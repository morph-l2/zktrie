package zktrie

import (
	"math/big"
)

// HashElemsWithDomain performs a recursive poseidon hash over the array of ElemBytes, each hash
// reduce 2 fieds into one, with a specified domain field which would be used in
// every recursiving call
func HashElemsWithDomain(domain, fst, snd *big.Int, elems ...*big.Int) (*Hash, error) {

	l := len(elems)
	baseH, err := hashScheme([]*big.Int{fst, snd}, domain)
	if err != nil {
		return nil, err
	}
	if l == 0 {
		return NewHashFromBigInt(baseH), nil
	} else if l == 1 {
		return HashElemsWithDomain(domain, baseH, elems[0])
	}

	tmp := make([]*big.Int, (l+1)/2)
	for i := range tmp {
		if (i+1)*2 > l {
			tmp[i] = elems[i*2]
		} else {
			h, err := hashScheme(elems[i*2:(i+1)*2], domain)
			if err != nil {
				return nil, err
			}
			tmp[i] = h
		}
	}

	return HashElemsWithDomain(domain, baseH, tmp[0], tmp[1:]...)
}

// HashElems call HashElemsWithDomain with a domain of HASH_DOMAIN_ELEMS_BASE(256)*<element counts>
func HashElems(fst, snd *big.Int, elems ...*big.Int) (*Hash, error) {

	return HashElemsWithDomain(big.NewInt(int64(len(elems)*HASH_DOMAIN_ELEMS_BASE)+HASH_DOMAIN_BYTE32),
		fst, snd, elems...)
}

// HandlingElemsAndByte32 hash an arry mixed with field and byte32 elements, turn each byte32 into
// field elements first then calculate the hash with HashElems
func HandlingElemsAndByte32(flagArray uint32, elems []Byte32) (*Hash, error) {

	ret := make([]*big.Int, len(elems))
	var err error

	for i, elem := range elems {
		if flagArray&(1<<i) != 0 {
			ret[i], err = elem.Hash()
			if err != nil {
				return nil, err
			}
		} else {
			ret[i] = new(big.Int).SetBytes(elem[:])
		}
	}

	if len(ret) < 2 {
		return NewHashFromBigInt(ret[0]), nil
	}

	return HashElems(ret[0], ret[1], ret[2:]...)

}

// SetBitBigEndian sets the bit n in the bitmap to 1, in Big Endian.
func SetBitBigEndian(bitmap []byte, n uint) {
	bitmap[uint(len(bitmap))-n/8-1] |= 1 << (n % 8)
}

// TestBit tests whether the bit n in bitmap is 1.
func TestBit(bitmap []byte, n uint) bool {
	return bitmap[n/8]&(1<<(n%8)) != 0
}

// TestBitBigEndian tests whether the bit n in bitmap is 1, in Big Endian.
func TestBitBigEndian(bitmap []byte, n uint) bool {
	return bitmap[uint(len(bitmap))-n/8-1]&(1<<(n%8)) != 0
}

var BigOne = big.NewInt(1)
var BigZero = big.NewInt(0)

func BigEndianBitsToBigInt(bits []bool) *big.Int {
	result := big.NewInt(0)
	for _, bit := range bits {
		result.Mul(result, big.NewInt(2))
		if bit {
			result.Add(result, BigOne)
		}
	}
	return result
}

func BigIntToBigEndianBits(num *big.Int) []bool {
	base2String := num.Text(2)
	var result []bool
	for _, b := range base2String {
		result = append(result, b == '1')
	}
	return result
}

// ToSecureKey turn the byte key into the integer represent of "secured" key
func ToSecureKey(key []byte) (*big.Int, error) {
	word := NewByte32FromBytesPaddingZero(key)
	return word.Hash()
}

// ToSecureKeyBytes turn the byte key into a 32-byte "secured" key, which represented a big-endian integer
func ToSecureKeyBytes(key []byte) (*Byte32, error) {
	k, err := ToSecureKey(key)
	if err != nil {
		return nil, err
	}

	return NewByte32FromBytes(k.Bytes()), nil
}

// ReverseByteOrder swaps the order of the bytes in the slice.
func ReverseByteOrder(b []byte) []byte {
	o := make([]byte, len(b))
	for i := range b {
		o[len(b)-1-i] = b[i]
	}
	return o
}

// Path to zk.Hash
// Hash value of the root node's path
var TrieRootPathKey = NewHashFromBytes([]byte{255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255})

// Prefix for valid path hash
var TriePrefix = []bool{true}

func PathToKey(arr []bool) *Hash {
	if len(arr) == 0 {
		return TrieRootPathKey
	}
	bigInt := BigEndianBitsToBigInt(append(TriePrefix, arr...))
	hash := NewHashFromBigInt(bigInt)
	return hash
}

func KeyToPath(hash *Hash) []bool {
	if hash == nil {
		return []bool{}
	}
	bigInt := hash.BigInt()
	result := BigIntToBigEndianBits(bigInt)
	return result[len(TriePrefix):]
}

func PathToString(arr []bool) string {
	str := ""
	for i := range arr {
		if arr[i] {
			str += "1 "
		} else {
			str += "0 "
		}
	}
	return str
}

func GetPathKey(prefix, path []byte) []byte {
	key := make([]byte, len(prefix)+len(path))
	copy(key[:len(prefix)], prefix[:])
	copy(key[len(prefix):], path[:])
	return key
}

func GetPathFromKey(prefix, key []byte) []byte {
	if len(key) < len(prefix) {
		return nil
	}
	path := make([]byte, len(key)-len(prefix))
	copy(path[:], key[len(prefix):])
	return path
}

func AppendPath(path []bool, val bool) []bool {
	newPath := make([]bool, len(path)+1)
	copy(newPath, path)
	newPath[len(newPath)-1] = val
	return newPath
}
