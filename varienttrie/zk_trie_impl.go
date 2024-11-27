package varienttrie

import (
	"bytes"
	"errors"
	"fmt"
	"io"
	"math/big"
	"sync"

	zkt "github.com/scroll-tech/zktrie/types"
)

const (
	// proofFlagsLen is the byte length of the flags in the proof header
	// (first 32 bytes).
	proofFlagsLen = 2
)

var (
	// ErrNodeKeyAlreadyExists is used when a node key already exists.
	ErrInvalidField = errors.New("Key not inside the Finite Field")
	// ErrNodeKeyAlreadyExists is used when a node key already exists.
	ErrNodeKeyAlreadyExists = errors.New("key already exists")
	// ErrKeyNotFound is used when a key is not found in the ZkTrieImpl.
	ErrKeyNotFound = errors.New("key not found in ZkTrieImpl")
	// ErrNodeBytesBadSize is used when the data of a node has an incorrect
	// size and can't be parsed.
	ErrNodeBytesBadSize = errors.New("node data has incorrect size in the DB")
	// ErrReachedMaxLevel is used when a traversal of the MT reaches the
	// maximum level.
	ErrReachedMaxLevel = errors.New("reached maximum level of the merkle tree")
	// ErrInvalidNodeFound is used when an invalid node is found and can't
	// be parsed.
	ErrInvalidNodeFound = errors.New("found an invalid node in the DB")
	// ErrInvalidProofBytes is used when a serialized proof is invalid.
	ErrInvalidProofBytes = errors.New("the serialized proof is invalid")
	// ErrEntryIndexAlreadyExists is used when the entry index already
	// exists in the tree.
	ErrEntryIndexAlreadyExists = errors.New("the entry index already exists in the tree")
	// ErrNotWritable is used when the ZkTrieImpl is not writable and a
	// write function is called
	ErrNotWritable = errors.New("merkle Tree not writable")

	dbKeyRootNode = []byte("currentroot")
)

// ZkTrieImpl is the struct with the main elements of the ZkTrieImpl
type ZkTrieImpl struct {
	lock      sync.RWMutex
	db        ZktrieDatabase
	rootKey   *zkt.Hash
	origin    *zkt.Hash
	writable  bool
	maxLevels int
	Debug     bool
	prefix    []byte

	dirtyIndex   *big.Int
	dirtyStorage map[zkt.Hash]*Node
	caching      map[zkt.Hash]zkt.Hash
}

func NewZkTrieImpl(storage ZktrieDatabase, maxLevels int) (*ZkTrieImpl, error) {
	return NewZkTrieImplWithRoot(storage, &zkt.HashZero, &zkt.HashZero, maxLevels, nil)
}

// NewZkTrieImplWithRoot loads a new ZkTrieImpl. If in the storage already exists one
// will open that one, if not, will create a new one.
func NewZkTrieImplWithRoot(storage ZktrieDatabase, root *zkt.Hash, origin *zkt.Hash, maxLevels int, prefix []byte) (*ZkTrieImpl, error) {
	mt := ZkTrieImpl{
		db:           storage,
		maxLevels:    maxLevels,
		writable:     true,
		dirtyIndex:   big.NewInt(0),
		dirtyStorage: make(map[zkt.Hash]*Node),
		caching:      make(map[zkt.Hash]zkt.Hash),
	}
	mt.rootKey = root
	if origin == nil {
		origin = &zkt.HashZero
	}
	mt.origin = origin
	if prefix == nil {
		mt.prefix = []byte{}
	} else {
		mt.prefix = prefix
	}
	if *root != zkt.HashZero {
		_, err := mt.GetNode(zkt.TrieRootPathKey)
		if err != nil {
			return nil, err
		}
	}
	return &mt, nil
}

// Root returns the MerkleRoot
func (mt *ZkTrieImpl) Root() (*zkt.Hash, error) {
	mt.lock.Lock()
	defer mt.lock.Unlock()
	// short circuit if there are no nodes to hash
	if mt.dirtyIndex.Cmp(big.NewInt(0)) == 0 {
		return mt.rootKey, nil
	}

	hashedDirtyStorage := make(map[zkt.Hash]*Node)
	rootKey, err := mt.calcCommitment(zkt.TrieRootPathKey, hashedDirtyStorage, new(sync.Mutex))
	if err != nil {
		return nil, err
	}

	newCaching := make(map[zkt.Hash]zkt.Hash)
	for k, n := range hashedDirtyStorage {
		if n.nodeHash != nil {
			newCaching[k] = *n.nodeHash
		}
	}

	mt.rootKey = rootKey
	mt.dirtyIndex = big.NewInt(0)
	mt.dirtyStorage = hashedDirtyStorage
	mt.caching = newCaching
	if mt.Debug {
		_, err := mt.getNode(zkt.TrieRootPathKey)
		if err != nil {
			panic(fmt.Errorf("load trie root failed hash %v", mt.rootKey.Bytes()))
		}
	}
	return mt.rootKey, nil
}

// MaxLevels returns the MT maximum level
func (mt *ZkTrieImpl) MaxLevels() int {
	return mt.maxLevels
}

// TryUpdate updates a nodeKey & value into the ZkTrieImpl. Where the `k` determines the
// path from the Root to the Leaf. This also return the updated leaf node
func (mt *ZkTrieImpl) TryUpdate(nodeKey *zkt.Hash, vFlag uint32, vPreimage []zkt.Byte32) error {
	// verify that the ZkTrieImpl is writable
	if !mt.writable {
		return ErrNotWritable
	}

	// verify that k are valid and fit inside the Finite Field.
	if !zkt.CheckBigIntInField(nodeKey.BigInt()) {
		return ErrInvalidField
	}

	newLeafNode := NewLeafNode(nodeKey, vFlag, vPreimage)
	path := getPath(mt.maxLevels, nodeKey[:])

	mt.lock.Lock()
	defer mt.lock.Unlock()

	newRootKey, _, err := mt.addLeaf(newLeafNode, zkt.TrieRootPathKey, 0, path)

	// sanity check
	if err == ErrEntryIndexAlreadyExists {
		panic("Encounter unexpected errortype: ErrEntryIndexAlreadyExists")
	} else if err != nil {
		return err
	}
	if newRootKey != nil {
		mt.rootKey = newRootKey
	}

	return nil
}

// pushLeaf recursively pushes an existing oldLeaf down until its path diverges
// from newLeaf, at which point both leafs are stored, all while updating the
// path. pushLeaf returns the node hash of the parent of the oldLeaf and newLeaf
func (mt *ZkTrieImpl) pushLeaf(newLeaf *Node, oldLeaf *Node, lvl int,
	pathNewLeaf []bool, pathOldLeaf []bool) (*zkt.Hash, error) {
	if lvl > mt.maxLevels-2 {
		return nil, ErrReachedMaxLevel
	}
	var newParentNode *Node
	if pathNewLeaf[lvl] == pathOldLeaf[lvl] { // We need to go deeper!
		// notice the node corresponding to return hash is always branch
		nextNodeHash, err := mt.pushLeaf(newLeaf, oldLeaf, lvl+1, pathNewLeaf, pathOldLeaf)
		if err != nil {
			return nil, err
		}

		siblingNodeRight := false
		if pathNewLeaf[lvl] { // go right
			siblingNodeRight = false
			newParentNode = NewParentNode(NodeTypeBranch_1, &zkt.HashZero, nextNodeHash)
		} else { // go left
			siblingNodeRight = true
			newParentNode = NewParentNode(NodeTypeBranch_2, nextNodeHash, &zkt.HashZero)
		}

		// Update path's nodes
		parentNodePathKey := zkt.PathToKey(pathNewLeaf[:lvl])
		mt.dirtyStorage[*parentNodePathKey] = newParentNode

		siblingNodePathKey := zkt.PathToKey(zkt.AppendPath(pathNewLeaf[:lvl], siblingNodeRight))
		mt.dirtyStorage[*siblingNodePathKey] = NewEmptyNode()

		// Increase dirty index, mark for changes
		mt.newDirtyNodeKey()

		return parentNodePathKey, nil
	}
	oldLeafHash, err := oldLeaf.NodeHash()
	if err != nil {
		return nil, err
	}
	newLeafHash, err := newLeaf.NodeHash()
	if err != nil {
		return nil, err
	}

	newLeafPathRight := false
	if pathNewLeaf[lvl] {
		newParentNode = NewParentNode(NodeTypeBranch_0, oldLeafHash, newLeafHash)
		newLeafPathRight = true
	} else {
		newParentNode = NewParentNode(NodeTypeBranch_0, newLeafHash, oldLeafHash)
		newLeafPathRight = false
	}

	// Update path's nodes
	oldPathKey := zkt.PathToKey(zkt.AppendPath(pathNewLeaf[:lvl], !newLeafPathRight))
	newPathKey := zkt.PathToKey(zkt.AppendPath(pathNewLeaf[:lvl], newLeafPathRight))
	parentPathKey := zkt.PathToKey(pathNewLeaf[:lvl])

	// We can add newLeaf now.  We don't need to add oldLeaf because it's
	// already in the tree.
	mt.dirtyStorage[*oldPathKey] = oldLeaf
	mt.dirtyStorage[*newPathKey] = newLeaf
	mt.dirtyStorage[*parentPathKey] = newParentNode

	// Increase dirty index, mark for changes
	mt.newDirtyNodeKey()
	return parentPathKey, nil
}

// Commit calculates the root for the entire trie and persist all the dirty nodes
func (mt *ZkTrieImpl) Commit() error {
	// force root hash calculation if needed
	if _, err := mt.Root(); err != nil {
		return err
	}

	mt.lock.Lock()
	defer mt.lock.Unlock()

	for key, node := range mt.dirtyStorage {
		pathKey := zkt.GetPathKey(mt.prefix, key[:])
		if err := mt.db.Put(pathKey[:], node.CanonicalValue()); err != nil {
			return err
		}
	}

	mt.dirtyStorage = make(map[zkt.Hash]*Node)
	mt.caching = make(map[zkt.Hash]zkt.Hash)
	return mt.db.Put(dbKeyRootNode, append([]byte{byte(DBEntryTypeRoot)}, mt.rootKey[:]...))
}

// addLeaf recursively adds a newLeaf in the MT while updating the path, and returns the key
// of the new added leaf.
func (mt *ZkTrieImpl) addLeaf(newLeaf *Node, currNodeKey *zkt.Hash,
	lvl int, path []bool) (*zkt.Hash, bool, error) {
	var err error
	if lvl > mt.maxLevels-1 {
		return nil, false, ErrReachedMaxLevel
	}
	n, err := mt.getNode(currNodeKey)
	if err != nil {
		return nil, false, err
	}
	switch n.Type {
	case NodeTypeEmpty_New:
		newLeafHash, err := newLeaf.NodeHash()
		if err != nil {
			return nil, false, err
		}

		// Update path's nodes
		pathKey := zkt.PathToKey(path[:lvl])
		mt.dirtyStorage[*pathKey] = newLeaf
		mt.caching[*pathKey] = *newLeafHash

		return newLeafHash, true, nil
	case NodeTypeLeaf_New:
		newLeafHash, err := newLeaf.NodeHash()
		if err != nil {
			return nil, false, err
		}

		if bytes.Equal(currNodeKey[:], newLeafHash[:]) {
			// do nothing, duplicate entry
			return nil, true, nil
		} else if bytes.Equal(newLeaf.NodeKey.Bytes(), n.NodeKey.Bytes()) {
			// update the existing leaf
			// Update path's nodes
			pathKey := zkt.PathToKey(path[:lvl])
			mt.dirtyStorage[*pathKey] = newLeaf
			mt.caching[*pathKey] = *newLeafHash

			return newLeafHash, true, nil
		}
		newSubTrieRootPathKey, err := mt.pushLeaf(newLeaf, n, lvl, path, getPath(mt.maxLevels, n.NodeKey[:]))
		return newSubTrieRootPathKey, false, err
	case NodeTypeBranch_0, NodeTypeBranch_1, NodeTypeBranch_2, NodeTypeBranch_3:
		// We need to go deeper, continue traversing the tree, left or
		// right depending on path
		branchRight := path[lvl]
		newChildSubTrieRootPathKey, isTerminal, err := mt.addLeaf(newLeaf, zkt.PathToKey(zkt.AppendPath(path[:lvl], branchRight)), lvl+1, path)
		if err != nil {
			return nil, false, err
		}

		// do nothing, if child subtrie was not modified
		if newChildSubTrieRootPathKey == nil {
			return nil, false, nil
		}

		newNodetype := n.Type
		if !isTerminal {
			newNodetype = newNodetype.DeduceUpgradeType(branchRight)
		}

		var newNode *Node
		if branchRight {
			siblingNodePathKey := zkt.PathToKey(zkt.AppendPath(path[:lvl], false))
			mt.caching[*siblingNodePathKey] = *n.ChildL

			newNode = NewParentNode(newNodetype, n.ChildL, newChildSubTrieRootPathKey)
		} else {
			siblingNodePathKey := zkt.PathToKey(zkt.AppendPath(path[:lvl], true))
			mt.caching[*siblingNodePathKey] = *n.ChildR

			newNode = NewParentNode(newNodetype, newChildSubTrieRootPathKey, n.ChildR)
		}

		// if current node is already dirty, modify in-place
		// else create a new dirty sub-trie
		newNodePathKey := zkt.PathToKey(path[:lvl])
		mt.dirtyStorage[*newNodePathKey] = newNode

		// Increase dirty index, mark for changes
		mt.newDirtyNodeKey()

		return newNodePathKey, false, err
	case NodeTypeEmpty, NodeTypeLeaf, NodeTypeParent:
		panic("encounter unsupported deprecated node type")
	default:
		return nil, false, ErrInvalidNodeFound
	}
}

// newDirtyNodeKey increments the dirtyIndex and creates a new dirty node key
func (mt *ZkTrieImpl) newDirtyNodeKey() *zkt.Hash {
	mt.dirtyIndex.Add(mt.dirtyIndex, zkt.BigOne)
	return zkt.NewHashFromBigInt(mt.dirtyIndex)
}

// isDirtyNode returns if the node with the given key is dirty or not
func (mt *ZkTrieImpl) isDirtyNode(pathKey *zkt.Hash) bool {
	_, found := mt.dirtyStorage[*pathKey]
	return found
}

// calcCommitment calculates the commitment for the given sub trie
func (mt *ZkTrieImpl) calcCommitment(nodePathKey *zkt.Hash, hashedDirtyNodes map[zkt.Hash]*Node, commitLock *sync.Mutex) (*zkt.Hash, error) {
	if !mt.isDirtyNode(nodePathKey) {
		if h, found := mt.caching[*nodePathKey]; found {
			return &h, nil
		}
	}
	root, err := mt.getNode(nodePathKey)
	if err != nil {
		return nil, err
	}

	rootPath := []bool{}
	if !bytes.Equal(nodePathKey[:], zkt.TrieRootPathKey[:]) {
		rootPath = zkt.KeyToPath(nodePathKey)
	}

	switch root.Type {
	case NodeTypeEmpty, NodeTypeEmpty_New:
		// Empty node must add to hashedDirtyNodes
		break
	case NodeTypeLeaf_New:
		// leaves are already hashed, we just need to persist it
		break
	case NodeTypeBranch_0, NodeTypeBranch_1, NodeTypeBranch_2, NodeTypeBranch_3:
		leftDone := make(chan struct{})
		var leftErr error
		go func() {
			leftPathKey := zkt.PathToKey(zkt.AppendPath(rootPath, false))
			root.ChildL, leftErr = mt.calcCommitment(leftPathKey, hashedDirtyNodes, commitLock)
			close(leftDone)
		}()

		rightPathKey := zkt.PathToKey(zkt.AppendPath(rootPath, true))
		root.ChildR, err = mt.calcCommitment(rightPathKey, hashedDirtyNodes, commitLock)
		if err != nil {
			return nil, err
		}
		<-leftDone
		if leftErr != nil {
			return nil, leftErr
		}
	default:
		return nil, errors.New(fmt.Sprint("unexpected node type", root.Type))
	}

	rootHash, err := root.NodeHash()
	if err != nil {
		return nil, err
	}

	commitLock.Lock()
	defer commitLock.Unlock()
	if mt.isDirtyNode(nodePathKey) {
		hashedDirtyNodes[*nodePathKey] = root
	}
	return rootHash, nil
}

func (mt *ZkTrieImpl) tryGet(nodeKey *zkt.Hash) (*Node, []*zkt.Hash, error) {
	path := getPath(mt.maxLevels, nodeKey[:])

	var siblings []*zkt.Hash
	//sanity check
	lastNodeType := NodeTypeBranch_3
	for i := 0; i < mt.maxLevels; i++ {
		n, err := mt.getNode(zkt.PathToKey(path[:i]))
		if err != nil {
			return nil, nil, err
		}
		//sanity check
		if i > 0 && n.IsTerminal() {
			if lastNodeType == NodeTypeBranch_3 {
				panic("parent node has invalid type: children are not terminal")
			} else if path[i-1] && lastNodeType == NodeTypeBranch_1 {
				panic("parent node has invalid type: right child is not terminal")
			} else if !path[i-1] && lastNodeType == NodeTypeBranch_2 {
				panic("parent node has invalid type: left child is not terminal")
			}
		}

		lastNodeType = n.Type
		switch n.Type {
		case NodeTypeEmpty_New:
			return NewEmptyNode(), siblings, ErrKeyNotFound
		case NodeTypeLeaf_New:
			if bytes.Equal(nodeKey[:], n.NodeKey[:]) {
				return n, siblings, nil
			}
			return n, siblings, ErrKeyNotFound
		case NodeTypeBranch_0, NodeTypeBranch_1, NodeTypeBranch_2, NodeTypeBranch_3:
			if path[i] {
				siblings = append(siblings, n.ChildL)
			} else {
				siblings = append(siblings, n.ChildR)
			}
		case NodeTypeEmpty, NodeTypeLeaf, NodeTypeParent:
			panic("encounter deprecated node types")
		default:
			return nil, nil, ErrInvalidNodeFound
		}
	}

	return nil, siblings, ErrReachedMaxLevel
}

// TryGet returns the value for key stored in the trie.
// The value bytes must not be modified by the caller.
// If a node was not found in the database, a MissingNodeError is returned.
func (mt *ZkTrieImpl) TryGet(nodeKey *zkt.Hash) ([]byte, error) {
	mt.lock.RLock()
	defer mt.lock.RUnlock()

	node, _, err := mt.tryGet(nodeKey)
	if err == ErrKeyNotFound {
		// according to https://github.com/ethereum/go-ethereum/blob/37f9d25ba027356457953eab5f181c98b46e9988/trie/trie.go#L135
		return nil, nil
	} else if err != nil {
		return nil, err
	}
	return node.Data(), nil
}

// Delete removes the specified Key from the ZkTrieImpl and updates the path
// from the deleted key to the Root with the new values.  This method removes
// the key from the ZkTrieImpl, but does not remove the old nodes from the
// key-value database; this means that if the tree is accessed by an old Root
// where the key was not deleted yet, the key will still exist. If is desired
// to remove the key-values from the database that are not under the current
// Root, an option could be to dump all the leafs (using mt.DumpLeafs) and
// import them in a new ZkTrieImpl in a new database (using
// mt.ImportDumpedLeafs), but this will lose all the Root history of the
// ZkTrieImpl
func (mt *ZkTrieImpl) TryDelete(nodeKey *zkt.Hash) error {
	// verify that the ZkTrieImpl is writable
	if !mt.writable {
		return ErrNotWritable
	}

	// verify that k is valid and fit inside the Finite Field.
	if !zkt.CheckBigIntInField(nodeKey.BigInt()) {
		return ErrInvalidField
	}

	mt.lock.Lock()
	defer mt.lock.Unlock()

	rootPathKey := &zkt.HashZero
	if !mt.rootKey.IsHashZero() {
		rootPathKey = zkt.TrieRootPathKey
	}
	newRootKey, _, _, err := mt.tryDelete(rootPathKey, nodeKey, getPath(mt.maxLevels, nodeKey[:]))
	if err != nil {
		return err
	}
	mt.rootKey = newRootKey
	return nil
}

func (mt *ZkTrieImpl) tryDelete(nodePathKey *zkt.Hash, nodeKey *zkt.Hash, path []bool) (*zkt.Hash, *zkt.Hash, bool, error) {
	root, err := mt.getNode(nodePathKey)
	if err != nil {
		return nil, nil, false, err
	}

	rootPath := []bool{}
	if !bytes.Equal(nodePathKey[:], zkt.TrieRootPathKey[:]) {
		rootPath = zkt.KeyToPath(nodePathKey)
	}

	switch root.Type {
	case NodeTypeEmpty_New:
		return nil, nil, false, ErrKeyNotFound
	case NodeTypeLeaf_New:
		if bytes.Equal(nodeKey[:], root.NodeKey[:]) {
			mt.dirtyStorage[*nodePathKey] = NewEmptyNode()

			return &zkt.HashZero, nodePathKey, true, nil
		}
		return nil, nil, false, ErrKeyNotFound
	case NodeTypeBranch_0, NodeTypeBranch_1, NodeTypeBranch_2, NodeTypeBranch_3:
		branchRight := path[0]
		siblingKey := root.ChildR
		if branchRight {
			siblingKey = root.ChildL
		}

		newChildKey, newChildPathKey, newChildIsTerminal, err := mt.tryDelete(zkt.PathToKey(zkt.AppendPath(rootPath, branchRight)), nodeKey, path[1:])
		if err != nil {
			return nil, nil, false, err
		}

		newChildPath := zkt.KeyToPath(newChildPathKey)
		newParentNodePath := []bool{}
		if len(newChildPath) > 0 {
			newParentNodePath = newChildPath[:len(newChildPath)-1]
		}

		newParentNodePathKey := zkt.PathToKey(newParentNodePath)
		leftNodePathKey := zkt.PathToKey(zkt.AppendPath(newParentNodePath, false))
		rightNodePathKey := zkt.PathToKey(zkt.AppendPath(newParentNodePath, true))

		// Prune
		siblingIsTerminal := root.Type == NodeTypeBranch_0 ||
			(branchRight && root.Type == NodeTypeBranch_1) ||
			(!branchRight && root.Type == NodeTypeBranch_2)

		leftChild, rightChild := newChildKey, siblingKey
		leftIsTerminal, rightIsTerminal := newChildIsTerminal, siblingIsTerminal
		if branchRight {
			leftChild, rightChild = siblingKey, newChildKey
			leftIsTerminal, rightIsTerminal = siblingIsTerminal, newChildIsTerminal
		}

		var newNodeType NodeType
		if leftIsTerminal && rightIsTerminal {
			leftIsEmpty := bytes.Equal(zkt.HashZero[:], (*leftChild)[:])
			rightIsEmpty := bytes.Equal(zkt.HashZero[:], (*rightChild)[:])

			// if both children are terminal and one of them is empty, prune the root node
			// and send return the non-empty child
			if leftIsEmpty || rightIsEmpty {
				if leftIsEmpty {
					rightNode, err := mt.getNode(rightNodePathKey)
					if err != nil {
						return nil, nil, false, err
					}
					mt.dirtyStorage[*newParentNodePathKey] = rightNode

					// Delete path
					mt.dirtyStorage[*leftNodePathKey] = NewEmptyNode()
					mt.dirtyStorage[*rightNodePathKey] = NewEmptyNode()

					mt.caching[*newParentNodePathKey] = *rightChild

					return rightChild, newParentNodePathKey, true, nil
				}

				leftNode, err := mt.getNode(leftNodePathKey)
				if err != nil {
					return nil, nil, false, err
				}
				mt.dirtyStorage[*newParentNodePathKey] = leftNode
				mt.caching[*newParentNodePathKey] = *leftChild

				// Delete path
				mt.dirtyStorage[*leftNodePathKey] = NewEmptyNode()
				mt.dirtyStorage[*rightNodePathKey] = NewEmptyNode()

				return leftChild, newParentNodePathKey, true, nil
			} else {
				newNodeType = NodeTypeBranch_0
			}
		} else if leftIsTerminal {
			newNodeType = NodeTypeBranch_1
		} else if rightIsTerminal {
			newNodeType = NodeTypeBranch_2
		} else {
			newNodeType = NodeTypeBranch_3
		}

		// Update unchanged path node
		if branchRight {
			mt.caching[*leftNodePathKey] = *siblingKey
		} else {
			mt.caching[*rightNodePathKey] = *siblingKey
		}

		// // Update child path
		// leftNode, err := mt.getNode(leftNodePathKey)
		// if err != nil {
		// 	return nil, nil, false, err
		// }
		// mt.dirtyStorage[*leftNodePathKey] = leftNode

		// rightNode, err := mt.getNode(rightNodePathKey)
		// if err != nil {
		// 	return nil, nil, false, err
		// }
		// mt.dirtyStorage[*rightNodePathKey] = rightNode

		// The old parent node need prune
		// The left or right node's path maybe not change.
		newParentNode := NewParentNode(newNodeType, leftChild, rightChild)
		mt.dirtyStorage[*newParentNodePathKey] = newParentNode

		// Increase dirty index, mark for changes
		mt.newDirtyNodeKey()

		return newParentNodePathKey, newParentNodePathKey, false, nil
	default:
		panic("encounter unsupported deprecated node type")
	}
}

// GetLeafNode is more underlying method than TryGet, which obtain an leaf node
// or nil if not exist
func (mt *ZkTrieImpl) GetLeafNode(nodeKey *zkt.Hash) (*Node, error) {
	mt.lock.RLock()
	defer mt.lock.RUnlock()

	n, _, err := mt.tryGet(nodeKey)
	return n, err
}

// GetNode gets a node by node hash from the MT.  Empty nodes are not stored in the
// tree; they are all the same and assumed to always exist.
// <del>for non exist key, return (NewEmptyNode(), nil)</del>
func (mt *ZkTrieImpl) GetNode(nodeHash *zkt.Hash) (*Node, error) {
	mt.lock.RLock()
	defer mt.lock.RUnlock()

	return mt.getNode(nodeHash)
}

func (mt *ZkTrieImpl) getNode(pathKey *zkt.Hash) (*Node, error) {
	if bytes.Equal(pathKey[:], zkt.HashZero[:]) {
		return NewEmptyNode(), nil
	}
	if mt.rootKey.IsHashZero() && bytes.Equal(pathKey[:], zkt.TrieRootPathKey[:]) {
		return NewEmptyNode(), nil
	}

	if node, found := mt.dirtyStorage[*pathKey]; found {
		return node, nil
	}

	key := zkt.GetPathKey(mt.prefix, pathKey[:])
	nBytes, err := mt.db.GetFrom(mt.origin[:], key[:])
	if err == ErrKeyNotFound {
		return nil, ErrKeyNotFound
	} else if err != nil {
		return nil, err
	}
	return NewNodeFromBytes(nBytes)
}

// getPath returns the binary path, from the root to the leaf.
func getPath(numLevels int, k []byte) []bool {
	path := make([]bool, numLevels)
	for n := 0; n < numLevels; n++ {
		path[n] = zkt.TestBit(k[:], uint(n))
	}
	return path
}

// NodeAux contains the auxiliary node used in a non-existence proof.
type NodeAux struct {
	Key   *zkt.Hash // Key is the node key
	Value *zkt.Hash // Value is the value hash in the node
}

// Proof defines the required elements for a MT proof of existence or
// non-existence.
type Proof struct {
	// existence indicates wether this is a proof of existence or
	// non-existence.
	Existence bool
	// depth indicates how deep in the tree the proof goes.
	depth uint
	// notempties is a bitmap of non-empty Siblings found in Siblings.
	notempties [zkt.HashByteLen - proofFlagsLen]byte
	// Siblings is a list of non-empty sibling node hashes.
	Siblings []*zkt.Hash
	// NodeInfos is a list of nod types along mpt path
	NodeInfos []NodeType
	// NodeKey record the key of node and path
	NodeKey *zkt.Hash
	// NodeAux contains the auxiliary information of the lowest common ancestor
	// node in a non-existence proof.
	NodeAux *NodeAux
}

// BuildZkTrieProof prove uniformed way to turn some data collections into Proof struct
func BuildZkTrieProof(rootHash *zkt.Hash, k *big.Int, lvl int, getNode func(key *zkt.Hash) (*Node, error)) (*Proof,
	*Node, error) {

	p := &Proof{}
	var siblingHash *zkt.Hash

	p.NodeKey = zkt.NewHashFromBigInt(k)
	kHash := p.NodeKey
	path := getPath(lvl, kHash[:])

	for p.depth = 0; p.depth < uint(lvl); p.depth++ {
		n, err := getNode(zkt.PathToKey(path[:p.depth]))
		if err != nil {
			return nil, nil, err
		}
		p.NodeInfos = append(p.NodeInfos, n.Type)
		switch n.Type {
		case NodeTypeEmpty_New:
			return p, n, nil
		case NodeTypeLeaf_New:
			if bytes.Equal(kHash[:], n.NodeKey[:]) {
				p.Existence = true
				return p, n, nil
			}
			vHash, err := n.ValueHash()
			// We found a leaf whose entry didn't match hIndex
			p.NodeAux = &NodeAux{Key: n.NodeKey, Value: vHash}
			return p, n, err
		case NodeTypeBranch_0, NodeTypeBranch_1, NodeTypeBranch_2, NodeTypeBranch_3:
			if path[p.depth] {
				siblingHash = n.ChildL
			} else {
				siblingHash = n.ChildR
			}
		case NodeTypeEmpty, NodeTypeLeaf, NodeTypeParent:
			panic("encounter deprecated node types")
		default:
			return nil, nil, ErrInvalidNodeFound
		}
		if !bytes.Equal(siblingHash[:], zkt.HashZero[:]) {
			zkt.SetBitBigEndian(p.notempties[:], p.depth)
			p.Siblings = append(p.Siblings, siblingHash)
		}
	}
	return nil, nil, ErrKeyNotFound

}

// VerifyProof verifies the Merkle Proof for the entry and root.
// nodeHash can be nil when try to verify a nonexistent proof
func VerifyProofZkTrie(rootHash *zkt.Hash, proof *Proof, node *Node) bool {
	var nodeHash *zkt.Hash
	var err error
	if node == nil {
		if proof.NodeAux != nil {
			nodeHash, err = LeafHash(proof.NodeAux.Key, proof.NodeAux.Value)
		} else {
			nodeHash = &zkt.HashZero
		}
	} else {
		nodeHash, err = node.NodeHash()
	}

	if err != nil {
		return false
	}

	rootFromProof, err := proof.rootFromProof(nodeHash, proof.NodeKey)
	if err != nil {
		return false
	}
	return bytes.Equal(rootHash[:], rootFromProof[:])
}

// Verify the proof and calculate the root, nodeHash can be nil when try to verify
// a nonexistent proof
func (proof *Proof) Verify(nodeHash *zkt.Hash) (*zkt.Hash, error) {
	if proof.Existence {
		if nodeHash == nil {
			return nil, ErrKeyNotFound
		}
		return proof.rootFromProof(nodeHash, proof.NodeKey)
	} else {
		if proof.NodeAux == nil {
			return proof.rootFromProof(&zkt.HashZero, proof.NodeKey)
		} else {
			if bytes.Equal(proof.NodeKey[:], proof.NodeAux.Key[:]) {
				return nil, fmt.Errorf("non-existence proof being checked against hIndex equal to nodeAux")
			}
			midHash, err := LeafHash(proof.NodeAux.Key, proof.NodeAux.Value)
			if err != nil {
				return nil, err
			}
			return proof.rootFromProof(midHash, proof.NodeKey)
		}
	}

}

func (proof *Proof) rootFromProof(nodeHash, nodeKey *zkt.Hash) (*zkt.Hash, error) {
	var err error

	sibIdx := len(proof.Siblings) - 1
	path := getPath(int(proof.depth), nodeKey[:])
	for lvl := int(proof.depth) - 1; lvl >= 0; lvl-- {
		var siblingHash *zkt.Hash
		if zkt.TestBitBigEndian(proof.notempties[:], uint(lvl)) {
			siblingHash = proof.Siblings[sibIdx]
			sibIdx--
		} else {
			siblingHash = &zkt.HashZero
		}
		curType := proof.NodeInfos[lvl]
		if path[lvl] {
			nodeHash, err = NewParentNode(curType, siblingHash, nodeHash).NodeHash()
			if err != nil {
				return nil, err
			}
		} else {
			nodeHash, err = NewParentNode(curType, nodeHash, siblingHash).NodeHash()
			if err != nil {
				return nil, err
			}
		}
	}
	return nodeHash, nil
}

// walk is a helper recursive function to iterate over all tree branches
func (mt *ZkTrieImpl) walk(nodeHash *zkt.Hash, f func(*Node)) error {
	n, err := mt.getNode(nodeHash)
	if err != nil {
		return err
	}

	rootPath := []bool{}
	if !bytes.Equal(nodeHash[:], zkt.TrieRootPathKey[:]) {
		rootPath = zkt.KeyToPath(nodeHash)
	}

	if n.IsTerminal() {
		f(n)
	} else {
		f(n)
		leftPath := zkt.PathToKey(zkt.AppendPath(rootPath, false))
		if err := mt.walk(leftPath, f); err != nil {
			return err
		}
		rightPath := zkt.PathToKey(zkt.AppendPath(rootPath, true))
		if err := mt.walk(rightPath, f); err != nil {
			return err
		}
	}
	return nil
}

// Walk iterates over all the branches of a ZkTrieImpl with the given rootHash
// if rootHash is nil, it will get the current RootHash of the current state of
// the ZkTrieImpl.  For each node, it calls the f function given in the
// parameters.  See some examples of the Walk function usage in the
// ZkTrieImpl.go and merkletree_test.go
func (mt *ZkTrieImpl) Walk(rootHash *zkt.Hash, f func(*Node)) error {
	var err error
	rootPathKey := &zkt.HashZero
	if !mt.rootKey.IsHashZero() {
		rootPathKey = zkt.TrieRootPathKey
	}

	mt.lock.RLock()
	defer mt.lock.RUnlock()

	err = mt.walk(rootPathKey, f)
	return err
}

// GraphViz uses Walk function to generate a string GraphViz representation of
// the tree and writes it to w
func (mt *ZkTrieImpl) GraphViz(w io.Writer, rootHash *zkt.Hash) error {
	if rootHash == nil {
		var err error
		rootHash, err = mt.Root()
		if err != nil {
			return err
		}
	}

	mt.lock.RLock()
	defer mt.lock.RUnlock()

	fmt.Fprintf(w,
		"--------\nGraphViz of the ZkTrieImpl with RootHash "+rootHash.BigInt().String()+"\n")

	fmt.Fprintf(w, `digraph hierarchy {
node [fontname=Monospace,fontsize=10,shape=box]
`)

	rootPathKey := &zkt.HashZero
	if !mt.rootKey.IsHashZero() {
		rootPathKey = zkt.TrieRootPathKey
	}

	cnt := 0
	var errIn error
	err := mt.walk(rootPathKey, func(n *Node) {
		hash, err := n.NodeHash()
		if err != nil {
			errIn = err
		}
		switch n.Type {
		case NodeTypeEmpty_New:
		case NodeTypeLeaf_New:
			fmt.Fprintf(w, "\"%v\" [style=filled];\n", hash.String())
		case NodeTypeBranch_0, NodeTypeBranch_1, NodeTypeBranch_2, NodeTypeBranch_3:
			lr := [2]string{n.ChildL.String(), n.ChildR.String()}
			emptyNodes := ""
			for i := range lr {
				if lr[i] == "0" {
					lr[i] = fmt.Sprintf("empty%v", cnt)
					emptyNodes += fmt.Sprintf("\"%v\" [style=dashed,label=0];\n", lr[i])
					cnt++
				}
			}
			fmt.Fprintf(w, "\"%v\" -> {\"%v\" \"%v\"}\n", hash.String(), lr[0], lr[1])
			fmt.Fprint(w, emptyNodes)
		case NodeTypeEmpty, NodeTypeLeaf, NodeTypeParent:
			panic("encounter unsupported deprecated node type")
		default:
		}
	})
	fmt.Fprintf(w, "}\n")

	fmt.Fprintf(w,
		"End of GraphViz of the ZkTrieImpl with RootHash "+rootHash.BigInt().String()+"\n--------\n")

	if errIn != nil {
		return errIn
	}
	return err
}

// Copy creates a new independent zkTrie from the given trie
func (mt *ZkTrieImpl) Copy() *ZkTrieImpl {
	mt.lock.RLock()
	defer mt.lock.RUnlock()

	// Deep copy in-memory dirty nodes
	newDirtyStorage := make(map[zkt.Hash]*Node, len(mt.dirtyStorage))
	for key, dirtyNode := range mt.dirtyStorage {
		newDirtyStorage[key] = dirtyNode.Copy()
	}

	newCaching := make(map[zkt.Hash]zkt.Hash, len(mt.caching))
	for key, h := range mt.caching {
		newCaching[key] = *zkt.NewHashFromBigInt(h.BigInt())
	}

	newRootKey := *mt.rootKey
	return &ZkTrieImpl{
		db:           mt.db,
		maxLevels:    mt.maxLevels,
		writable:     mt.writable,
		dirtyIndex:   new(big.Int).Set(mt.dirtyIndex),
		dirtyStorage: newDirtyStorage,
		rootKey:      &newRootKey,
		Debug:        mt.Debug,
		prefix:       mt.prefix,
		caching:      newCaching,
	}
}
