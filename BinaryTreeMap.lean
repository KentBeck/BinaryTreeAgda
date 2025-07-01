-- Binary Tree Map verification in Lean

-- Error type corresponding to Rust MapError
inductive MapError where
  | KeyNotFound : MapError

-- Binary tree node structure
inductive BTreeNode (K V : Type) where
  | node : K → V → Option (BTreeNode K V) → Option (BTreeNode K V) → BTreeNode K V

-- Binary tree map structure
structure BinaryTreeMap (K V : Type) where
  root : Option (BTreeNode K V)

-- Constructor for empty map
def BinaryTreeMap.empty {K V : Type} : BinaryTreeMap K V :=
  { root := none }

-- Get operation that mirrors the Rust implementation
def BTreeNode.get [LT K] [DecidableRel (· < · : K → K → Prop)] (node : BTreeNode K V) (key : K) : Option V :=
  match node with
  | BTreeNode.node k v left right =>
    if key < k then
      match left with
      | none => none
      | some leftNode => leftNode.get key
    else if k < key then
      match right with
      | none => none  
      | some rightNode => rightNode.get key
    else
      some v

-- Insert operation for nodes
def BTreeNode.insert [LT K] [DecidableRel (· < · : K → K → Prop)] (node : BTreeNode K V) (key : K) (value : V) : BTreeNode K V :=
  match node with
  | BTreeNode.node k v left right =>
    if key < k then
      let newLeft := match left with
        | none => some (BTreeNode.node key value none none)
        | some leftNode => some (leftNode.insert key value)
      BTreeNode.node k v newLeft right
    else if k < key then
      let newRight := match right with
        | none => some (BTreeNode.node key value none none)
        | some rightNode => some (rightNode.insert key value)
      BTreeNode.node k v left newRight
    else
      BTreeNode.node key value left right -- Update existing key

-- Insert operation for the map
def BinaryTreeMap.insert [LT K] [DecidableRel (· < · : K → K → Prop)] (map : BinaryTreeMap K V) (key : K) (value : V) : BinaryTreeMap K V :=
  match map.root with
  | none => { root := some (BTreeNode.node key value none none) }
  | some node => { root := some (node.insert key value) }

-- Find minimum node in a tree (for deletion)
def BTreeNode.findMin [LT K] [DecidableRel (· < · : K → K → Prop)] (node : BTreeNode K V) : K × V :=
  match node with
  | BTreeNode.node k v (some left) _ => left.findMin
  | BTreeNode.node k v none _ => (k, v)

-- Remove minimum node and return the remaining tree
def BTreeNode.removeMin [LT K] [DecidableRel (· < · : K → K → Prop)] (node : BTreeNode K V) : Option (BTreeNode K V) :=
  match node with
  | BTreeNode.node k v (some left) right => 
    match left.removeMin with
    | none => right
    | some newLeft => some (BTreeNode.node k v (some newLeft) right)
  | BTreeNode.node k v none right => right

-- Delete operation for nodes
def BTreeNode.delete [LT K] [DecidableRel (· < · : K → K → Prop)] (node : BTreeNode K V) (key : K) : Option (BTreeNode K V) × Option V :=
  match node with
  | BTreeNode.node k v left right =>
    if key < k then
      match left with
      | none => (some node, none)
      | some leftNode => 
        let (newLeft, deletedValue) := leftNode.delete key
        (some (BTreeNode.node k v newLeft right), deletedValue)
    else if k < key then
      match right with
      | none => (some node, none)
      | some rightNode =>
        let (newRight, deletedValue) := rightNode.delete key
        (some (BTreeNode.node k v left newRight), deletedValue)
    else
      -- Found the key to delete
      match left, right with
      | none, none => (none, some v)
      | some leftNode, none => (some leftNode, some v)
      | none, some rightNode => (some rightNode, some v)
      | some leftNode, some rightNode =>
        let (successorKey, successorValue) := rightNode.findMin
        let newRight := rightNode.removeMin
        (some (BTreeNode.node successorKey successorValue (some leftNode) newRight), some v)

-- Delete operation for the map
def BinaryTreeMap.delete [LT K] [DecidableRel (· < · : K → K → Prop)] (map : BinaryTreeMap K V) (key : K) : BinaryTreeMap K V × Option V :=
  match map.root with
  | none => (map, none)
  | some node => 
    let (newRoot, deletedValue) := node.delete key
    ({ root := newRoot }, deletedValue)

-- Get operation for the map
def BinaryTreeMap.get [LT K] [DecidableRel (· < · : K → K → Prop)] (map : BinaryTreeMap K V) (key : K) : Option V :=
  match map.root with
  | none => none
  | some node => node.get key

-- Convert Option to Result type for better correspondence with Rust
def optionToResult {V : Type} (opt : Option V) : V ⊕ MapError :=
  match opt with
  | none => Sum.inr MapError.KeyNotFound
  | some v => Sum.inl v

def BinaryTreeMap.getResult [LT K] [DecidableRel (· < · : K → K → Prop)] (map : BinaryTreeMap K V) (key : K) : V ⊕ MapError :=
  optionToResult (map.get key)

-- Main correctness theorem: getting from empty map returns KeyNotFound
theorem empty_map_get_returns_error {K V : Type} [LT K] [DecidableRel (· < · : K → K → Prop)] 
    (key : K) : BinaryTreeMap.getResult (BinaryTreeMap.empty : BinaryTreeMap K V) key = Sum.inr MapError.KeyNotFound := by
  -- Unfold definitions
  unfold BinaryTreeMap.getResult
  unfold optionToResult
  unfold BinaryTreeMap.get
  unfold BinaryTreeMap.empty
  -- The root is none, so get returns none, which becomes KeyNotFound
  simp

-- Core correctness theorems for binary tree map operations

-- Property 1: Insert then get returns the inserted value
theorem insert_then_get {K V : Type} [LT K] [DecidableRel (· < · : K → K → Prop)] 
    [DecidableEq K] (map : BinaryTreeMap K V) (key : K) (value : V) :
    (map.insert key value).get key = some value := by
  sorry

-- Property 2: Delete then get returns none
theorem delete_then_get_none {K V : Type} [LT K] [DecidableRel (· < · : K → K → Prop)] 
    [DecidableEq K] (map : BinaryTreeMap K V) (key : K) :
    let (newMap, _) := map.delete key
    newMap.get key = none := by
  sorry

-- Property 3: Delete preserves other keys
theorem delete_preserves_others {K V : Type} [LT K] [DecidableRel (· < · : K → K → Prop)] 
    [DecidableEq K] (map : BinaryTreeMap K V) (deleteKey otherKey : K) (h : deleteKey ≠ otherKey) :
    let (newMap, _) := map.delete deleteKey
    newMap.get otherKey = map.get otherKey := by
  sorry

-- Property 4: Insert preserves other keys (unless overwriting)
theorem insert_preserves_others {K V : Type} [LT K] [DecidableRel (· < · : K → K → Prop)] 
    [DecidableEq K] (map : BinaryTreeMap K V) (insertKey otherKey : K) (value : V) 
    (h : insertKey ≠ otherKey) :
    (map.insert insertKey value).get otherKey = map.get otherKey := by
  sorry

-- Property 5: Delete returns the correct value when key exists  
theorem delete_returns_value {K V : Type} [LT K] [DecidableRel (· < · : K → K → Prop)] 
    [DecidableEq K] (map : BinaryTreeMap K V) (key : K) (value : V) 
    (h : map.get key = some value) :
    let (_, deletedValue) := map.delete key
    deletedValue = some value := by
  sorry

-- Property 6: Delete from empty map returns none
theorem delete_empty_returns_none {K V : Type} [LT K] [DecidableRel (· < · : K → K → Prop)] 
    (key : K) :
    (BinaryTreeMap.empty : BinaryTreeMap K V).delete key = (BinaryTreeMap.empty, none) := by
  sorry

-- Additional property: get is deterministic
theorem get_deterministic {K V : Type} [LT K] [DecidableRel (· < · : K → K → Prop)] 
    (map : BinaryTreeMap K V) (key : K) : 
    map.get key = map.get key := by
  rfl

#check empty_map_get_returns_error
#check get_deterministic
#check insert_then_get
