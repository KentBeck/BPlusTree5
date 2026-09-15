import BPlusTree.Model.Tree

/-!
# Model of `src/delete.rs`

`delete.rs` works on a branch's `keys[i]` / `children[i]` arrays, so this
file views a branch that way (`Node.keysOf`, `Node.childrenOf`, `mkBranch`)
and mirrors each Rust function by name with its index arithmetic verbatim.
`removeRec` descends the way `insertRec` does (the entries whose separator
is `≤ k`, then `lastChild`), so the two share `replaceLast`.
-/

namespace BPlusTree

open Std

section Delete

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-- `hdr.len`: keys in a node, either kind. -/
def Node.len : Node K V → Nat
  | .leaf kvs => kvs.length
  | .branch _ es => es.length

/-- `keys[0..len)` of a branch. -/
def Node.keysOf : Node K V → List K
  | .leaf _ => []
  | .branch _ es => es.map (·.1)

/-- `children[0..=len]` of a branch. -/
def Node.childrenOf : Node K V → List (Node K V)
  | .leaf _ => []
  | .branch c0 es => c0 :: es.map (·.2)

/-- Rebuild a branch from its arrays. `children` is one longer than `keys`. -/
def mkBranch (keys : List K) (children : List (Node K V)) : Node K V :=
  match children with
  | c0 :: rest => .branch c0 (keys.zip rest)
  -- Unreachable: a branch always has `children[0]`.
  | [] => .leaf []

/-- `min_leaf_len`. -/
def minLeafLen (lc : Nat) : Nat := lc / 2

/-- `min_branch_len`. -/
def minBranchLen (bc : Nat) : Nat := if bc ≤ 2 then 1 else bc / 2

/-- `leaf_remove`: `binary_search(key).ok()`, then close the gap. -/
def leafRemove (kvs : Leaf K V) (k : K) : Option (V × Leaf K V) :=
  let idx := lowerBound kvs k
  match kvs[idx]? with
  | some e => if k < e.1 then none else some (e.2, kvs.eraseIdx idx)
  | none => none

/-- `Rebalance`. -/
inductive Rebalance where
  | borrowFromLeft | borrowFromRight | mergeWithLeft | mergeWithRight

def Rebalance.mergesSiblings : Rebalance → Bool
  | .mergeWithLeft | .mergeWithRight => true
  | _ => false

/-- `child_len`: length of `children[idx]`, or 0 for a missing slot. -/
def childLen (children : List (Node K V)) (idx : Nat) : Nat :=
  match children[idx]? with
  | some n => n.len
  | none => 0

/-- `plan_rebalance`: borrow from a sibling holding more than `min` (left
first), else merge with the left sibling, else the right. -/
def planRebalance (children : List (Node K V)) (childIdx branchLen min : Nat) : Rebalance :=
  let hasLeft := childIdx > 0
  let hasRight := childIdx < branchLen
  if hasLeft && childLen children (childIdx - 1) > min then .borrowFromLeft
  else if hasRight && childLen children (childIdx + 1) > min then .borrowFromRight
  else if hasLeft then .mergeWithLeft
  else .mergeWithRight

/-- `rotate_leaf_right`: the left leaf's last item becomes the right leaf's
first; the separator is re-derived from the right leaf's new first key. -/
def rotateLeafRight (keys : List K) (children : List (Node K V)) (sepIdx : Nat) :
    List K × List (Node K V) :=
  match children[sepIdx]?, children[sepIdx + 1]? with
  | some (.leaf L), some (.leaf R) =>
    match L.getLast? with
    | some last =>
      (keys.set sepIdx last.1,
        (children.set sepIdx (.leaf L.dropLast)).set (sepIdx + 1) (.leaf (last :: R)))
    | none => (keys, children)
  | _, _ => (keys, children)

/-- `rotate_leaf_left`: the right leaf's first item becomes the left leaf's
last; the separator is re-derived from the right leaf's new first key. -/
def rotateLeafLeft (keys : List K) (children : List (Node K V)) (sepIdx : Nat) :
    List K × List (Node K V) :=
  match children[sepIdx]?, children[sepIdx + 1]? with
  | some (.leaf L), some (.leaf (first :: R')) =>
    match R' with
    | newFirst :: _ =>
      (keys.set sepIdx newFirst.1,
        (children.set sepIdx (.leaf (L ++ [first]))).set (sepIdx + 1) (.leaf R'))
    -- Unreachable: the donor holds more than the minimum, so `R'` is nonempty.
    | [] => (keys, children)
  | _, _ => (keys, children)

/-- `merge_leaf_pair`: `children[leftIdx]` absorbs `children[leftIdx + 1]`;
the separator is dropped (`remove_branch_entry`). -/
def mergeLeafPair (keys : List K) (children : List (Node K V)) (leftIdx : Nat) :
    List K × List (Node K V) :=
  match children[leftIdx]?, children[leftIdx + 1]? with
  | some (.leaf L), some (.leaf R) =>
    (keys.eraseIdx leftIdx, (children.set leftIdx (.leaf (L ++ R))).eraseIdx (leftIdx + 1))
  | _, _ => (keys, children)

/-- `rotate_branch_right`: the left child's last key moves up, the old
separator moves down as the right child's first key, and the left child's
last subtree travels with it as the right child's `children[0]`. -/
def rotateBranchRight (keys : List K) (children : List (Node K V)) (sepIdx : Nat) :
    List K × List (Node K V) :=
  match children[sepIdx]?, children[sepIdx + 1]?, keys[sepIdx]? with
  | some (.branch lc0 les), some (.branch rc0 res), some sep =>
    match les.getLast? with
    | some (promoted, movedChild) =>
      (keys.set sepIdx promoted,
        (children.set sepIdx (.branch lc0 les.dropLast)).set (sepIdx + 1)
          (.branch movedChild ((sep, rc0) :: res)))
    | none => (keys, children)
  | _, _, _ => (keys, children)

/-- `rotate_branch_left`: the right child's first key moves up, the old
separator moves down as the left child's last key, and the right child's
`children[0]` travels with it. -/
def rotateBranchLeft (keys : List K) (children : List (Node K V)) (sepIdx : Nat) :
    List K × List (Node K V) :=
  match children[sepIdx]?, children[sepIdx + 1]?, keys[sepIdx]? with
  | some (.branch lc0 les), some (.branch rc0 ((promoted, rch1) :: rest)), some sep =>
    (keys.set sepIdx promoted,
      (children.set sepIdx (.branch lc0 (les ++ [(sep, rc0)]))).set (sepIdx + 1)
        (.branch rch1 rest))
  | _, _, _ => (keys, children)

/-- `merge_branch_pair`: the separator moves down between the two children
(`merge_branch_into`) and its slot closes (`remove_branch_entry`). -/
def mergeBranchPair (keys : List K) (children : List (Node K V)) (leftIdx : Nat) :
    List K × List (Node K V) :=
  match children[leftIdx]?, children[leftIdx + 1]?, keys[leftIdx]? with
  | some (.branch lc0 les), some (.branch rc0 res), some sep =>
    (keys.eraseIdx leftIdx,
      (children.set leftIdx (.branch lc0 (les ++ (sep, rc0) :: res))).eraseIdx (leftIdx + 1))
  | _, _, _ => (keys, children)

/-- `rebalance_leaf_child`. Returns the repaired arrays and whether the
repair merged two children. -/
def rebalanceLeafChild (lc : Nat) (keys : List K) (children : List (Node K V))
    (childIdx branchLen : Nat) : List K × List (Node K V) × Bool :=
  let repair := planRebalance children childIdx branchLen (minLeafLen lc)
  let arrays := match repair with
    | .borrowFromLeft => rotateLeafRight keys children (childIdx - 1)
    | .borrowFromRight => rotateLeafLeft keys children childIdx
    | .mergeWithLeft => mergeLeafPair keys children (childIdx - 1)
    | .mergeWithRight => mergeLeafPair keys children childIdx
  (arrays.1, arrays.2, repair.mergesSiblings)

/-- `rebalance_branch_child`, the structural twin. -/
def rebalanceBranchChild (bc : Nat) (keys : List K) (children : List (Node K V))
    (childIdx branchLen : Nat) : List K × List (Node K V) × Bool :=
  let repair := planRebalance children childIdx branchLen (minBranchLen bc)
  let arrays := match repair with
    | .borrowFromLeft => rotateBranchRight keys children (childIdx - 1)
    | .borrowFromRight => rotateBranchLeft keys children childIdx
    | .mergeWithLeft => mergeBranchPair keys children (childIdx - 1)
    | .mergeWithRight => mergeBranchPair keys children childIdx
  (arrays.1, arrays.2, repair.mergesSiblings)

/-- `fix_branch_child`: repair the underfull `children[childIdx]`; report
whether the branch itself became underfull. -/
def fixBranchChild (lc bc : Nat) (node : Node K V) (childIdx : Nat) : Node K V × Bool :=
  match node with
  | .leaf _ => (node, false)
  | .branch c0 es =>
    let keys := es.map (·.1)
    let children := c0 :: es.map (·.2)
    let len := keys.length
    if len = 0 then (node, true)
    else
      let idx := min childIdx len
      match children[idx]? with
      | none => (node, len < minBranchLen bc)
      | some child =>
        let repaired := match child with
          | .leaf _ => rebalanceLeafChild lc keys children idx len
          | .branch _ _ => rebalanceBranchChild bc keys children idx len
        (mkBranch repaired.1 repaired.2.1, repaired.2.2 && decide (len - 1 < minBranchLen bc))

/-- `remove_rec`: the removed value, the node afterwards, and whether it
became underfull. -/
def removeRec (lc bc : Nat) (k : K) : Node K V → Option (V × Node K V × Bool)
  | .leaf kvs =>
    match leafRemove kvs k with
    | none => none
    | some (v, kvs') => some (v, .leaf kvs', decide (kvs'.length < minLeafLen lc))
  | .branch c0 entries =>
    let A := entries.takeWhile (sepLE k)
    let B := entries.dropWhile (sepLE k)
    match removeRec lc bc k (lastChild c0 A) with
    | none => none
    | some (v, child', childUnderflowed) =>
      match replaceLast c0 A child' with
      | (c0', A') =>
        let node := Node.branch c0' (A' ++ B)
        if childUnderflowed then
          match fixBranchChild lc bc node A.length with
          | (node', under) => some (v, node', under)
        else some (v, node, false)
termination_by n => sizeOf n
decreasing_by
  simp_wf
  have h1 := sizeOf_lastChild c0 (entries.takeWhile (sepLE k))
  have h2 := sizeOf_takeWhile_le (sepLE k) entries
  omega

/-- `consolidate_root_children` with `absorb_root_child` inlined: an
emptied leaf is freed, the first real child becomes the survivor, and a
later leaf is merged into a leaf survivor when it fits. Anything else
blocks the collapse. -/
def consolidateRootChildren (lc : Nat) : Option (Node K V) → List (Node K V) →
    Option (Option (Node K V))
  | survivor, [] => some survivor
  | survivor, child :: rest =>
    match child with
    | .leaf [] => consolidateRootChildren lc survivor rest
    | _ =>
      match survivor with
      | none => consolidateRootChildren lc (some child) rest
      | some kept =>
        match kept, child with
        | .leaf L, .leaf R =>
          if L.length + R.length ≤ lc then consolidateRootChildren lc (some (.leaf (L ++ R))) rest
          else none
        | _, _ => none

/-- `check_root_collapse`. A root with no surviving child becomes the empty
tree, which the model renders as an empty leaf (the Rust `root = None`
allocates a fresh leaf on the next insert). -/
def checkRootCollapse (lc : Nat) (root : Node K V) : Node K V :=
  match root with
  | .leaf _ => root
  | .branch c0 es =>
    if es.length + 1 > 2 then root
    else
      match consolidateRootChildren lc none (c0 :: es.map (·.2)) with
      | none => root
      | some none => .leaf []
      | some (some survivor) => survivor

/-- `remove`. -/
def removeTree (lc bc : Nat) (root : Node K V) (k : K) : Option (V × Node K V) :=
  match removeRec lc bc k root with
  | none => none
  | some (v, root', _) =>
    match root' with
    | .branch _ es => if es.length ≤ 2 then some (v, checkRootCollapse lc root') else some (v, root')
    | .leaf _ => some (v, root')

end Delete

end BPlusTree
