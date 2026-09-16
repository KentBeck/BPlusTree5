import Std.Data.HashMap
import BPlusTree.Model.Tree
import BPlusTree.Model.Delete
import BPlusTree.Model.Read

/-!
# The heap model

The tree model has no allocation, so "no double free" is vacuous there.
This lower model keeps nodes in a store keyed by node identity, the way
the Rust keeps them behind raw pointers, and runs every operation as
explicit state passing whose primitives can fault: a read, write or
free of an unallocated id is `none`, and so is a violated precondition
that the Rust only `debug_assert!`s (freeing a leaf that still holds
items). Success (`some`) on every input is therefore the memory-safety
statement.

Leaves carry their `prev` / `next` sibling ids, so the doubly-linked
chain that `link_leaf_after` and `unlink_leaf` maintain is in the model,
and `range` walks it the way `Items::next` does instead of assuming it.

Node contents are computed by the same functions the tree model uses
(`leafInsertOrSplit`, `branchApplySplit`, `leafRemove`, ...); what this
model adds is exactly the plumbing the tree model abstracts away: which
node is read, written, allocated, linked, unlinked and freed, and in
what order. Allocation and freeing sites mirror `alloc_leaf_block`,
`alloc_branch_block`, `free_emptied_leaf`, `free_emptied_branch`,
`empty_branch` and `drop_subtree`.

Recursion over ids is not structural, so the descents take a `fuel`
argument and fault when it runs out; a tree of height `h` needs
`h + 1`.
-/

namespace BPlusTree

open Std

section HeapModel

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-- A node's identity: the Rust's pointer. -/
abbrev NodeId := Nat

/-- What a node block holds. A leaf's `prev` / `next` are its sibling
links (`None` at the ends of the chain); a branch holds `children[0]` and
its `(separator, child)` entries. -/
inductive NodeRec (K V : Type) where
  | leaf (kvs : Leaf K V) (prev next : Option NodeId)
  | branch (c0 : NodeId) (entries : List (K × NodeId))

/-- The store: allocated nodes by id, and the next id to hand out. -/
structure Heap (K V : Type) where
  nodes : Std.HashMap NodeId (NodeRec K V)
  fresh : NodeId

namespace Heap

def empty : Heap K V := ⟨∅, 0⟩

/-- A read: `None` for an unallocated id. -/
def get (h : Heap K V) (id : NodeId) : Option (NodeRec K V) := h.nodes[id]?

/-- `alloc_leaf_block` / `alloc_branch_block`: a fresh id, never a fault. -/
def alloc (h : Heap K V) (r : NodeRec K V) : NodeId × Heap K V :=
  (h.fresh, ⟨h.nodes.insert h.fresh r, h.fresh + 1⟩)

/-- A write through an id: faults on an unallocated one. -/
def write (h : Heap K V) (id : NodeId) (r : NodeRec K V) : Option (Heap K V) :=
  if h.nodes.contains id then some ⟨h.nodes.insert id r, h.fresh⟩ else none

/-- `free_leaf_block` / `free_branch_block`: faults on an unallocated id,
which is what a double free is. -/
def free (h : Heap K V) (id : NodeId) : Option (Heap K V) :=
  if h.nodes.contains id then some ⟨h.nodes.erase id, h.fresh⟩ else none

def getLeaf (h : Heap K V) (id : NodeId) : Option (Leaf K V × Option NodeId × Option NodeId) :=
  match h.get id with
  | some (.leaf kvs p n) => some (kvs, p, n)
  | _ => none

def getBranch (h : Heap K V) (id : NodeId) : Option (NodeId × List (K × NodeId)) :=
  match h.get id with
  | some (.branch c0 es) => some (c0, es)
  | _ => none

def setLeaf (h : Heap K V) (id : NodeId) (kvs : Leaf K V) : Option (Heap K V) := do
  let (_, p, n) ← h.getLeaf id
  h.write id (.leaf kvs p n)

def setPrev (h : Heap K V) (id : NodeId) (p : Option NodeId) : Option (Heap K V) := do
  let (kvs, _, n) ← h.getLeaf id
  h.write id (.leaf kvs p n)

def setNext (h : Heap K V) (id : NodeId) (n : Option NodeId) : Option (Heap K V) := do
  let (kvs, p, _) ← h.getLeaf id
  h.write id (.leaf kvs p n)

def setBranch (h : Heap K V) (id : NodeId) (c0 : NodeId) (es : List (K × NodeId)) :
    Option (Heap K V) :=
  h.write id (.branch c0 es)

/-- `node_len`. -/
def nodeLen (h : Heap K V) (id : NodeId) : Option Nat :=
  match h.get id with
  | some (.leaf kvs _ _) => some kvs.length
  | some (.branch _ es) => some es.length
  | none => none

end Heap

/-- `children[i]` of a branch in entry view. -/
def childAt (c0 : NodeId) (es : List (K × NodeId)) (i : Nat) : Option NodeId :=
  (c0 :: es.map (·.2))[i]?

/-! ## The sibling chain -/

/-- `link_leaf_after`: splice `right` in after `leaf`. -/
def linkLeafAfter (h : Heap K V) (leaf right : NodeId) : Option (Heap K V) := do
  let (_, _, oldNext) ← h.getLeaf leaf
  let h ← h.setNext leaf (some right)
  let h ← h.setNext right oldNext
  let h ← h.setPrev right (some leaf)
  match oldNext with
  | none => some h
  | some o => h.setPrev o (some right)

/-- `unlink_leaf`: splice `leaf` out and clear its own links. -/
def unlinkLeaf (h : Heap K V) (leaf : NodeId) : Option (Heap K V) := do
  let (_, prev, next) ← h.getLeaf leaf
  let h ← match prev with
    | none => some h
    | some p => h.setNext p next
  let h ← match next with
    | none => some h
    | some n => h.setPrev n prev
  let h ← h.setNext leaf none
  h.setPrev leaf none

/-- `free_emptied_leaf`: the leaf must already be empty (the Rust
`debug_assert!`), then unlink and free. -/
def freeEmptiedLeaf (h : Heap K V) (leaf : NodeId) : Option (Heap K V) := do
  let (kvs, _, _) ← h.getLeaf leaf
  if kvs.isEmpty then
    let h ← unlinkLeaf h leaf
    h.free leaf
  else none

/-- `free_emptied_branch`: the branch must hold no separators. -/
def freeEmptiedBranch (h : Heap K V) (id : NodeId) : Option (Heap K V) := do
  let (_, es) ← h.getBranch id
  if es.isEmpty then h.free id else none

/-- `empty_branch`: drop the separators a branch still owns. -/
def emptyBranch (h : Heap K V) (id : NodeId) : Option (Heap K V) := do
  let (c0, _) ← h.getBranch id
  h.setBranch id c0 []

/-! ## Insert -/

/-- `InsertResult` as the heap sees it: the split-off sibling is an id. -/
inductive InsertResH (K V : Type) where
  | noSplit (old : Option V)
  | split (sep : K) (right : NodeId) (old : Option V)

/-- `insert_rec`. A child that splits stays in its slot (its id does not
change), so the parent only ever absorbs `(sep, right)` at `child_idx`. -/
def insertRecH (lc bc : Nat) (k : K) (v : V) :
    Nat → Heap K V → NodeId → Option (InsertResH K V × Heap K V)
  | 0, _, _ => none
  | fuel + 1, h, id =>
    match h.get id with
    | none => none
    | some (.leaf kvs prev next) =>
      match leafInsertOrSplit lc kvs k v with
      | .noSplit l old => (h.write id (.leaf l prev next)).map fun h => (.noSplit old, h)
      | .split l r sep => do
        -- `split_leaf`: allocate the right sibling, move the upper half
        -- across, link it in after this leaf.
        let (rid, h) := h.alloc (.leaf r none none)
        let h ← h.write id (.leaf l prev next)
        let h ← linkLeafAfter h id rid
        some (.split sep rid none, h)
    | some (.branch c0 es) =>
      let A := es.takeWhile (sepLE k)
      match insertRecH lc bc k v fuel h (lastChild c0 A) with
      | none => none
      | some (.noSplit old, h) => some (.noSplit old, h)
      | some (.split sep rid old, h) =>
        -- `branch_apply_split`
        match branchApplySplit bc ⟨c0, es⟩ A.length sep rid with
        | .noSplit b => (h.write id (.branch b.c0 b.entries)).map fun h => (.noSplit old, h)
        | .split l pk r => do
          let (rid', h) := h.alloc (.branch r.c0 r.entries)
          let h ← h.write id (.branch l.c0 l.entries)
          some (.split pk rid' old, h)

/-- `BPlusTreeMap`: the store, the root id (`None` after `clear`), and
`entry_count`. -/
structure HeapMap (K V : Type) where
  heap : Heap K V
  root : Option NodeId
  count : Nat

/-- `with_caps`: a fresh empty leaf as the root. -/
def HeapMap.new : HeapMap K V :=
  match Heap.empty.alloc (.leaf [] none none) with
  | (id, h) => ⟨h, some id, 0⟩

/-- `insert`, with `grow_root` when the root splits and `insert_inner`'s
fresh root leaf when there is none. -/
def insertH (lc bc fuel : Nat) (m : HeapMap K V) (k : K) (v : V) :
    Option (Option V × HeapMap K V) := do
  let (root, h) := match m.root with
    | some r => (r, m.heap)
    | none => m.heap.alloc (.leaf [] none none)
  match ← insertRecH lc bc k v fuel h root with
  | (.noSplit old, h) =>
    some (old, ⟨h, some root, if old.isNone then m.count + 1 else m.count⟩)
  | (.split sep rid old, h) =>
    let (nr, h) := h.alloc (.branch root [(sep, rid)])
    some (old, ⟨h, some nr, if old.isNone then m.count + 1 else m.count⟩)

/-! ## Remove -/

/-- `child_len`: reads `children[idx]` unchecked, so a missing slot or an
unallocated child is a fault. -/
def childLenH (h : Heap K V) (children : List NodeId) (idx : Nat) : Option Nat := do
  let id ← children[idx]?
  h.nodeLen id

/-- `plan_rebalance`, reading only the siblings it consults. -/
def planRebalanceH (h : Heap K V) (children : List NodeId) (childIdx branchLen min : Nat) :
    Option Rebalance :=
  let hasLeft := decide (childIdx > 0)
  let hasRight := decide (childIdx < branchLen)
  let borrowLeft : Option Bool :=
    if hasLeft then (childLenH h children (childIdx - 1)).map (· > min) else some false
  borrowLeft.bind fun bl =>
    if bl then some .borrowFromLeft
    else
      let borrowRight : Option Bool :=
        if hasRight then (childLenH h children (childIdx + 1)).map (· > min) else some false
      borrowRight.bind fun br =>
        if br then some .borrowFromRight
        else if hasLeft then some .mergeWithLeft
        else some .mergeWithRight

/-- Replace the key of entry `i`, keeping its child. -/
def setSep (es : List (K × NodeId)) (i : Nat) (s : K) : List (K × NodeId) :=
  match es[i]? with
  | some (_, c) => es.set i (s, c)
  | none => es

/-- `rotate_leaf_right`. -/
def rotateLeafRightH (h : Heap K V) (branch : NodeId) (sepIdx : Nat) : Option (Heap K V) := do
  let (c0, es) ← h.getBranch branch
  let left ← childAt c0 es sepIdx
  let right ← childAt c0 es (sepIdx + 1)
  let (L, _, _) ← h.getLeaf left
  let (R, _, _) ← h.getLeaf right
  let last ← L.getLast?
  let h ← h.setLeaf left L.dropLast
  let h ← h.setLeaf right (last :: R)
  h.setBranch branch c0 (setSep es sepIdx last.1)

/-- `rotate_leaf_left`. -/
def rotateLeafLeftH (h : Heap K V) (branch : NodeId) (sepIdx : Nat) : Option (Heap K V) := do
  let (c0, es) ← h.getBranch branch
  let left ← childAt c0 es sepIdx
  let right ← childAt c0 es (sepIdx + 1)
  let (L, _, _) ← h.getLeaf left
  let (R, _, _) ← h.getLeaf right
  match R with
  | first :: R'@(newFirst :: _) => do
    let h ← h.setLeaf left (L ++ [first])
    let h ← h.setLeaf right R'
    h.setBranch branch c0 (setSep es sepIdx newFirst.1)
  | _ => none

/-- `merge_leaf_pair`: `merge_leaf_into`, `free_emptied_leaf`, then
`remove_branch_entry`. -/
def mergeLeafPairH (h : Heap K V) (branch : NodeId) (leftIdx : Nat) : Option (Heap K V) := do
  let (c0, es) ← h.getBranch branch
  let left ← childAt c0 es leftIdx
  let right ← childAt c0 es (leftIdx + 1)
  let (L, _, _) ← h.getLeaf left
  let (R, _, _) ← h.getLeaf right
  let h ← h.setLeaf left (L ++ R)
  let h ← h.setLeaf right []
  let h ← freeEmptiedLeaf h right
  h.setBranch branch c0 (es.eraseIdx leftIdx)

/-- `rotate_branch_right`. -/
def rotateBranchRightH (h : Heap K V) (branch : NodeId) (sepIdx : Nat) : Option (Heap K V) := do
  let (c0, es) ← h.getBranch branch
  let left ← childAt c0 es sepIdx
  let right ← childAt c0 es (sepIdx + 1)
  let (sep, _) ← es[sepIdx]?
  let (lc0, les) ← h.getBranch left
  let (rc0, res) ← h.getBranch right
  let (promoted, movedChild) ← les.getLast?
  let h ← h.setBranch left lc0 les.dropLast
  let h ← h.setBranch right movedChild ((sep, rc0) :: res)
  h.setBranch branch c0 (setSep es sepIdx promoted)

/-- `rotate_branch_left`. -/
def rotateBranchLeftH (h : Heap K V) (branch : NodeId) (sepIdx : Nat) : Option (Heap K V) := do
  let (c0, es) ← h.getBranch branch
  let left ← childAt c0 es sepIdx
  let right ← childAt c0 es (sepIdx + 1)
  let (sep, _) ← es[sepIdx]?
  let (lc0, les) ← h.getBranch left
  let (rc0, res) ← h.getBranch right
  match res with
  | (promoted, rch1) :: rest => do
    let h ← h.setBranch left lc0 (les ++ [(sep, rc0)])
    let h ← h.setBranch right rch1 rest
    h.setBranch branch c0 (setSep es sepIdx promoted)
  | [] => none

/-- `merge_branch_pair`: `remove_branch_entry`, `merge_branch_into` (which
empties the source), then `free_emptied_branch`. -/
def mergeBranchPairH (h : Heap K V) (branch : NodeId) (leftIdx : Nat) : Option (Heap K V) := do
  let (c0, es) ← h.getBranch branch
  let left ← childAt c0 es leftIdx
  let right ← childAt c0 es (leftIdx + 1)
  let (sep, _) ← es[leftIdx]?
  let (lc0, les) ← h.getBranch left
  let (rc0, res) ← h.getBranch right
  let h ← h.setBranch branch c0 (es.eraseIdx leftIdx)
  let h ← h.setBranch left lc0 (les ++ (sep, rc0) :: res)
  let h ← h.setBranch right rc0 []
  freeEmptiedBranch h right

/-- `rebalance_leaf_child`. -/
def rebalanceLeafChildH (lc : Nat) (h : Heap K V) (branch : NodeId) (childIdx len : Nat) :
    Option (Bool × Heap K V) := do
  let (c0, es) ← h.getBranch branch
  let repair ← planRebalanceH h (c0 :: es.map (·.2)) childIdx len (minLeafLen lc)
  let h ← match repair with
    | .borrowFromLeft => rotateLeafRightH h branch (childIdx - 1)
    | .borrowFromRight => rotateLeafLeftH h branch childIdx
    | .mergeWithLeft => mergeLeafPairH h branch (childIdx - 1)
    | .mergeWithRight => mergeLeafPairH h branch childIdx
  some (repair.mergesSiblings, h)

/-- `rebalance_branch_child`. -/
def rebalanceBranchChildH (bc : Nat) (h : Heap K V) (branch : NodeId) (childIdx len : Nat) :
    Option (Bool × Heap K V) := do
  let (c0, es) ← h.getBranch branch
  let repair ← planRebalanceH h (c0 :: es.map (·.2)) childIdx len (minBranchLen bc)
  let h ← match repair with
    | .borrowFromLeft => rotateBranchRightH h branch (childIdx - 1)
    | .borrowFromRight => rotateBranchLeftH h branch childIdx
    | .mergeWithLeft => mergeBranchPairH h branch (childIdx - 1)
    | .mergeWithRight => mergeBranchPairH h branch childIdx
  some (repair.mergesSiblings, h)

/-- `fix_branch_child`. -/
def fixBranchChildH (lc bc : Nat) (h : Heap K V) (branch : NodeId) (childIdx : Nat) :
    Option (Bool × Heap K V) := do
  let (c0, es) ← h.getBranch branch
  let len := es.length
  let child ← childAt c0 es childIdx
  let (merged, h) ← match h.get child with
    | some (.leaf ..) => rebalanceLeafChildH lc h branch childIdx len
    | some (.branch ..) => rebalanceBranchChildH bc h branch childIdx len
    | none => none
  some (merged && decide (len - 1 < minBranchLen bc), h)

/-- `remove_rec`: `none` is a fault; `some (none, h)` means the key was
absent; `some (some (v, under), h)` returns the value and the underflow
flag. -/
def removeRecH (lc bc : Nat) (k : K) :
    Nat → Heap K V → NodeId → Option (Option (V × Bool) × Heap K V)
  | 0, _, _ => none
  | fuel + 1, h, id =>
    match h.get id with
    | none => none
    | some (.leaf kvs prev next) =>
      match leafRemove kvs k with
      | none => some (none, h)
      | some (v, kvs') =>
        (h.write id (.leaf kvs' prev next)).map fun h =>
          (some (v, decide (kvs'.length < minLeafLen lc)), h)
    | some (.branch c0 es) =>
      let A := es.takeWhile (sepLE k)
      match removeRecH lc bc k fuel h (lastChild c0 A) with
      | none => none
      | some (none, h) => some (none, h)
      | some (some (v, under), h) =>
        if under then
          (fixBranchChildH lc bc h id A.length).map fun (u, h) => (some (v, u), h)
        else some (some (v, false), h)

/-- `try_merge_leaves`. -/
def tryMergeLeavesH (lc : Nat) (h : Heap K V) (target source : NodeId) :
    Option (Bool × Heap K V) :=
  match h.get target, h.get source with
  | some (.leaf T _ _), some (.leaf S _ _) =>
    if T.length + S.length > lc then some (false, h)
    else do
      let h ← h.setLeaf target (T ++ S)
      let h ← h.setLeaf source []
      let h ← freeEmptiedLeaf h source
      some (true, h)
  | some _, some _ => some (false, h)
  | _, _ => none

/-- `replace_root`: empty the old root, make a leaf survivor's `prev`
null (`make_leaf_root`), free the old root. -/
def replaceRootH (h : Heap K V) (root survivor : NodeId) : Option (NodeId × Heap K V) := do
  let h ← emptyBranch h root
  let h ← match h.get survivor with
    | some (.leaf ..) => h.setPrev survivor none
    | some (.branch ..) => some h
    | none => none
  let h ← freeEmptiedBranch h root
  some (survivor, h)

/-- `check_root_collapse` on a root branch with at most two children. -/
def checkRootCollapseH (lc : Nat) (h : Heap K V) (root : NodeId) : Option (NodeId × Heap K V) := do
  let (c0, es) ← h.getBranch root
  match es with
  | [] => replaceRootH h root c0
  | [(_, c1)] => do
    let (merged, h) ← tryMergeLeavesH lc h c0 c1
    if merged then replaceRootH h root c0 else some (root, h)
  | _ => none

/-- `remove`. -/
def removeH (lc bc fuel : Nat) (m : HeapMap K V) (k : K) : Option (Option V × HeapMap K V) := do
  match m.root with
  | none => some (none, m)
  | some root =>
    match ← removeRecH lc bc k fuel m.heap root with
    | (none, h) => some (none, { m with heap := h })
    | (some (v, _), h) =>
      let count := m.count - 1
      match h.get root with
      | some (.branch _ es) =>
        if es.length ≤ 1 then do
          let (r', h) ← checkRootCollapseH lc h root
          some (some v, ⟨h, some r', count⟩)
        else some (some v, ⟨h, some root, count⟩)
      | some (.leaf ..) => some (some v, ⟨h, some root, count⟩)
      | none => none

/-! ## Reads -/

/-- `leaf_for_key`: the id of the leaf reached. -/
def leafForKeyH (k : K) : Nat → Heap K V → NodeId → Option NodeId
  | 0, _, _ => none
  | fuel + 1, h, id =>
    match h.get id with
    | some (.leaf ..) => some id
    | some (.branch c0 es) => leafForKeyH k fuel h (lastChild c0 (es.takeWhile (sepLE k)))
    | none => none

/-- `get`. -/
def getH (fuel : Nat) (m : HeapMap K V) (k : K) : Option (Option V) := do
  match m.root with
  | none => some none
  | some root =>
    let leaf ← leafForKeyH k fuel m.heap root
    let (kvs, _, _) ← m.heap.getLeaf leaf
    some ((leafSearch kvs k).map (·.2))

/-- `leftmost_leaf`. -/
def leftmostLeafH : Nat → Heap K V → NodeId → Option NodeId
  | 0, _, _ => none
  | fuel + 1, h, id =>
    match h.get id with
    | some (.leaf ..) => some id
    | some (.branch c0 _) => leftmostLeafH fuel h c0
    | none => none

/-- `rightmost_leaf`. -/
def rightmostLeafH : Nat → Heap K V → NodeId → Option NodeId
  | 0, _, _ => none
  | fuel + 1, h, id =>
    match h.get id with
    | some (.leaf ..) => some id
    | some (.branch c0 es) => rightmostLeafH fuel h (lastChild c0 es)
    | none => none

/-- `first`. -/
def firstH (fuel : Nat) (m : HeapMap K V) : Option (Option (K × V)) := do
  match m.root with
  | none => some none
  | some root =>
    let leaf ← leftmostLeafH fuel m.heap root
    let (kvs, _, _) ← m.heap.getLeaf leaf
    some kvs.head?

/-- `last`. -/
def lastH (fuel : Nat) (m : HeapMap K V) : Option (Option (K × V)) := do
  match m.root with
  | none => some none
  | some root =>
    let leaf ← rightmostLeafH fuel m.heap root
    let (kvs, _, _) ← m.heap.getLeaf leaf
    some kvs.getLast?

/-- `cut_in_leaf`: `(leaf, cut, len)`. -/
def cutInLeafH (fuel : Nat) (h : Heap K V) (root : NodeId) (k : K) (afterEqual : Bool) :
    Option (NodeId × Nat × Nat) := do
  let leaf ← leafForKeyH k fuel h root
  let (kvs, _, _) ← h.getLeaf leaf
  let cut := if afterEqual then (kvs.takeWhile fun e => decide (¬ k < e.1)).length
    else (kvs.takeWhile fun e => decide (e.1 < k)).length
  some (leaf, cut, kvs.length)

/-- `resolve_front`: `some none` is an empty range, `none` a fault. -/
def resolveFrontH (fuel : Nat) (h : Heap K V) (root : NodeId) (start : Bound K) :
    Option (Option (NodeId × Nat)) := do
  match start.key with
  | none =>
    let leaf ← leftmostLeafH fuel h root
    let (kvs, _, _) ← h.getLeaf leaf
    some (if kvs.length > 0 then some (leaf, 0) else none)
  | some k =>
    let afterEqual := match start with
      | .excluded _ => true
      | _ => false
    let (leaf, cut, len) ← cutInLeafH fuel h root k afterEqual
    if cut < len then some (some (leaf, cut))
    else
      let (_, _, next) ← h.getLeaf leaf
      some (next.map fun n => (n, 0))

/-- `resolve_back`. -/
def resolveBackH (fuel : Nat) (h : Heap K V) (root : NodeId) (stop : Bound K) :
    Option (Option (NodeId × Nat)) := do
  match stop.key with
  | none =>
    let leaf ← rightmostLeafH fuel h root
    let (kvs, _, _) ← h.getLeaf leaf
    some (if kvs.length > 0 then some (leaf, kvs.length) else none)
  | some k =>
    let afterEqual := match stop with
      | .included _ => true
      | _ => false
    let (leaf, cut, _) ← cutInLeafH fuel h root k afterEqual
    if cut > 0 then some (some (leaf, cut))
    else
      let (_, prev, _) ← h.getLeaf leaf
      match prev with
      | none => some none
      | some p => do
        let (pk, _, _) ← h.getLeaf p
        some (some (p, pk.length))

/-- `Items::next`, drained: yield from the front position, hopping along
`next` until the back leaf. A missing `next` before the back leaf ends
the iteration, as it does in the Rust. -/
def drainH : Nat → Heap K V → NodeId × Nat → NodeId × Nat → Option (List (K × V))
  | 0, _, _, _ => none
  | fuel + 1, h, (fl, fi), (bl, bi) => do
    let (kvs, _, next) ← h.getLeaf fl
    if fl == bl then some ((kvs.drop fi).take (bi - fi))
    else
      match next with
      | none => some (kvs.drop fi)
      | some n => do
        let rest ← drainH fuel h (n, 0) (bl, bi)
        some (kvs.drop fi ++ rest)

/-- `make_items`, drained. `hops` bounds the chain walk (any bound on the
number of leaves will do). -/
def rangeH (fuel hops : Nat) (m : HeapMap K V) (start stop : Bound K) : Option (List (K × V)) := do
  match m.root with
  | none => some []
  | some root =>
    match ← resolveFrontH fuel m.heap root start with
    | none => some []
    | some (fl, fi) =>
      match ← resolveBackH fuel m.heap root stop with
      | none => some []
      | some (bl, bi) =>
        let (kvs, _, _) ← m.heap.getLeaf fl
        let first ← kvs[fi]?
        let inRange := match stop with
          | .unbounded => true
          | .included e => decide (¬ e < first.1)
          | .excluded e => decide (first.1 < e)
        if inRange then drainH hops m.heap (fl, fi) (bl, bi) else some []

/-! ## Drop -/

/-- `drop_subtree`: free every node below `id`, children first. -/
def dropSubtreeH : Nat → Heap K V → NodeId → Option (Heap K V)
  | 0, _, _ => none
  | fuel + 1, h, id =>
    match h.get id with
    | none => none
    | some (.leaf ..) => h.free id
    | some (.branch c0 es) => do
      let h ← dropSubtreeH fuel h c0
      let h ← dropChildrenH fuel h es
      h.free id
where
  dropChildrenH : Nat → Heap K V → List (K × NodeId) → Option (Heap K V)
    | _, h, [] => some h
    | fuel, h, (_, c) :: rest => do
      let h ← dropSubtreeH fuel h c
      dropChildrenH fuel h rest

/-- `clear`: drop the tree and forget the root. -/
def clearH (fuel : Nat) (m : HeapMap K V) : Option (HeapMap K V) := do
  match m.root with
  | none => some { m with count := 0 }
  | some root =>
    let h ← dropSubtreeH fuel m.heap root
    some ⟨h, none, 0⟩

/-! ## Abstraction and the heap invariant, as executable checks -/

/-- The tree a subtree of the store denotes, if it is a tree at all. -/
def absNode : Nat → Heap K V → NodeId → Option (Node K V)
  | 0, _, _ => none
  | fuel + 1, h, id =>
    match h.get id with
    | none => none
    | some (.leaf kvs _ _) => some (.leaf kvs)
    | some (.branch c0 es) => do
      let c0' ← absNode fuel h c0
      let es' ← absEntries fuel h es
      some (.branch c0' es')
where
  absEntries : Nat → Heap K V → List (K × NodeId) → Option (List (K × Node K V))
    | _, _, [] => some []
    | fuel, h, (s, c) :: rest => do
      let c' ← absNode fuel h c
      let rest' ← absEntries fuel h rest
      some ((s, c') :: rest')

/-- Every id below `id`, preorder. -/
def reachIds : Nat → Heap K V → NodeId → Option (List NodeId)
  | 0, _, _ => none
  | fuel + 1, h, id =>
    match h.get id with
    | none => none
    | some (.leaf ..) => some [id]
    | some (.branch c0 es) => do
      let below ← reachChildren fuel h (c0 :: es.map (·.2))
      some (id :: below)
where
  reachChildren : Nat → Heap K V → List NodeId → Option (List NodeId)
    | _, _, [] => some []
    | fuel, h, c :: rest => do
      let l ← reachIds fuel h c
      let r ← reachChildren fuel h rest
      some (l ++ r)

/-- The leaf ids below `id`, left to right: the order the chain must have. -/
def leafIds : Nat → Heap K V → NodeId → Option (List NodeId)
  | 0, _, _ => none
  | fuel + 1, h, id =>
    match h.get id with
    | none => none
    | some (.leaf ..) => some [id]
    | some (.branch c0 es) => leafChildren fuel h (c0 :: es.map (·.2))
where
  leafChildren : Nat → Heap K V → List NodeId → Option (List NodeId)
    | _, _, [] => some []
    | fuel, h, c :: rest => do
      let l ← leafIds fuel h c
      let r ← leafChildren fuel h rest
      some (l ++ r)

/-- The chain links agree with the leaf order: each leaf's `prev` is the
leaf before it (`None` for the first) and its `next` the one after. -/
def chainOK (h : Heap K V) : Option NodeId → List NodeId → Bool
  | _, [] => true
  | prev, id :: rest =>
    match h.getLeaf id with
    | some (_, p, n) => p == prev && n == rest.head? && chainOK h (some id) rest
    | none => false

/-- The invariant the proofs maintain, as a check the replay can run: the
store holds exactly the nodes reachable from the root, none twice, all
below `fresh`, and the leaves are chained in tree order. -/
def heapInvOK (fuel : Nat) (m : HeapMap K V) : Bool :=
  match m.root with
  | none => m.heap.nodes.isEmpty
  | some root =>
    match reachIds fuel m.heap root, leafIds fuel m.heap root with
    | some ids, some leaves =>
      let seen : Std.HashSet NodeId := ids.foldl (fun s i => s.insert i) ∅
      seen.size == ids.length && ids.length == m.heap.nodes.size &&
        ids.all (fun i => i < m.heap.fresh) && chainOK m.heap none leaves
    | _, _ => false

end HeapModel

end BPlusTree
