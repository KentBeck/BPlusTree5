import BPlusTree.Model.Tree
import BPlusTree.Model.Spec

/-!
# Model of the read paths: `get.rs`, `first`, `last`, and `range`

Each Rust read walks the tree to a leaf and then works inside it. `range`
also walks the leaves' sibling chain (`next_ptr` / `prev_ptr`), which the
tree model does not carry: the chain lists the leaves in tree order (the
Rust invariant checker verifies this at every replay check line), so a
position `(leaf, idx)` is modelled as the index of that slot in `toList`,
and hopping to a neighbouring leaf is moving that index past the current
leaf. `leafForKey` therefore returns, with the leaf, the entries of the
leaves to its left and right: what the chain reaches from it.
-/

namespace BPlusTree

open Std

section Read

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-- `leaf_for_key`: descend by `child_for_key` (the child after the
separators `≤ k`, as `insertRec` and `removeRec` do) down to a leaf.
Returns the entries before that leaf, the leaf, and the entries after it. -/
def leafForKey (k : K) : Node K V → List (K × V) × Leaf K V × List (K × V)
  | .leaf kvs => ([], kvs, [])
  | .branch c0 es =>
    let A := es.takeWhile (sepLE k)
    let B := es.dropWhile (sepLE k)
    match leafForKey k (lastChild c0 A) with
    | (pre, leaf, post) => (frontList c0 A ++ pre, leaf, post ++ entriesToList B)
termination_by n => sizeOf n
decreasing_by
  simp_wf
  have h1 := sizeOf_lastChild c0 (es.takeWhile (sepLE k))
  have h2 := sizeOf_takeWhile_le (sepLE k) es
  omega

/-- `leaf_search`: `binary_search_keys` lands on the first key `≥ k`
(`lowerBound`) and answers `Ok` exactly when the key there is `k`. -/
def leafSearch (kvs : Leaf K V) (k : K) : Option (K × V) :=
  match kvs[lowerBound kvs k]? with
  | some e => if k < e.1 then none else some e
  | none => none

/-- `get`. -/
def getTree (root : Node K V) (k : K) : Option V :=
  match leafForKey k root with
  | (_, leaf, _) => (leafSearch leaf k).map (·.2)

/-- `leftmost_leaf`: `children[0]` all the way down. -/
def leftmostLeaf : Node K V → Leaf K V
  | .leaf kvs => kvs
  | .branch c0 _ => leftmostLeaf c0

/-- `rightmost_leaf`: `children[len]` all the way down. -/
def rightmostLeaf : Node K V → Leaf K V
  | .leaf kvs => kvs
  | .branch c0 es => rightmostLeaf (lastChild c0 es)
termination_by n => sizeOf n
decreasing_by
  simp_wf
  have h1 := sizeOf_lastChild c0 es
  omega

/-- `first`: the leftmost leaf's first slot; `None` when that leaf is
empty, which only a root leaf can be. -/
def firstTree (root : Node K V) : Option (K × V) := (leftmostLeaf root).head?

/-- `last`: the rightmost leaf's last slot. -/
def lastTree (root : Node K V) : Option (K × V) := (rightmostLeaf root).getLast?

/-- `bound_key`. -/
def Bound.key : Bound K → Option K
  | .unbounded => none
  | .included k => some k
  | .excluded k => some k

/-- `cut_in_leaf`: the leaf that would hold `k` and the index that cuts
its keys into those before `k` and those after. With `afterEqual` the
cut is `partition_point(|x| x <= k)`, otherwise `partition_point(|x| x < k)`.
Returned with the entries before and after the leaf, so the cut's index
into `toList` is `pre.length + cut`. -/
def cutInLeaf (root : Node K V) (k : K) (afterEqual : Bool) :
    List (K × V) × Leaf K V × Nat × List (K × V) :=
  match leafForKey k root with
  | (pre, leaf, post) =>
    let cut := if afterEqual then (leaf.takeWhile fun e => decide (¬ k < e.1)).length
      else (leaf.takeWhile fun e => decide (e.1 < k)).length
    (pre, leaf, cut, post)

/-- `resolve_front`: the position (index into `toList`) of the first
in-range item. An excluded start skips an exact match. When the cut is
past the leaf's last key, the position is the next leaf's first slot,
which exists exactly when there are entries after this leaf. -/
def resolveFront (root : Node K V) (start : Bound K) : Option Nat :=
  match start.key with
  | none => if (leftmostLeaf root).length > 0 then some 0 else none
  | some k =>
    let afterEqual := match start with
      | .excluded _ => true
      | _ => false
    match cutInLeaf root k afterEqual with
    | (pre, leaf, cut, post) =>
      if cut < leaf.length then some (pre.length + cut)
      else
        match post with
        | [] => none
        | _ => some (pre.length + leaf.length)

/-- `resolve_back`: the position one past the last in-range item. An
included end keeps an exact match. When the cut is before the leaf's
first key, the position is the end of the previous leaf, which exists
exactly when there are entries before this leaf. -/
def resolveBack (root : Node K V) (stop : Bound K) : Option Nat :=
  match stop.key with
  | none => if (rightmostLeaf root).length > 0 then some root.toList.length else none
  | some k =>
    let afterEqual := match stop with
      | .included _ => true
      | _ => false
    match cutInLeaf root k afterEqual with
    | (pre, _, cut, _) =>
      if cut > 0 then some (pre.length + cut)
      else
        match pre with
        | [] => none
        | _ => some pre.length

/-- `make_items`, drained: the items `Items::next` yields from the front
position up to the back position. The front slot must itself satisfy the
end bound, or the range (possibly inverted) is empty. -/
def makeItems (root : Node K V) (start stop : Bound K) : List (K × V) :=
  match resolveFront root start with
  | none => []
  | some f =>
    match resolveBack root stop with
    | none => []
    | some b =>
      match root.toList[f]? with
      | none => []
      | some first =>
        let inRange := match stop with
          | .unbounded => true
          | .included e => decide (¬ e < first.1)
          | .excluded e => decide (first.1 < e)
        if inRange then (root.toList.drop f).take (b - f) else []

/-- `range`. -/
def rangeTree (root : Node K V) (start stop : Bound K) : List (K × V) :=
  makeItems root start stop

/-- `items`. -/
def itemsTree (root : Node K V) : List (K × V) := makeItems root .unbounded .unbounded

end Read

end BPlusTree
