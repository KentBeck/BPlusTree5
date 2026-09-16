import BPlusTree.Model.Leaf

/-!
# Branch-level model of `src/insert.rs`

A branch is its first child plus a list of `(separator, child)` entries:
entry `i` is `(keys[i], children[i + 1])`. This is the "entry view" the
Rust comments describe, and it makes `branch_apply_split` an ordinary
insert into the entry list. Children are an abstract type `C` here; the
tree model supplies the real one.
-/

namespace BPlusTree

universe u
variable {α : Type u}

/-- The fused split: decide how many existing entries stay left
(`left_keep`) from where the new one lands, move the rest right, then
insert the new entry into whichever side it sorts into. `left_count` is the
final left size. `cutInsert_eq` shows this equals "insert, then cut at
`(len + 1) / 2`". -/
def cutInsert (l : List α) (idx : Nat) (x : α) : List α × List α :=
  let leftCount := (l.length + 1) / 2
  let leftKeep := if idx < leftCount then leftCount - 1 else leftCount
  let kept := l.take leftKeep
  let moved := l.drop leftKeep
  if idx < leftCount then (insertAt kept idx x, moved)
  else (kept, insertAt moved (idx - leftKeep) x)

section Branch

variable {K C : Type}

/-- A branch node: `children[0]` and the entries `(keys[i], children[i + 1])`. -/
structure Branch (K C : Type) where
  c0 : C
  entries : List (K × C)

/-- `InsertResult` as a branch sees it from its parent's point of view. -/
inductive BranchInsert (K C : Type) where
  | noSplit (b : Branch K C)
  | split (left : Branch K C) (sep : K) (right : Branch K C)

/-- `branch_insert_and_split`: `cutInsert` on the entries, then promote the
boundary. The right side's first entry's key goes up and its child becomes
the right node's `children[0]` (the "close slot 0" move). -/
def branchInsertAndSplit (b : Branch K C) (idx : Nat) (sep : K) (right : C) :
    Branch K C × K × Branch K C :=
  match cutInsert b.entries idx (sep, right) with
  | (l, r) =>
    match r with
    | (pk, pc) :: rest => (⟨b.c0, l⟩, pk, ⟨pc, rest⟩)
    -- Unreachable: a full branch has `cap ≥ 1` entries, so after the cut
    -- the right side holds at least one.
    | [] => (⟨b.c0, l⟩, sep, ⟨right, []⟩)

/-- `branch_apply_split`: absorb a child split at `childIdx` by inserting
the separator and the new right child as one entry, splitting this branch
too if it is full. `cap` is `branch_layout.cap`. -/
def branchApplySplit (cap : Nat) (b : Branch K C) (childIdx : Nat) (sep : K) (right : C) :
    BranchInsert K C :=
  if b.entries.length < cap then .noSplit ⟨b.c0, insertAt b.entries childIdx (sep, right)⟩
  else
    match branchInsertAndSplit b childIdx sep right with
    | (l, pk, r) => .split l pk r

/-- `grow_root`: the new root holds the old root and the split-off right
sibling around one separator. -/
def growRoot (oldRoot : C) (sep : K) (right : C) : Branch K C :=
  ⟨oldRoot, [(sep, right)]⟩

end Branch

end BPlusTree
