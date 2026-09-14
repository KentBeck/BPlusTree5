/-!
# Leaf-level model of `src/insert.rs`

A leaf is its entries in slot order; the Rust `hdr.len` is the list length
and the `keys`/`vals` arrays are the two projections. Each definition below
names the Rust function it mirrors and keeps its arithmetic verbatim, so
the correspondence can be checked side by side.
-/

namespace BPlusTree

open Std

universe u
variable {α : Type u}

/-- `shift_right` then `write_kv_at`: open slot `i` and write `x` there. -/
def insertAt (l : List α) (i : Nat) (x : α) : List α :=
  l.take i ++ x :: l.drop i

/-- Overwrite slot `i`: the `Ok(idx)` arm of `leaf_insert_or_split`, which
writes only the value because the key there already equals the new key. -/
def replaceAt (l : List α) (i : Nat) (x : α) : List α :=
  l.take i ++ x :: l.drop (i + 1)

/-- The split arm of `leaf_insert_or_split`, arithmetic verbatim: decide
how many existing items stay left (`left_keep`), move the rest right, then
insert the new item into whichever side it sorts into. -/
def leafSplit (leaf : List α) (idx : Nat) (x : α) : List α × List α :=
  let totalItems := leaf.length + 1
  let leftCount := totalItems / 2
  let leftKeep := if idx < leftCount then leftCount - 1 else leftCount
  let kept := leaf.take leftKeep
  let moved := leaf.drop leftKeep
  if idx < leftCount then (insertAt kept idx x, moved)
  else (kept, insertAt moved (idx - leftKeep) x)

section Leaf

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-- A leaf's entries in slot order. -/
abbrev Leaf (K V : Type) := List (K × V)

/-- Strictly increasing keys: the "Leaf keys not strictly increasing" check
in `validate_leaf_key_order_and_bounds`. -/
def Sorted (l : List (K × V)) : Prop := l.Pairwise (fun a b => a.1 < b.1)

/-- The predicate a leaf slot satisfies when it sorts strictly before `k`. -/
def keyBelow (k : K) (e : K × V) : Bool := decide (e.1 < k)

/-- Slot of the first key that is `≥ k`. On a sorted leaf this is what
`binary_search_keys` returns: `Err(idx)` when the key at `idx` is not `k`,
`Ok(idx)` when it is. -/
def lowerBound (l : Leaf K V) (k : K) : Nat := (l.takeWhile (keyBelow k)).length

/-- `InsertResult` for a leaf: either the leaf absorbed the entry, or it
split and hands its parent the new right sibling and separator. -/
inductive LeafInsert (K V : Type) where
  | noSplit (leaf : Leaf K V) (old : Option V)
  | split (left right : Leaf K V) (sep : K)

/-- `leaf_insert_or_split`. `cap` is `leaf_layout.cap`. -/
def leafInsertOrSplit (cap : Nat) (leaf : Leaf K V) (k : K) (v : V) : LeafInsert K V :=
  let idx := lowerBound leaf k
  match leaf[idx]? with
  | some e =>
    if k < e.1 then insertOrSplit idx
    else .noSplit (replaceAt leaf idx (k, v)) (some e.2)
  | none => insertOrSplit idx
where
  insertOrSplit (idx : Nat) : LeafInsert K V :=
    if leaf.length < cap then .noSplit (insertAt leaf idx (k, v)) none
    else
      let (l, r) := leafSplit leaf idx (k, v)
      -- `key_clone_at(r.keys_ptr, 0)`; the right half is never empty
      -- (`leafSplit_right_ne_nil`), so the fallback is unreachable.
      .split l r (match r with | e :: _ => e.1 | [] => k)

end Leaf

end BPlusTree
