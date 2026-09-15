import BPlusTree.Model.Leaf
import BPlusTree.Model.Branch

/-!
# Tree-level model of `src/insert.rs`

`Node` ties the leaf and branch models together. `insertRec` mirrors the
Rust `insert_rec`: descend to the leaf, insert there, and hand any split
up for `branch_apply_split` to absorb; `insertTree` mirrors `insert` with
`grow_root` when the root itself splits.
-/

set_option linter.unusedSectionVars false

namespace BPlusTree

open Std

section Tree

variable {K V : Type}

/-- A node: a leaf's entries, or a branch's first child and
`(separator, child)` entries. -/
inductive Node (K V : Type) where
  | leaf (kvs : List (K × V))
  | branch (c0 : Node K V) (entries : List (K × Node K V))

/-- `InsertResult`. -/
inductive InsertRes (K V : Type) where
  | noSplit (n : Node K V) (old : Option V)
  | split (left : Node K V) (sep : K) (right : Node K V)

mutual
/-- Every key/value pair in the subtree, in key order once the tree is
well-formed: the leaves' entries left to right. -/
def Node.toList : Node K V → List (K × V)
  | .leaf kvs => kvs
  | .branch c0 entries => c0.toList ++ entriesToList entries

/-- The entries of a list of children, left to right. -/
def entriesToList : List (K × Node K V) → List (K × V)
  | [] => []
  | (_, c) :: rest => c.toList ++ entriesToList rest
end

/-- The entries of the children before the one `lastChild` picks. -/
def frontList (c : Node K V) : List (K × Node K V) → List (K × V)
  | [] => []
  | (_, ch) :: rest => c.toList ++ frontList ch rest

/-- The child that `child_for_key` picks, given the entries whose separator
is `≤ k`: the last of those entries' children, or `children[0]`. Generic
in the child type so the heap model can use it on node ids. -/
def lastChild {C : Type} (c : C) : List (K × C) → C
  | [] => c
  | (_, ch) :: rest => lastChild ch rest

/-- Replace the child `lastChild c A` picks. Returns the new `children[0]`
and the new prefix. -/
def replaceLast (c : Node K V) : List (K × Node K V) → Node K V → Node K V × List (K × Node K V)
  | [], c' => (c', [])
  | (s, ch) :: rest, c' =>
    (c, (s, (replaceLast ch rest c').1) :: (replaceLast ch rest c').2)

theorem sizeOf_lastChild {C : Type} [SizeOf C] (c : C) (A : List (K × C)) :
    sizeOf (lastChild c A) ≤ sizeOf c ∨ sizeOf (lastChild c A) < sizeOf A := by
  induction A generalizing c with
  | nil => left; simp [lastChild]
  | cons e rest ih =>
    obtain ⟨s, ch⟩ := e
    simp only [lastChild]
    rcases ih ch with h | h
    · right; simp; omega
    · right; simp; omega

theorem sizeOf_takeWhile_le {α : Type} [SizeOf α] (p : α → Bool) (l : List α) :
    sizeOf (l.takeWhile p) ≤ sizeOf l := by
  induction l with
  | nil => simp [List.takeWhile]
  | cons a l ih =>
    by_cases h : p a = true
    · rw [List.takeWhile_cons_of_pos h]; simp; omega
    · rw [List.takeWhile_cons_of_neg h]; simp; omega

end Tree

section Insert

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-- The separator test `child_for_key` routes on: the key goes right of
every separator that is `≤ k`. -/
def sepLE {C : Type} (k : K) (e : K × C) : Bool := decide (¬ k < e.1)

/-- `insert_rec`. `lc`/`bc` are the leaf and branch capacities. -/
def insertRec (lc bc : Nat) (k : K) (v : V) : Node K V → InsertRes K V
  | .leaf kvs =>
    match leafInsertOrSplit lc kvs k v with
    | .noSplit l old => .noSplit (.leaf l) old
    | .split l r sep => .split (.leaf l) sep (.leaf r)
  | .branch c0 entries =>
    -- `child_for_key`: the entries whose separator is `≤ k` come first.
    let A := entries.takeWhile (sepLE k)
    let B := entries.dropWhile (sepLE k)
    match insertRec lc bc k v (lastChild c0 A) with
    | .noSplit c' old =>
      match replaceLast c0 A c' with
      | (c0', A') => .noSplit (.branch c0' (A' ++ B)) old
    | .split cl sep cr =>
      -- The split child stays in its slot; the parent absorbs the new
      -- separator and right sibling at `child_idx`.
      match replaceLast c0 A cl with
      | (c0', A') =>
        match branchApplySplit bc ⟨c0', A' ++ B⟩ A.length sep cr with
        | .noSplit b => .noSplit (.branch b.c0 b.entries) none
        | .split l pk r => .split (.branch l.c0 l.entries) pk (.branch r.c0 r.entries)
termination_by n => sizeOf n
decreasing_by
  simp_wf
  have h1 := sizeOf_lastChild c0 (entries.takeWhile (sepLE k))
  have h2 := sizeOf_takeWhile_le (sepLE k) entries
  omega

/-- `insert`: the root absorbs the insert, or grows by one level. -/
def insertTree (lc bc : Nat) (root : Node K V) (k : K) (v : V) : Node K V × Option V :=
  match insertRec lc bc k v root with
  | .noSplit n old => (n, old)
  | .split l sep r =>
    match growRoot l sep r with
    | b => (.branch b.c0 b.entries, none)

end Insert

end BPlusTree
