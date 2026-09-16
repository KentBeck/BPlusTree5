import BPlusTree.Model.Branch
import BPlusTree.Proofs.Leaf

/-!
# Proofs about the branch-level model

`validate_branch` checks strictly increasing keys and fill between
`cap / 2` and `cap`. Both survive `branch_apply_split`, and a split hands
the parent a promoted key that strictly separates the two halves. The
entries are preserved as a sequence, which is what the tree-level bounds
argument will need.
-/

set_option linter.unusedSectionVars false

namespace BPlusTree

open Std List

universe u
variable {α : Type u}

/-! ## The fused cut -/

theorem cutInsert_append (A B : List α) (x : α) :
    cutInsert (A ++ B) A.length x =
      ((A ++ x :: B).take ((A.length + B.length + 1) / 2),
       (A ++ x :: B).drop ((A.length + B.length + 1) / 2)) := by
  unfold cutInsert
  simp only [List.length_append]
  split
  · -- The new entry lands on the left: `left_keep = left_count - 1`.
    rename_i hlt
    have hk : A.length ≤ (A.length + B.length + 1) / 2 - 1 := by omega
    have hk' : A.length ≤ (A.length + B.length + 1) / 2 := by omega
    have e1 : (A.length + B.length + 1) / 2 - A.length =
        ((A.length + B.length + 1) / 2 - 1 - A.length) + 1 := by omega
    simp only [List.take_append, List.drop_append, List.take_of_length_le hk,
      List.take_of_length_le hk', List.drop_of_length_le hk, List.drop_of_length_le hk',
      List.nil_append, insertAt_append]
    rw [e1, List.take_succ_cons, List.drop_succ_cons]
  · -- The new entry lands on the right: `left_keep = left_count`.
    rename_i hge
    have e0 : (A.length + B.length + 1) / 2 - A.length = 0 := by omega
    have hl : (A.drop ((A.length + B.length + 1) / 2)).length =
        A.length - (A.length + B.length + 1) / 2 := by simp
    simp only [List.take_append, List.drop_append, e0, List.take_zero, List.drop_zero,
      List.append_nil]
    rw [← hl, insertAt_append]

/-- The `left_keep` arithmetic equals "insert, then cut at `(len + 1) / 2`". -/
theorem cutInsert_eq (l : List α) (idx : Nat) (x : α) (h : idx ≤ l.length) :
    cutInsert l idx x =
      ((insertAt l idx x).take ((l.length + 1) / 2),
       (insertAt l idx x).drop ((l.length + 1) / 2)) := by
  have hA : (l.take idx).length = idx := by simp; omega
  have this := cutInsert_append (l.take idx) (l.drop idx) x
  rw [List.take_append_drop, hA, List.length_drop] at this
  rw [this, insertAt]
  have e : idx + (l.length - idx) + 1 = l.length + 1 := by omega
  rw [e]

section Branch

variable {K C : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-- The precondition a child split hands its parent: the separator sits
strictly between the entries on either side of the split child. -/
def SepFits (entries : List (K × C)) (childIdx : Nat) (sep : K) : Prop :=
  (∀ e ∈ entries.take childIdx, e.1 < sep) ∧ (∀ e ∈ entries.drop childIdx, sep < e.1)

/-- Inserting a fitting separator keeps the entry keys strictly increasing. -/
theorem sorted_insertAt_of_sepFits {entries : List (K × C)} {childIdx : Nat} {sep : K}
    {right : C} (hs : Sorted entries) (hfit : SepFits entries childIdx sep) :
    Sorted (insertAt entries childIdx (sep, right)) := by
  have hs' : Sorted (entries.take childIdx ++ entries.drop childIdx) := by
    rw [List.take_append_drop]; exact hs
  rw [insertAt]
  exact sorted_append_cons hs' hfit.1 hfit.2

/-- `NoSplit`: the branch keeps its first child, gains one entry at the
split child's slot, stays sorted, and stays within capacity. -/
theorem branchApplySplit_noSplit {cap : Nat} {b b' : Branch K C} {childIdx : Nat} {sep : K}
    {right : C} (hs : Sorted b.entries) (hfit : SepFits b.entries childIdx sep)
    (hidx : childIdx ≤ b.entries.length)
    (h : branchApplySplit cap b childIdx sep right = .noSplit b') :
    b'.c0 = b.c0 ∧ b'.entries = insertAt b.entries childIdx (sep, right) ∧
      Sorted b'.entries ∧ b'.entries.length = b.entries.length + 1 ∧ b'.entries.length ≤ cap := by
  unfold branchApplySplit at h
  split at h
  · rename_i hlt
    cases h
    refine ⟨rfl, rfl, sorted_insertAt_of_sepFits hs hfit, ?_, ?_⟩
    · simp [insertAt]; omega
    · simp [insertAt]; omega
  · split at h; cases h

/-- `Split`: both halves are sorted and hold between `cap / 2` and `cap`
entries for every capacity from 1 up (`with_caps` enforces 4); the
promoted key sits strictly above every left key and strictly below every
right key; the left half keeps the first child; and the two halves with
the promoted entry between them are exactly the old entries with the new
one inserted. -/
theorem branchApplySplit_split {cap : Nat} {b l r : Branch K C} {childIdx : Nat} {sep pk : K}
    {right : C} (hcap : 1 ≤ cap) (hs : Sorted b.entries) (hfit : SepFits b.entries childIdx sep)
    (hidx : childIdx ≤ b.entries.length) (hlen : b.entries.length ≤ cap)
    (h : branchApplySplit cap b childIdx sep right = .split l pk r) :
    Sorted l.entries ∧ Sorted r.entries ∧
      cap / 2 ≤ l.entries.length ∧ l.entries.length ≤ cap ∧
      cap / 2 ≤ r.entries.length ∧ r.entries.length ≤ cap ∧
      (∀ e ∈ l.entries, e.1 < pk) ∧ (∀ e ∈ r.entries, pk < e.1) ∧
      l.c0 = b.c0 ∧
      l.entries ++ (pk, r.c0) :: r.entries = insertAt b.entries childIdx (sep, right) := by
  unfold branchApplySplit at h
  split at h
  · cases h
  rename_i hfull
  have hfull' : b.entries.length = cap := by omega
  have hall : Sorted (insertAt b.entries childIdx (sep, right)) :=
    sorted_insertAt_of_sepFits hs hfit
  have hall_len : (insertAt b.entries childIdx (sep, right)).length = cap + 1 := by
    simp [insertAt]; omega
  unfold branchInsertAndSplit at h
  rw [cutInsert_eq _ _ _ hidx, hfull'] at h
  -- Name the inserted list and the cut point.
  generalize hall_eq : insertAt b.entries childIdx (sep, right) = all at h hall hall_len ⊢
  generalize hlc : (cap + 1) / 2 = lc at h
  have hlc_le : lc ≤ cap := by omega
  rcases hr : all.drop lc with _ | ⟨⟨qk, qc⟩, rest⟩
  · exfalso
    have := congrArg List.length hr
    simp at this; omega
  rw [hr] at h
  simp only [BranchInsert.split.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hcut : all.take lc ++ (qk, qc) :: rest = all := by rw [← hr, List.take_append_drop]
  have hs' : Sorted (all.take lc ++ (qk, qc) :: rest) := by rw [hcut]; exact hall
  simp only [Sorted, List.pairwise_append, List.pairwise_cons] at hs'
  have hrest : rest.length + 1 + lc = cap + 1 := by
    have := congrArg List.length hr
    simp only [List.length_drop, List.length_cons, hall_len] at this
    omega
  refine ⟨hs'.1, hs'.2.1.2, ?_, ?_, ?_, ?_, ?_, ?_, rfl, hcut⟩
  · show cap / 2 ≤ (all.take lc).length
    simp only [List.length_take, hall_len]; omega
  · show (all.take lc).length ≤ cap
    simp only [List.length_take, hall_len]; omega
  · show cap / 2 ≤ rest.length; omega
  · show rest.length ≤ cap; omega
  · intro e he; exact hs'.2.2 e he (qk, qc) List.mem_cons_self
  · intro e he; exact hs'.2.1.1 e he

/-- `grow_root`: the new root is a one-entry branch, so its keys are
trivially sorted and it is within any capacity from 1 up. The root is
exempt from the minimum fill. -/
theorem growRoot_spec (oldRoot : C) (sep : K) (right : C) :
    (growRoot oldRoot sep right).c0 = oldRoot ∧
      (growRoot oldRoot sep right).entries = [(sep, right)] ∧
      Sorted (growRoot oldRoot sep right).entries ∧
      (growRoot oldRoot sep right).entries.length = 1 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  simp [Sorted, growRoot]

end Branch

end BPlusTree
