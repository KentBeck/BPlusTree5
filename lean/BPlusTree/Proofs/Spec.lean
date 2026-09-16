import BPlusTree.Model.Spec
import BPlusTree.Proofs.Leaf

/-!
# Facts about `insertSorted`

How `insertSorted` behaves on a sorted list cut at the key: it lands
between the entries below the key and those above it, replacing an entry
with the same key when there is one, and it passes through entries known
to sort entirely before or after the key.
-/

set_option linter.unusedSectionVars false

namespace BPlusTree

open Std

section Spec

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K] [DecidableLT K]

theorem insertSorted_append_left {k : K} {v : V} (L M : List (K × V))
    (hL : ∀ e ∈ L, e.1 < k) : insertSorted k v (L ++ M) = L ++ insertSorted k v M := by
  induction L with
  | nil => rfl
  | cons e rest ih =>
    have he : e.1 < k := hL e List.mem_cons_self
    simp only [List.cons_append, insertSorted, he, if_true]
    rw [ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))]

theorem insertSorted_append_right {k : K} {v : V} (M R : List (K × V))
    (hR : ∀ e ∈ R, k < e.1) : insertSorted k v (M ++ R) = insertSorted k v M ++ R := by
  induction M with
  | nil =>
    cases R with
    | nil => rfl
    | cons e rest =>
      have he : k < e.1 := hR e List.mem_cons_self
      have hne : ¬ e.1 < k := fun h => lt_irrefl (lt_trans h he)
      simp [insertSorted, hne, he]
  | cons e rest ih =>
    simp only [List.cons_append, insertSorted]
    split
    · rw [ih, List.cons_append]
    · split <;> rfl

/-- Absent key: the pair lands at the cut. -/
theorem insertSorted_absent {k : K} {v : V} (A B : List (K × V))
    (hA : ∀ e ∈ A, e.1 < k) (hB : ∀ e ∈ B, k < e.1) :
    insertSorted k v (A ++ B) = A ++ (k, v) :: B := by
  rw [insertSorted_append_left A B hA]
  cases B with
  | nil => rfl
  | cons e rest =>
    have he : k < e.1 := hB e List.mem_cons_self
    have hne : ¬ e.1 < k := fun h => lt_irrefl (lt_trans h he)
    simp [insertSorted, hne, he]

/-- Present key: the pair replaces the entry at the cut. -/
theorem insertSorted_present {k : K} {v : V} (A : List (K × V)) (e : K × V) (B : List (K × V))
    (hA : ∀ a ∈ A, a.1 < k) (he : e.1 = k) :
    insertSorted k v (A ++ e :: B) = A ++ (k, v) :: B := by
  rw [insertSorted_append_left A _ hA]
  have h1 : ¬ e.1 < k := by rw [he]; exact lt_irrefl
  have h2 : ¬ k < e.1 := by rw [he]; exact lt_irrefl
  simp [insertSorted, h1, h2]

/-- `leaf_insert_or_split`'s `NoSplit` leaf is `insertSorted`. -/
theorem leafInsertOrSplit_noSplit_eq {cap : Nat} {leaf leaf' : Leaf K V} {k : K} {v : V}
    {old : Option V} (hs : Sorted leaf)
    (h : leafInsertOrSplit cap leaf k v = .noSplit leaf' old) :
    leaf' = insertSorted k v leaf := by
  obtain ⟨A, B, rfl, hidx, hA, hB⟩ := lowerBound_spec leaf k hs
  simp only [leafInsertOrSplit, leafInsertOrSplit.insertOrSplit, hidx,
    getElem?_append_length] at h
  have hsB : Sorted B := hs.sublist (List.sublist_append_right A B)
  cases B with
  | nil =>
    simp only [List.head?_nil] at h
    split at h
    · cases h
      rw [insertAt_append, insertSorted_absent A [] hA (by simp)]
    · exact absurd h (leafSplitInsert_ne_noSplit _ _ _ _ _ _)
  | cons e B =>
    simp only [List.head?_cons] at h
    split at h
    · rename_i hke
      split at h
      · cases h
        rw [insertAt_append, insertSorted_absent A (e :: B) hA (forall_gt_of_head_gt hsB hke)]
      · exact absurd h (leafSplitInsert_ne_noSplit _ _ _ _ _ _)
    · rename_i hke
      have hek : e.1 = k := by
        rcases lt_trichotomy e.1 k with h' | h' | h'
        · exact absurd h' (hB e List.mem_cons_self)
        · exact h'
        · exact absurd h' hke
      cases h
      rw [replaceAt_append, List.drop_succ_cons, List.drop_zero,
        insertSorted_present A e B hA hek]

/-- `leaf_insert_or_split`'s `Split` halves concatenate to `insertSorted`. -/
theorem leafInsertOrSplit_split_eq {cap : Nat} {leaf l r : Leaf K V} {k : K} {v : V}
    {sep : K} (hcap : 2 ≤ cap) (hs : Sorted leaf) (hlen : leaf.length ≤ cap)
    (h : leafInsertOrSplit cap leaf k v = .split l r sep) :
    l ++ r = insertSorted k v leaf := by
  obtain ⟨_, _, _, _, _, _, _, _, habs, heq⟩ := leafInsertOrSplit_split hcap hs hlen h
  rw [heq]
  obtain ⟨A, B, hAB, hidx, hA, hB⟩ := lowerBound_spec leaf k hs
  rw [hidx, hAB, insertAt_append]
  refine (insertSorted_absent A B hA ?_).symm
  intro e he
  rcases lt_trichotomy k e.1 with h' | h' | h'
  · exact h'
  · exact absurd h'.symm (habs e (by rw [hAB]; exact List.mem_append_right _ he))
  · exact absurd h' (hB e he)

/-! ## `eraseSorted` -/

theorem eraseIdx_window {α : Type} (cs1 : List α) (a : α) (cs2 : List α) :
    (cs1 ++ a :: cs2).eraseIdx cs1.length = cs1 ++ cs2 := by
  rw [List.eraseIdx_append_of_length_le (Nat.le_refl _), Nat.sub_self]; rfl

theorem eraseSorted_append_left {k : K} (L M : List (K × V))
    (hL : ∀ e ∈ L, e.1 < k) : eraseSorted k (L ++ M) = L ++ eraseSorted k M := by
  induction L with
  | nil => rfl
  | cons e rest ih =>
    have he : e.1 < k := hL e List.mem_cons_self
    simp only [List.cons_append, eraseSorted, he, if_true]
    rw [ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))]

theorem eraseSorted_append_right {k : K} (M R : List (K × V))
    (hR : ∀ e ∈ R, k < e.1) : eraseSorted k (M ++ R) = eraseSorted k M ++ R := by
  induction M with
  | nil =>
    cases R with
    | nil => rfl
    | cons e rest =>
      have he : k < e.1 := hR e List.mem_cons_self
      have hne : ¬ e.1 < k := fun h => lt_irrefl (lt_trans h he)
      simp [eraseSorted, hne, he]
  | cons e rest ih =>
    simp only [List.cons_append, eraseSorted]
    split
    · rw [ih, List.cons_append]
    · split <;> rfl

/-- Present key: the entry at the cut is dropped. -/
theorem eraseSorted_present {k : K} (A : List (K × V)) (e : K × V) (B : List (K × V))
    (hA : ∀ a ∈ A, a.1 < k) (he : e.1 = k) :
    eraseSorted k (A ++ e :: B) = A ++ B := by
  rw [eraseSorted_append_left A _ hA]
  have h1 : ¬ e.1 < k := by rw [he]; exact lt_irrefl
  have h2 : ¬ k < e.1 := by rw [he]; exact lt_irrefl
  simp [eraseSorted, h1, h2]

end Spec

end BPlusTree
