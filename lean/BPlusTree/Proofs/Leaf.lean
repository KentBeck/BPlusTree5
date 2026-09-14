import BPlusTree.Model.Leaf

/-!
# Proofs about the leaf-level model

The invariants `validate_leaf` checks (strictly increasing keys, fill
between `cap / 2` and `cap`) hold after `leaf_insert_or_split`, and a split
hands the parent a separator that correctly bounds both halves.
-/

set_option linter.unusedSectionVars false

namespace BPlusTree

open Std List

universe u
variable {α : Type u}

/-! ## List helpers -/

theorem mem_takeWhile_imp {p : α → Bool} {l : List α} {x : α}
    (h : x ∈ l.takeWhile p) : p x = true := by
  induction l with
  | nil => simp [List.takeWhile] at h
  | cons a l ih =>
    by_cases hp : p a = true
    · rw [List.takeWhile_cons_of_pos hp] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact hp
      · exact ih h
    · rw [List.takeWhile_cons_of_neg hp] at h
      simp at h

/-- `insertAt` on a list split at the insertion point. -/
theorem insertAt_append (A B : List α) (x : α) :
    insertAt (A ++ B) A.length x = A ++ x :: B := by
  simp [insertAt]

/-- `replaceAt` on a list split at the replaced slot. -/
theorem replaceAt_append (A B : List α) (x : α) :
    replaceAt (A ++ B) A.length x = A ++ x :: B.drop 1 := by
  simp only [replaceAt, List.take_append_length, List.drop_append]
  simp

theorem getElem?_append_length (A B : List α) : (A ++ B)[A.length]? = B.head? := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  cases B <;> rfl

/-! ## The split arithmetic

`leafSplit` computes with `left_keep` in two cases. Both cases produce the
same thing: insert the new item, then cut the result at `(len + 1) / 2`.
This is the theorem behind the comment "`left_count` is the final left
size" in `src/insert.rs`.
-/

theorem leafSplit_append (A B : List α) (x : α) :
    leafSplit (A ++ B) A.length x =
      ((A ++ x :: B).take ((A.length + B.length + 1) / 2),
       (A ++ x :: B).drop ((A.length + B.length + 1) / 2)) := by
  unfold leafSplit
  simp only [List.length_append]
  split
  · -- The new item lands on the left: `left_keep = left_count - 1`.
    rename_i hlt
    have hk : A.length ≤ (A.length + B.length + 1) / 2 - 1 := by omega
    have hk' : A.length ≤ (A.length + B.length + 1) / 2 := by omega
    have e1 : (A.length + B.length + 1) / 2 - A.length =
        ((A.length + B.length + 1) / 2 - 1 - A.length) + 1 := by omega
    simp only [List.take_append, List.drop_append, List.take_of_length_le hk,
      List.take_of_length_le hk', List.drop_of_length_le hk, List.drop_of_length_le hk',
      List.nil_append, insertAt_append]
    rw [e1, List.take_succ_cons, List.drop_succ_cons]
  · -- The new item lands on the right: `left_keep = left_count`.
    rename_i hge
    have e0 : (A.length + B.length + 1) / 2 - A.length = 0 := by omega
    have hl : (A.drop ((A.length + B.length + 1) / 2)).length =
        A.length - (A.length + B.length + 1) / 2 := by simp
    simp only [List.take_append, List.drop_append, e0, List.take_zero, List.drop_zero,
      List.append_nil]
    rw [← hl, insertAt_append]

theorem leafSplit_eq (leaf : List α) (idx : Nat) (x : α) (h : idx ≤ leaf.length) :
    leafSplit leaf idx x =
      ((insertAt leaf idx x).take ((leaf.length + 1) / 2),
       (insertAt leaf idx x).drop ((leaf.length + 1) / 2)) := by
  have hA : (leaf.take idx).length = idx := by simp; omega
  have this := leafSplit_append (leaf.take idx) (leaf.drop idx) x
  rw [List.take_append_drop, hA, List.length_drop] at this
  rw [this, insertAt]
  have e : idx + (leaf.length - idx) + 1 = leaf.length + 1 := by omega
  rw [e]

/-! ## Order facts about `lowerBound` -/

section Leaf

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

theorem Sorted.sublist {l l' : List (K × V)} (h : l' <+ l) (hs : Sorted l) :
    Sorted l' := List.Pairwise.sublist h hs

theorem lt_of_mem_takeWhile {l : Leaf K V} {k : K} {e : K × V}
    (h : e ∈ l.takeWhile (keyBelow k)) : e.1 < k := by
  have := mem_takeWhile_imp h
  simpa [keyBelow] using this

theorem not_lt_of_mem_dropWhile {l : Leaf K V} {k : K} (hs : Sorted l) {e : K × V}
    (h : e ∈ l.dropWhile (keyBelow k)) : ¬ e.1 < k := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [Sorted, List.pairwise_cons] at hs
    by_cases ha : keyBelow k a = true
    · rw [List.dropWhile_cons_of_pos ha] at h
      exact ih hs.2 h
    · rw [List.dropWhile_cons_of_neg ha] at h
      simp only [keyBelow, decide_eq_true_eq] at ha
      rcases List.mem_cons.mp h with rfl | h'
      · exact ha
      · intro hek
        exact ha (lt_trans (hs.1 e h') hek)

/-- Everything the proofs need about where `lowerBound` cuts a sorted leaf. -/
theorem lowerBound_spec (l : Leaf K V) (k : K) (hs : Sorted l) :
    ∃ A B : Leaf K V, l = A ++ B ∧ lowerBound l k = A.length ∧
      (∀ e ∈ A, e.1 < k) ∧ (∀ e ∈ B, ¬ e.1 < k) := by
  refine ⟨l.takeWhile (keyBelow k), l.dropWhile (keyBelow k),
    List.takeWhile_append_dropWhile.symm, rfl, ?_, ?_⟩
  · intro e he; exact lt_of_mem_takeWhile he
  · intro e he; exact not_lt_of_mem_dropWhile hs he

/-- Inserting `(k, v)` between the entries below `k` and those above it
keeps the leaf sorted. Both the `Err(idx)` insert and the `Ok(idx)`
overwrite reduce to this. -/
theorem sorted_append_cons {A B : Leaf K V} {k : K} {v : V}
    (hs : Sorted (A ++ B)) (hA : ∀ e ∈ A, e.1 < k) (hB : ∀ e ∈ B, k < e.1) :
    Sorted (A ++ (k, v) :: B) := by
  simp only [Sorted, List.pairwise_append, List.pairwise_cons] at hs ⊢
  refine ⟨hs.1, ⟨hB, hs.2.1⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hA a ha
  · exact hs.2.2 a ha b hb

/-- On a sorted tail whose head is above `k`, every entry is above `k`. -/
theorem forall_gt_of_head_gt {e : K × V} {B : Leaf K V} {k : K}
    (hs : Sorted (e :: B)) (he : k < e.1) : ∀ b ∈ e :: B, k < b.1 := by
  simp only [Sorted, List.pairwise_cons] at hs
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact he
  · exact lt_trans he (hs.1 b hb)

/-! ## `leaf_insert_or_split` -/

/-- The `NoSplit` outcome: the leaf stays sorted, stays within capacity,
and grows by exactly one entry when the key was absent or not at all when
it was present (in which case the returned value was the one stored). -/
theorem leafInsertOrSplit_noSplit {cap : Nat} {leaf leaf' : Leaf K V} {k : K} {v : V}
    {old : Option V} (hs : Sorted leaf) (hlen : leaf.length ≤ cap)
    (h : leafInsertOrSplit cap leaf k v = .noSplit leaf' old) :
    Sorted leaf' ∧ leaf'.length ≤ cap ∧
      (∀ o, old = some o → (k, o) ∈ leaf ∧ leaf'.length = leaf.length) ∧
      (old = none → (∀ e ∈ leaf, e.1 ≠ k) ∧ leaf'.length = leaf.length + 1) := by
  obtain ⟨A, B, rfl, hidx, hA, hB⟩ := lowerBound_spec leaf k hs
  simp only [leafInsertOrSplit, leafInsertOrSplit.insertOrSplit, hidx,
    getElem?_append_length] at h
  have hsB : Sorted B := hs.sublist (List.sublist_append_right A B)
  cases B with
  | nil =>
    -- Key absent, past the last entry.
    simp only [List.head?_nil] at h
    split at h
    · rename_i hlt
      cases h
      rw [insertAt_append]
      simp only [List.length_append, List.length_nil] at hlt
      refine ⟨sorted_append_cons hs hA (by simp), by simp; omega, ?_, ?_⟩
      · intro o ho; cases ho
      · intro _
        refine ⟨?_, by simp <;> omega⟩
        intro e he; exact ne_of_lt (hA e (by simpa using he))
    · cases h
  | cons e B =>
    simp only [List.head?_cons] at h
    split at h
    · -- `k < e.1`: key absent, insert at the cut.
      rename_i hke
      split at h
      · rename_i hlt
        cases h
        rw [insertAt_append]
        have hgt := forall_gt_of_head_gt hsB hke
        simp only [List.length_append, List.length_cons] at hlt
        refine ⟨sorted_append_cons hs hA hgt, by simp; omega, ?_, ?_⟩
        · intro o ho; cases ho
        · intro _
          refine ⟨?_, by simp <;> omega⟩
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact ne_of_lt (hA x hx)
          · exact (ne_of_lt (hgt x hx)).symm
      · cases h
    · -- `¬ k < e.1`, and `¬ e.1 < k` from the cut: the key is `e.1`.
      rename_i hke
      have hek : e.1 = k := by
        rcases lt_trichotomy e.1 k with h' | h' | h'
        · exact absurd h' (hB e (List.mem_cons_self))
        · exact h'
        · exact absurd h' hke
      cases h
      rw [replaceAt_append, List.drop_succ_cons, List.drop_zero]
      have hs' : Sorted (A ++ B) :=
        hs.sublist ((List.Sublist.refl A).append (List.sublist_cons_self e B))
      simp only [Sorted, List.pairwise_cons] at hsB
      refine ⟨?_, by simpa using hlen, ?_, ?_⟩
      · refine sorted_append_cons hs' hA ?_
        intro b hb; simpa [hek] using hsB.1 b hb
      · intro o ho
        cases ho
        have : (k, e.2) = e := by
          rcases e with ⟨ek, ev⟩; simp at hek; simp [hek]
        rw [this]; simp
      · intro hn; cases hn

/-- The `Split` outcome: both halves are sorted, meet the minimum fill for
every capacity from 1 up (`with_caps` enforces 4), and the separator (the right half's first key) sits
strictly above the left half and at or below the right half. Together the
halves hold exactly the old entries plus the new one. -/
theorem leafInsertOrSplit_split {cap : Nat} {leaf l r : Leaf K V} {k : K} {v : V}
    {sep : K} (hcap : 1 ≤ cap) (hs : Sorted leaf) (hlen : leaf.length ≤ cap)
    (h : leafInsertOrSplit cap leaf k v = .split l r sep) :
    Sorted l ∧ Sorted r ∧
      cap / 2 ≤ l.length ∧ l.length ≤ cap ∧ cap / 2 ≤ r.length ∧ r.length ≤ cap ∧
      (∀ e ∈ l, e.1 < sep) ∧ (∀ e ∈ r, sep ≤ e.1) ∧
      (∀ e ∈ leaf, e.1 ≠ k) ∧ l ++ r = insertAt leaf (lowerBound leaf k) (k, v) := by
  obtain ⟨A, B, rfl, hidx, hA, hB⟩ := lowerBound_spec leaf k hs
  simp only [leafInsertOrSplit, leafInsertOrSplit.insertOrSplit, hidx,
    getElem?_append_length] at h
  have hsB : Sorted B := hs.sublist (List.sublist_append_right A B)
  -- Reduce every arm to: the key is absent and the leaf is full.
  have key : (∀ b ∈ B, k < b.1) ∧ ¬ (A ++ B).length < cap ∧
      LeafInsert.split
        (leafSplit (A ++ B) A.length (k, v)).1 (leafSplit (A ++ B) A.length (k, v)).2
        (match (leafSplit (A ++ B) A.length (k, v)).2 with
          | e :: _ => e.1 | [] => k) = .split l r sep := by
    cases B with
    | nil =>
      simp only [List.head?_nil] at h
      split at h
      · cases h
      · rename_i hfull
        exact ⟨by simp, hfull, h⟩
    | cons e B =>
      simp only [List.head?_cons] at h
      split at h
      · rename_i hke
        split at h
        · cases h
        · rename_i hfull
          exact ⟨forall_gt_of_head_gt hsB hke, hfull, h⟩
      · cases h
  obtain ⟨hgt, hfull, h⟩ := key
  have hfull' : (A ++ B).length = cap := by omega
  have hsorted : Sorted (A ++ (k, v) :: B) := sorted_append_cons hs hA hgt
  rw [leafSplit_append] at h
  simp only [List.length_append] at hfull' h
  -- Name the cut point and the two halves.
  generalize hlc : (A.length + B.length + 1) / 2 = lc at h
  have hlc_le : lc ≤ A.length + B.length := by omega
  rcases hr : (A ++ (k, v) :: B).drop lc with _ | ⟨e, r'⟩
  · exfalso
    have := congrArg List.length hr
    simp at this; omega
  rw [hr] at h
  simp only [LeafInsert.split.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hsplit : (A ++ (k, v) :: B).take lc ++ e :: r' = A ++ (k, v) :: B := by
    rw [← hr, List.take_append_drop]
  have hs' : Sorted ((A ++ (k, v) :: B).take lc ++ e :: r') := by rw [hsplit]; exact hsorted
  simp only [Sorted, List.pairwise_append, List.pairwise_cons] at hs'
  have hr_len : r'.length + 1 + lc = A.length + B.length + 1 := by
    have := congrArg List.length hr
    simp only [List.length_drop, List.length_append, List.length_cons] at this
    omega
  have hlc2 : A.length + B.length ≤ 2 * lc ∧ 2 * lc ≤ A.length + B.length + 1 := by omega
  refine ⟨hs'.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.Pairwise.cons hs'.2.1.1 hs'.2.1.2
  · simp only [List.length_take, List.length_append, List.length_cons]; omega
  · simp only [List.length_take, List.length_append, List.length_cons]; omega
  · simp only [List.length_cons]; omega
  · simp only [List.length_cons]; omega
  · intro a ha; exact hs'.2.2 a ha e (List.mem_cons_self)
  · intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact le_refl _
    · exact le_of_lt (hs'.2.1.1 b hb)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ne_of_lt (hA x hx)
    · exact (ne_of_lt (hgt x hx)).symm
  · rw [hidx, insertAt_append]; exact hsplit

end Leaf

end BPlusTree
