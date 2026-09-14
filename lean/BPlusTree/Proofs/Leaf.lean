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

/-! ## The split

`split_leaf` cuts a full leaf at `(len + 1) / 2`, so both halves hold at
least `len / 2` items whichever half then receives the new one.
-/

theorem leafSplit_fst_length (leaf : List α) :
    (leafSplit leaf).1.length = (leaf.length + 1) / 2 := by
  simp [leafSplit]; omega

theorem leafSplit_snd_length (leaf : List α) :
    (leafSplit leaf).2.length = leaf.length - (leaf.length + 1) / 2 := by
  simp [leafSplit]

theorem leafSplit_append (leaf : List α) : (leafSplit leaf).1 ++ (leafSplit leaf).2 = leaf :=
  List.take_append_drop _ _

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

/-- The split arm never reports `NoSplit`. -/
theorem leafSplitInsert_ne_noSplit (leaf : Leaf K V) (idx : Nat) (k : K) (v : V)
    (leaf' : Leaf K V) (old : Option V) :
    leafSplitInsert leaf idx k v ≠ .noSplit leaf' old := by
  intro h
  simp only [leafSplitInsert] at h
  split at h <;> (try split at h) <;> cases h

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
    · exact absurd h (leafSplitInsert_ne_noSplit _ _ _ _ _ _)
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
      · exact absurd h (leafSplitInsert_ne_noSplit _ _ _ _ _ _)
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

/-- The `Split` outcome: both halves are sorted and hold between `cap / 2`
and `cap` entries for every capacity from 2 up (`with_caps` enforces 4);
the separator, the right half's first key, sits strictly above the left
half and at or below the right half; the key was absent; and the halves
concatenated are the old leaf with the new entry inserted at its sorted
position. -/
theorem leafInsertOrSplit_split {cap : Nat} {leaf l r : Leaf K V} {k : K} {v : V}
    {sep : K} (hcap : 2 ≤ cap) (hs : Sorted leaf) (hlen : leaf.length ≤ cap)
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
      leafSplitInsert (A ++ B) A.length k v = .split l r sep := by
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
  have habsent : ∀ e ∈ A ++ B, e.1 ≠ k := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ne_of_lt (hA x hx)
    · exact (ne_of_lt (hgt x hx)).symm
  have hfull' : A.length + B.length = cap := by simp at hfull hlen; omega
  have hsorted : Sorted (A ++ (k, v) :: B) := sorted_append_cons hs hA hgt
  simp only [leafSplitInsert, leafSplit, List.length_append] at h
  -- Name the cut point; the right half is nonempty because `cap ≥ 2`.
  generalize hlc : (A.length + B.length + 1) / 2 = lc at h
  have hlc_lt : lc < A.length + B.length := by omega
  rcases hr : (A ++ B).drop lc with _ | ⟨e, r'⟩
  · exfalso
    have := congrArg List.length hr
    simp at this; omega
  rw [hr] at h
  simp only [] at h
  -- The old leaf, cut at `lc`.
  have hcut : (A ++ B).take lc ++ e :: r' = A ++ B := by
    rw [← hr, List.take_append_drop]
  have hs' : Sorted ((A ++ B).take lc ++ e :: r') := by rw [hcut]; exact hs
  simp only [Sorted, List.pairwise_append, List.pairwise_cons] at hs'
  have hget : (A ++ B)[lc]? = some e := by
    have := congrArg (fun l => l[0]?) hr
    simpa [List.getElem?_drop] using this
  have hr_len : r'.length + 1 + lc = A.length + B.length := by
    have := congrArg List.length hr
    simp only [List.length_drop, List.length_append, List.length_cons] at this
    omega
  have hlc2 : A.length + B.length ≤ 2 * lc ∧ 2 * lc ≤ A.length + B.length + 1 := by omega
  split at h
  · -- `k < sep`: the new entry goes left, so the cut sits at or past `A`.
    rename_i hke
    simp only [LeafInsert.split.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hAl : A.length ≤ lc := by
      by_cases hAl : A.length ≤ lc
      · exact hAl
      · exfalso
        have hlt := Nat.lt_of_not_le hAl
        rw [List.getElem?_append_left hlt] at hget
        exact lt_irrefl (lt_trans (hA e (List.mem_of_getElem? hget)) hke)
    have hsub : lc - A.length ≤ B.length := by omega
    have htake : (A ++ B).take lc = A ++ B.take (lc - A.length) := by
      rw [List.take_append, List.take_of_length_le hAl]
    have hdrop : (A ++ B).drop lc = B.drop (lc - A.length) := by
      rw [List.drop_append, List.drop_of_length_le hAl, List.nil_append]
    rw [htake, insertAt_append]
    have hleft : Sorted (A ++ (k, v) :: B.take (lc - A.length)) := by
      refine sorted_append_cons ?_ hA ?_
      · rw [← htake]; exact hs'.1
      · intro b hb; exact hgt b (List.mem_of_mem_take hb)
    refine ⟨hleft, List.Pairwise.cons hs'.2.1.1 hs'.2.1.2, ?_, ?_, ?_, ?_, ?_, ?_, habsent, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_take]; omega
    · simp only [List.length_append, List.length_cons, List.length_take]; omega
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hs'.2.2 a (by rw [htake]; exact List.mem_append_left _ ha) e List.mem_cons_self
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact hke
        · exact hs'.2.2 a (by rw [htake]; exact List.mem_append_right _ ha) e List.mem_cons_self
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_refl _
      · exact le_of_lt (hs'.2.1.1 b hb)
    · rw [← hr, hdrop, List.append_assoc, List.cons_append, List.take_append_drop, hidx,
        insertAt_append]
  · -- `¬ k < sep`: the new entry goes right, so the cut sits inside `A`.
    rename_i hke
    simp only [LeafInsert.split.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hek : e.1 < k := by
      rcases lt_trichotomy e.1 k with h' | h' | h'
      · exact h'
      · exact absurd h' (habsent e (List.mem_of_getElem? hget))
      · exact absurd h' hke
    have hlA : lc < A.length := by
      by_cases hlA : lc < A.length
      · exact hlA
      · exfalso
        have hge := Nat.le_of_not_lt hlA
        rw [List.getElem?_append_right hge] at hget
        exact lt_irrefl (lt_trans (hgt e (List.mem_of_getElem? hget)) hek)
    have htake : (A ++ B).take lc = A.take lc := by
      rw [List.take_append_of_le_length (Nat.le_of_lt hlA)]
    have hdrop : (A ++ B).drop lc = A.drop lc ++ B := by
      rw [List.drop_append_of_le_length (Nat.le_of_lt hlA)]
    have hlenA : (A.take lc).length = lc := by simp; omega
    have hidx' : A.length - (A.take lc).length = (A.drop lc).length := by simp; omega
    rw [htake, ← hr, hdrop, hidx', insertAt_append]
    have hright : Sorted (A.drop lc ++ (k, v) :: B) := by
      refine sorted_append_cons ?_ ?_ hgt
      · exact hs.sublist ((List.drop_sublist lc A).append (List.Sublist.refl B))
      · intro a ha; exact hA a (List.mem_of_mem_drop ha)
    -- Every entry of the old right half is at or above `e`, its head.
    have hge_e : ∀ x ∈ A.drop lc ++ B, e.1 ≤ x.1 := by
      intro x hx
      have hx' : x ∈ e :: r' := by rw [← hr, hdrop]; exact hx
      rcases List.mem_cons.mp hx' with rfl | hx'
      · exact le_refl _
      · exact le_of_lt (hs'.2.1.1 x hx')
    refine ⟨?_, hright, ?_, ?_, ?_, ?_, ?_, ?_, habsent, ?_⟩
    · rw [← htake]; exact hs'.1
    · simp only [List.length_take]; omega
    · simp only [List.length_take]; omega
    · simp only [List.length_append, List.length_cons, List.length_drop]; omega
    · simp only [List.length_append, List.length_cons, List.length_drop]; omega
    · intro a ha
      exact hs'.2.2 a (by rw [htake]; exact ha) e List.mem_cons_self
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact hge_e b (List.mem_append_left _ hb)
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact le_of_lt hek
        · exact hge_e b (List.mem_append_right _ hb)
    · rw [← List.append_assoc, List.take_append_drop, hidx, insertAt_append]

end Leaf

end BPlusTree
