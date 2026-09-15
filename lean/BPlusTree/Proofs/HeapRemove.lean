import BPlusTree.Proofs.Heap
import BPlusTree.Proofs.Delete

/-!
# The heap model: remove

On top of `Proofs/Heap.lean`: the primitives remove uses (`unlinkLeaf`,
the two emptied-node frees, `emptyBranch`), erasing a leaf from the
chain, the bridge from a branch record to the tree model's array view
(`mkBranch`), the plan equivalence, the six repairs, `fixBranchChildH`,
`removeRecH` and `removeH`.
-/

namespace BPlusTree

open Std

set_option linter.unusedSectionVars false

section HeapRemove

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-! ## Primitives -/

namespace Heap

theorem getBranch_eq {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    (hg : h.get id = some (.branch c0 es)) : h.getBranch id = some (c0, es) := by
  simp [getBranch, hg]

theorem setBranch_spec {h : Heap K V} {id : NodeId} (ha : (h.get id).isSome) (c0 : NodeId)
    (es : List (K × NodeId)) :
    ∃ h', h.setBranch id c0 es = some h' ∧ h'.get id = some (.branch c0 es) ∧
      (∀ i, i ≠ id → h'.get i = h.get i) ∧ h'.fresh = h.fresh := by
  obtain ⟨h', hw⟩ := write_some (h := h) (id := id) (r := .branch c0 es) ha
  exact ⟨h', hw, get_write_self hw, fun i hi => get_write_other hw hi, fresh_write hw⟩

end Heap

theorem emptyBranch_spec {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    (hg : h.get id = some (.branch c0 es)) :
    ∃ h', emptyBranch h id = some h' ∧ h'.get id = some (.branch c0 []) ∧
      (∀ i, i ≠ id → h'.get i = h.get i) ∧ h'.fresh = h.fresh := by
  simp only [emptyBranch, Heap.getBranch_eq hg, Option.bind_eq_bind, Option.bind_some]
  exact Heap.setBranch_spec (by simp [hg]) c0 []

theorem freeEmptiedBranch_spec {h : Heap K V} {id c0 : NodeId}
    (hg : h.get id = some (.branch c0 [])) :
    ∃ h', freeEmptiedBranch h id = some h' ∧ h'.get id = none ∧
      (∀ i, i ≠ id → h'.get i = h.get i) ∧ h'.fresh = h.fresh := by
  simp only [freeEmptiedBranch, Heap.getBranch_eq hg, Option.bind_eq_bind, Option.bind_some,
    List.isEmpty_nil, if_true]
  obtain ⟨h', hf⟩ := Heap.free_some (h := h) (id := id) (by simp [hg])
  exact ⟨h', hf, Heap.get_free_self hf, fun i hi => Heap.get_free_other hf hi, Heap.fresh_free hf⟩

/-- `unlinkLeaf` on a leaf `b` whose predecessor is the leaf `a`: `a`'s
`next` skips to `b`'s successor, that successor's `prev` comes back to
`a`, `b`'s own links are cleared, nothing else changes. -/
theorem unlinkLeaf_spec {h : Heap K V} {a b : NodeId} {L R : Leaf K V} {pa nb : Option NodeId}
    (hb : h.get b = some (.leaf R (some a) nb)) (ha : h.get a = some (.leaf L pa (some b)))
    (hab : a ≠ b)
    (ho : ∀ o, nb = some o → o ≠ a ∧ o ≠ b ∧ ∃ O po no, h.get o = some (.leaf O po no)) :
    ∃ h', unlinkLeaf h b = some h' ∧ h'.get a = some (.leaf L pa nb) ∧
      h'.get b = some (.leaf R none none) ∧
      (∀ o O po no, nb = some o → h.get o = some (.leaf O po no) →
        h'.get o = some (.leaf O (some a) no)) ∧
      (∀ i, i ≠ a → i ≠ b → nb ≠ some i → h'.get i = h.get i) ∧ h'.fresh = h.fresh := by
  simp only [unlinkLeaf, Heap.getLeaf_eq hb, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨h1, hs1, hg1, ho1, hf1⟩ := Heap.setNext_spec ha nb
  rw [hs1]; try dsimp only
  have hb1 : h1.get b = some (.leaf R (some a) nb) := by rw [ho1 b (Ne.symm hab)]; exact hb
  rcases nb with _ | o
  · simp only [Option.bind_some]
    obtain ⟨h2, hs2, hg2, ho2, hf2⟩ := Heap.setNext_spec hb1 none
    rw [hs2]; simp only [Option.bind_some]
    obtain ⟨h3, hs3, hg3, ho3, hf3⟩ := Heap.setPrev_spec hg2 none
    refine ⟨h3, hs3, ?_, hg3, (fun o _ _ _ h => by cases h), ?_, by rw [hf3, hf2, hf1]⟩
    · rw [ho3 a hab, ho2 a hab]; exact hg1
    · intro i hia hib _
      rw [ho3 i hib, ho2 i hib, ho1 i hia]
  · simp only [Option.bind_some]
    obtain ⟨hoa, hob, O, po, no, hgo⟩ := ho o rfl
    have hgo1 : h1.get o = some (.leaf O po no) := by rw [ho1 o hoa]; exact hgo
    obtain ⟨h2, hs2, hg2, ho2, hf2⟩ := Heap.setPrev_spec hgo1 (some a)
    rw [hs2]; simp only [Option.bind_some]
    have hb2 : h2.get b = some (.leaf R (some a) (some o)) := by rw [ho2 b (Ne.symm hob)]; exact hb1
    obtain ⟨h3, hs3, hg3, ho3, hf3⟩ := Heap.setNext_spec hb2 none
    rw [hs3]; simp only [Option.bind_some]
    obtain ⟨h4, hs4, hg4, ho4, hf4⟩ := Heap.setPrev_spec hg3 none
    refine ⟨h4, hs4, ?_, hg4, ?_, ?_, by rw [hf4, hf3, hf2, hf1]⟩
    · rw [ho4 a hab, ho3 a hab, ho2 a (Ne.symm hoa)]; exact hg1
    · intro o' O' po' no' ho' hgo'
      cases ho'
      rw [hgo] at hgo'
      cases hgo'
      rw [ho4 _ hob, ho3 _ hob]
      exact hg2
    · intro i hia hib hio
      have hio' : i ≠ o := fun heq => hio (by rw [heq])
      rw [ho4 i hib, ho3 i hib, ho2 i hio', ho1 i hia]

/-- `freeEmptiedLeaf` on an emptied leaf `b` after the leaf `a`: unlink,
then free. -/
theorem freeEmptiedLeaf_spec {h : Heap K V} {a b : NodeId} {L : Leaf K V} {pa nb : Option NodeId}
    (hb : h.get b = some (.leaf [] (some a) nb)) (ha : h.get a = some (.leaf L pa (some b)))
    (hab : a ≠ b)
    (ho : ∀ o, nb = some o → o ≠ a ∧ o ≠ b ∧ ∃ O po no, h.get o = some (.leaf O po no)) :
    ∃ h', freeEmptiedLeaf h b = some h' ∧ h'.get a = some (.leaf L pa nb) ∧ h'.get b = none ∧
      (∀ o O po no, nb = some o → h.get o = some (.leaf O po no) →
        h'.get o = some (.leaf O (some a) no)) ∧
      (∀ i, i ≠ a → i ≠ b → nb ≠ some i → h'.get i = h.get i) ∧ h'.fresh = h.fresh := by
  simp only [freeEmptiedLeaf, Heap.getLeaf_eq hb, Option.bind_eq_bind, Option.bind_some,
    List.isEmpty_nil, if_true]
  obtain ⟨h1, hu, hga, hgb, hgo, hother, hf1⟩ := unlinkLeaf_spec hb ha hab ho
  rw [hu]; simp only [Option.bind_some]
  obtain ⟨h2, hf⟩ := Heap.free_some (h := h1) (id := b) (by simp [hgb])
  refine ⟨h2, hf, ?_, Heap.get_free_self hf, ?_, ?_, by rw [Heap.fresh_free hf, hf1]⟩
  · rw [Heap.get_free_other hf hab]; exact hga
  · intro o O po no hno hgo'
    have hob : o ≠ b := (ho o hno).2.1
    rw [Heap.get_free_other hf hob]; exact hgo o O po no hno hgo'
  · intro i hia hib hio
    rw [Heap.get_free_other hf hib]; exact hother i hia hib hio

/-! ## Erasing a leaf from the chain -/

/-- If the chain's records are unchanged except that its first leaf's
`prev` moved, it is still a chain from the new `prev`. -/
theorem linked_replace_prev {h h' : Heap K V} {p p' next : Option NodeId} {l : List NodeId}
    (hl : Linked h p l next)
    (hhead : ∀ a rest, l = a :: rest → ∀ O n, h.get a = some (.leaf O p n) →
      h'.get a = some (.leaf O p' n))
    (hrest : ∀ a rest, l = a :: rest → ∀ i ∈ rest, h'.get i = h.get i) :
    Linked h' p' l next := by
  cases l with
  | nil => trivial
  | cons a rest =>
    obtain ⟨⟨O, hga⟩, hr⟩ := hl
    exact ⟨⟨O, hhead a rest rfl O _ hga⟩, linked_congr (fun i hi => hrest a rest rfl i hi) hr⟩

/-- Removing the leaf `b` after `a` from a chain: `a`'s `next` skips to
`b`'s successor, whose `prev` comes back to `a`. -/
theorem linked_erase {h h' : Heap K V} {prev next : Option NodeId} {L1 L2 : List NodeId}
    {a b : NodeId} (hl : Linked h prev (L1 ++ a :: b :: L2) next)
    (ha : ∀ La pa, h.get a = some (.leaf La pa (some b)) →
      ∃ La', h'.get a = some (.leaf La' pa (L2.head?.or next)))
    (hL1 : ∀ i ∈ L1, h'.get i = h.get i)
    (hhead : ∀ o rest, L2 = o :: rest → ∀ O n, h.get o = some (.leaf O (some b) n) →
      h'.get o = some (.leaf O (some a) n))
    (hrest : ∀ o rest, L2 = o :: rest → ∀ i ∈ rest, h'.get i = h.get i) :
    Linked h' prev (L1 ++ a :: L2) next := by
  rw [linked_append] at hl ⊢
  obtain ⟨hl1, hl2⟩ := hl
  refine ⟨linked_congr hL1 hl1, ?_⟩
  obtain ⟨⟨La, hga⟩, ⟨Rb, hgb⟩, hl3⟩ := hl2
  simp only [List.head?_cons, Option.some_or] at hga hgb
  obtain ⟨La', hga'⟩ := ha La _ hga
  refine ⟨⟨La', hga'⟩, ?_⟩
  exact linked_replace_prev hl3 hhead hrest

/-! ## The array view of a branch record -/

theorem zip_map_fst_map_snd {C : Type} (f : NodeId → C) (es : List (K × NodeId)) :
    (es.map Prod.fst).zip ((es.map Prod.snd).map f) = es.map fun e => (e.1, f e.2) := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    simp only [List.map_cons, List.zip_cons_cons]
    rw [ih]

/-- A branch record abstracts to `mkBranch` of its key array and the
abstraction of its child-id array. -/
theorem absNode_branch_mk {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    (hg : h.get id = some (.branch c0 es))
    (hall : ∀ c ∈ c0 :: es.map (·.2), ∃ t, absNode d h c = some t) :
    absNode (d + 1) h id =
      some (mkBranch (es.map Prod.fst) ((c0 :: es.map (·.2)).map (absF d h))) := by
  rw [absNode_branch hg]
  obtain ⟨t0, ht0⟩ := hall c0 List.mem_cons_self
  rw [ht0]
  simp only [Option.bind_some]
  rw [absEntries_of_all_some (fun e he =>
    hall e.2 (List.mem_cons_of_mem _ (List.mem_map_of_mem he)))]
  simp only [Option.bind_some, List.map_cons, mkBranch, zip_map_fst_map_snd, absF_of_some ht0]

theorem nodeLen_of_abs {d : Nat} {h : Heap K V} {c : NodeId} {t : Node K V}
    (habs : absNode d h c = some t) : h.nodeLen c = some t.len := by
  cases d with
  | zero => simp [absNode] at habs
  | succ d =>
    rcases hg : h.get c with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
    · simp [absNode, hg] at habs
    · rw [absNode_leaf hg] at habs; cases habs; simp [Heap.nodeLen, hg, Node.len]
    · rw [absNode_branch hg] at habs
      cases h0 : absNode d h c0 <;> rw [h0] at habs
      · cases habs
      · cases he : absNode.absEntries d h es <;> rw [he] at habs
        · cases habs
        · simp only [Option.bind_some, Option.some.injEq] at habs
          subst habs
          simp [Heap.nodeLen, hg, Node.len, absEntries_length he]

theorem childLenH_eq {d : Nat} {h : Heap K V} {cs : List NodeId}
    (hall : ∀ c ∈ cs, ∃ t, absNode d h c = some t) {j : Nat} (hj : j < cs.length) :
    childLenH h cs j = some (childLen (cs.map (absF d h)) j) := by
  obtain ⟨c, hc⟩ : ∃ c, cs[j]? = some c := by
    rw [List.getElem?_eq_getElem hj]; exact ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := hall c (List.mem_of_getElem? hc)
  simp only [childLenH, hc, Option.bind_eq_bind, Option.bind_some, childLen, List.getElem?_map,
    Option.map_some, nodeLen_of_abs ht, absF_of_some ht]

/-- `plan_rebalance` on the heap reads the same lengths the tree model
computes, so it makes the same choice. -/
theorem planRebalanceH_eq {d : Nat} {h : Heap K V} {cs : List NodeId}
    (hall : ∀ c ∈ cs, ∃ t, absNode d h c = some t) {idx len min : Nat}
    (hidx : idx ≤ len) (hlen : cs.length = len + 1) :
    planRebalanceH h cs idx len min = some (planRebalance (cs.map (absF d h)) idx len min) := by
  have hcl : idx > 0 → childLenH h cs (idx - 1) = some (childLen (cs.map (absF d h)) (idx - 1)) :=
    fun _ => childLenH_eq hall (by omega)
  have hcr : idx < len → childLenH h cs (idx + 1) = some (childLen (cs.map (absF d h)) (idx + 1)) :=
    fun _ => childLenH_eq hall (by omega)
  simp only [planRebalanceH, planRebalance]
  by_cases hL : idx > 0 <;> by_cases hR : idx < len <;> simp [hL, hR, hcl, hcr]
  · by_cases h1 : min < childLen (cs.map (absF d h)) (idx - 1) <;>
      by_cases h2 : min < childLen (cs.map (absF d h)) (idx + 1) <;> simp [h1, h2]
  · by_cases h1 : min < childLen (cs.map (absF d h)) (idx - 1) <;> simp [h1]
  · by_cases h2 : min < childLen (cs.map (absF d h)) (idx + 1) <;> simp [h2]

/-! ### Entry-view edits as array-view edits -/

theorem map_fst_setSep (es : List (K × NodeId)) (i : Nat) (s : K) (hi : i < es.length) :
    (setSep es i s).map Prod.fst = (es.map Prod.fst).set i s := by
  obtain ⟨e, he⟩ : ∃ e, es[i]? = some e := by
    rw [List.getElem?_eq_getElem hi]; exact ⟨_, rfl⟩
  simp [setSep, he, List.map_set]

theorem map_snd_setSep (es : List (K × NodeId)) (i : Nat) (s : K) :
    (setSep es i s).map Prod.snd = es.map Prod.snd := by
  induction es generalizing i with
  | nil => simp [setSep]
  | cons e rest ih =>
    obtain ⟨s', c⟩ := e
    cases i with
    | zero => simp [setSep]
    | succ i =>
      simp only [setSep, List.getElem?_cons_succ]
      cases he : rest[i]? with
      | none => rfl
      | some e' =>
        obtain ⟨s'', c'⟩ := e'
        simp only [List.set_cons_succ, List.map_cons]
        have := ih i
        simp only [setSep, he] at this
        rw [this]

theorem length_setSep (es : List (K × NodeId)) (i : Nat) (s : K) :
    (setSep es i s).length = es.length := by
  simp only [setSep]; cases es[i]? <;> simp

theorem map_eraseIdx {α β : Type} (f : α → β) (l : List α) (i : Nat) :
    (l.eraseIdx i).map f = (l.map f).eraseIdx i := by
  induction l generalizing i with
  | nil => simp
  | cons a t ih =>
    cases i with
    | zero => simp
    | succ i => simp [ih]

theorem cons_map_snd_eraseIdx (c0 : NodeId) (es : List (K × NodeId)) (i : Nat) :
    c0 :: (es.eraseIdx i).map Prod.snd = (c0 :: es.map Prod.snd).eraseIdx (i + 1) := by
  rw [List.eraseIdx_cons_succ, map_eraseIdx]

/-- `l[i]? = some a` splits `l` around slot `i`. -/
theorem split_at_getElem? {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    ∃ F B, l = F ++ a :: B ∧ F.length = i := by
  induction l generalizing i with
  | nil => simp at h
  | cons x t ih =>
    cases i with
    | zero => simp at h; subst h; exact ⟨[], t, rfl, rfl⟩
    | succ i =>
      simp at h
      obtain ⟨F, B, rfl, hF⟩ := ih h
      exact ⟨x :: F, B, rfl, by simp [hF]⟩

/-! ## The six repairs, record by record -/

theorem childAt_some {c0 : NodeId} {es : List (K × NodeId)} {i : Nat} {a : NodeId}
    (h : childAt c0 es i = some a) : (c0 :: es.map (·.2))[i]? = some a := h

/-- `rotate_leaf_right`: the left leaf loses its last item to the right
leaf's front, the separator becomes that item's key. -/
theorem rotateLeafRightH_spec {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)} {i : Nat}
    {a b : NodeId} {L R : Leaf K V} {pa na pb nb : Option NodeId} {last : K × V}
    (hg : h.get id = some (.branch c0 es)) (ha : childAt c0 es i = some a)
    (hb : childAt c0 es (i + 1) = some b) (hga : h.get a = some (.leaf L pa na))
    (hgb : h.get b = some (.leaf R pb nb)) (hab : a ≠ b) (hai : a ≠ id) (hbi : b ≠ id)
    (hlast : L.getLast? = some last) :
    ∃ h', rotateLeafRightH h id i = some h' ∧ h'.get a = some (.leaf L.dropLast pa na) ∧
      h'.get b = some (.leaf (last :: R) pb nb) ∧
      h'.get id = some (.branch c0 (setSep es i last.1)) ∧
      (∀ j, j ≠ a → j ≠ b → j ≠ id → h'.get j = h.get j) ∧ h'.fresh = h.fresh := by
  simp only [rotateLeafRightH, Heap.getBranch_eq hg, ha, hb, Heap.getLeaf_eq hga,
    Heap.getLeaf_eq hgb, hlast, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨h1, hs1, hg1, ho1, hf1⟩ := Heap.setLeaf_spec hga L.dropLast
  rw [hs1]; simp only [Option.bind_some]
  have hgb1 : h1.get b = some (.leaf R pb nb) := by rw [ho1 b (Ne.symm hab)]; exact hgb
  obtain ⟨h2, hs2, hg2, ho2, hf2⟩ := Heap.setLeaf_spec hgb1 (last :: R)
  rw [hs2]; simp only [Option.bind_some]
  have hgid2 : (h2.get id).isSome := by
    rw [ho2 id (Ne.symm hbi), ho1 id (Ne.symm hai)]; simp [hg]
  obtain ⟨h3, hs3, hg3, ho3, hf3⟩ := Heap.setBranch_spec hgid2 c0 (setSep es i last.1)
  refine ⟨h3, hs3, ?_, ?_, hg3, ?_, by rw [hf3, hf2, hf1]⟩
  · rw [ho3 a hai, ho2 a hab]; exact hg1
  · rw [ho3 b hbi]; exact hg2
  · intro j hja hjb hji
    rw [ho3 j hji, ho2 j hjb, ho1 j hja]

/-- `rotate_leaf_left`. -/
theorem rotateLeafLeftH_spec {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)} {i : Nat}
    {a b : NodeId} {L : Leaf K V} {first newFirst : K × V} {R' : Leaf K V}
    {pa na pb nb : Option NodeId}
    (hg : h.get id = some (.branch c0 es)) (ha : childAt c0 es i = some a)
    (hb : childAt c0 es (i + 1) = some b) (hga : h.get a = some (.leaf L pa na))
    (hgb : h.get b = some (.leaf (first :: newFirst :: R') pb nb)) (hab : a ≠ b) (hai : a ≠ id)
    (hbi : b ≠ id) :
    ∃ h', rotateLeafLeftH h id i = some h' ∧ h'.get a = some (.leaf (L ++ [first]) pa na) ∧
      h'.get b = some (.leaf (newFirst :: R') pb nb) ∧
      h'.get id = some (.branch c0 (setSep es i newFirst.1)) ∧
      (∀ j, j ≠ a → j ≠ b → j ≠ id → h'.get j = h.get j) ∧ h'.fresh = h.fresh := by
  simp only [rotateLeafLeftH, Heap.getBranch_eq hg, ha, hb, Heap.getLeaf_eq hga,
    Heap.getLeaf_eq hgb, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨h1, hs1, hg1, ho1, hf1⟩ := Heap.setLeaf_spec hga (L ++ [first])
  rw [hs1]; simp only [Option.bind_some]
  have hgb1 : h1.get b = some (.leaf (first :: newFirst :: R') pb nb) := by
    rw [ho1 b (Ne.symm hab)]; exact hgb
  obtain ⟨h2, hs2, hg2, ho2, hf2⟩ := Heap.setLeaf_spec hgb1 (newFirst :: R')
  rw [hs2]; simp only [Option.bind_some]
  have hgid2 : (h2.get id).isSome := by
    rw [ho2 id (Ne.symm hbi), ho1 id (Ne.symm hai)]; simp [hg]
  obtain ⟨h3, hs3, hg3, ho3, hf3⟩ := Heap.setBranch_spec hgid2 c0 (setSep es i newFirst.1)
  refine ⟨h3, hs3, ?_, ?_, hg3, ?_, by rw [hf3, hf2, hf1]⟩
  · rw [ho3 a hai, ho2 a hab]; exact hg1
  · rw [ho3 b hbi]; exact hg2
  · intro j hja hjb hji
    rw [ho3 j hji, ho2 j hjb, ho1 j hja]

/-- `merge_leaf_pair`: the right leaf's items move left, it is unlinked
and freed, and its entry leaves the branch. -/
theorem mergeLeafPairH_spec {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)} {i : Nat}
    {a b : NodeId} {L R : Leaf K V} {pa nb : Option NodeId}
    (hg : h.get id = some (.branch c0 es)) (ha : childAt c0 es i = some a)
    (hb : childAt c0 es (i + 1) = some b) (hga : h.get a = some (.leaf L pa (some b)))
    (hgb : h.get b = some (.leaf R (some a) nb)) (hab : a ≠ b) (hai : a ≠ id) (hbi : b ≠ id)
    (ho : ∀ o, nb = some o → o ≠ a ∧ o ≠ b ∧ o ≠ id ∧ ∃ O po no, h.get o = some (.leaf O po no)) :
    ∃ h', mergeLeafPairH h id i = some h' ∧ h'.get a = some (.leaf (L ++ R) pa nb) ∧
      h'.get b = none ∧ h'.get id = some (.branch c0 (es.eraseIdx i)) ∧
      (∀ o O po no, nb = some o → h.get o = some (.leaf O po no) →
        h'.get o = some (.leaf O (some a) no)) ∧
      (∀ j, j ≠ a → j ≠ b → j ≠ id → nb ≠ some j → h'.get j = h.get j) ∧ h'.fresh = h.fresh := by
  simp only [mergeLeafPairH, Heap.getBranch_eq hg, ha, hb, Heap.getLeaf_eq hga,
    Heap.getLeaf_eq hgb, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨h1, hs1, hg1, ho1, hf1⟩ := Heap.setLeaf_spec hga (L ++ R)
  rw [hs1]; simp only [Option.bind_some]
  have hgb1 : h1.get b = some (.leaf R (some a) nb) := by rw [ho1 b (Ne.symm hab)]; exact hgb
  obtain ⟨h2, hs2, hg2, ho2, hf2⟩ := Heap.setLeaf_spec hgb1 []
  rw [hs2]; simp only [Option.bind_some]
  have hga2 : h2.get a = some (.leaf (L ++ R) pa (some b)) := by rw [ho2 a hab]; exact hg1
  have ho2' : ∀ o, nb = some o → o ≠ a ∧ o ≠ b ∧ ∃ O po no, h2.get o = some (.leaf O po no) := by
    intro o hno
    obtain ⟨hoa, hob, _, O, po, no, hgo⟩ := ho o hno
    exact ⟨hoa, hob, O, po, no, by rw [ho2 o hob, ho1 o hoa]; exact hgo⟩
  obtain ⟨h3, hfree, hga3, hgb3, hgo3, ho3, hf3⟩ := freeEmptiedLeaf_spec hg2 hga2 hab ho2'
  rw [hfree]; simp only [Option.bind_some]
  have hgid3 : (h3.get id).isSome := by
    rw [ho3 id (Ne.symm hai) (Ne.symm hbi) (fun heq => (ho id heq).2.2.1 rfl),
      ho2 id (Ne.symm hbi), ho1 id (Ne.symm hai)]
    simp [hg]
  obtain ⟨h4, hs4, hg4, ho4, hf4⟩ := Heap.setBranch_spec hgid3 c0 (es.eraseIdx i)
  refine ⟨h4, hs4, ?_, ?_, hg4, ?_, ?_, by rw [hf4, hf3, hf2, hf1]⟩
  · rw [ho4 a hai]; exact hga3
  · rw [ho4 b hbi]; exact hgb3
  · intro o O po no hno hgo
    obtain ⟨hoa, hob, hoi, _⟩ := ho o hno
    rw [ho4 o hoi]
    apply hgo3 o O po no hno
    rw [ho2 o hob, ho1 o hoa]; exact hgo
  · intro j hja hjb hji hjo
    rw [ho4 j hji, ho3 j hja hjb hjo, ho2 j hjb, ho1 j hja]

/-- `rotate_branch_right`: the left branch's last entry moves up, the old
separator moves down with the moved child as the right branch's first. -/
theorem rotateBranchRightH_spec {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {i : Nat} {a b : NodeId} {sep : K} {lc0 rc0 : NodeId} {les res : List (K × NodeId)}
    {promoted : K} {movedChild : NodeId}
    (hg : h.get id = some (.branch c0 es)) (ha : childAt c0 es i = some a)
    (hb : childAt c0 es (i + 1) = some b) (hsep : (es.map Prod.fst)[i]? = some sep)
    (hga : h.get a = some (.branch lc0 les)) (hgb : h.get b = some (.branch rc0 res))
    (hab : a ≠ b) (hai : a ≠ id) (hbi : b ≠ id)
    (hlast : les.getLast? = some (promoted, movedChild)) :
    ∃ h', rotateBranchRightH h id i = some h' ∧ h'.get a = some (.branch lc0 les.dropLast) ∧
      h'.get b = some (.branch movedChild ((sep, rc0) :: res)) ∧
      h'.get id = some (.branch c0 (setSep es i promoted)) ∧
      (∀ j, j ≠ a → j ≠ b → j ≠ id → h'.get j = h.get j) ∧ h'.fresh = h.fresh := by
  have hsep' := hsep
  rw [List.getElem?_map] at hsep'
  obtain ⟨e, he⟩ : ∃ e, es[i]? = some e := by
    cases he : es[i]? with
    | none => rw [he] at hsep'; cases hsep'
    | some e => exact ⟨e, rfl⟩
  rw [he, Option.map_some, Option.some.injEq] at hsep'
  obtain ⟨s', c'⟩ := e
  simp only at hsep'
  subst hsep'
  simp only [rotateBranchRightH, Heap.getBranch_eq hg, ha, hb, he, Heap.getBranch_eq hga,
    Heap.getBranch_eq hgb, hlast, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨h1, hs1, hg1, ho1, hf1⟩ := Heap.setBranch_spec (h := h) (id := a) (by simp [hga]) lc0 les.dropLast
  rw [hs1]; simp only [Option.bind_some]
  have hgb1 : (h1.get b).isSome := by rw [ho1 b (Ne.symm hab)]; simp [hgb]
  obtain ⟨h2, hs2, hg2, ho2, hf2⟩ := Heap.setBranch_spec hgb1 movedChild ((s', rc0) :: res)
  rw [hs2]; simp only [Option.bind_some]
  have hgid2 : (h2.get id).isSome := by
    rw [ho2 id (Ne.symm hbi), ho1 id (Ne.symm hai)]; simp [hg]
  obtain ⟨h3, hs3, hg3, ho3, hf3⟩ := Heap.setBranch_spec hgid2 c0 (setSep es i promoted)
  refine ⟨h3, hs3, ?_, ?_, hg3, ?_, by rw [hf3, hf2, hf1]⟩
  · rw [ho3 a hai, ho2 a hab]; exact hg1
  · rw [ho3 b hbi]; exact hg2
  · intro j hja hjb hji
    rw [ho3 j hji, ho2 j hjb, ho1 j hja]

/-- `rotate_branch_left`. -/
theorem rotateBranchLeftH_spec {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {i : Nat} {a b : NodeId} {sep : K} {lc0 rc0 : NodeId} {les rest : List (K × NodeId)}
    {promoted : K} {rch1 : NodeId}
    (hg : h.get id = some (.branch c0 es)) (ha : childAt c0 es i = some a)
    (hb : childAt c0 es (i + 1) = some b) (hsep : (es.map Prod.fst)[i]? = some sep)
    (hga : h.get a = some (.branch lc0 les))
    (hgb : h.get b = some (.branch rc0 ((promoted, rch1) :: rest)))
    (hab : a ≠ b) (hai : a ≠ id) (hbi : b ≠ id) :
    ∃ h', rotateBranchLeftH h id i = some h' ∧
      h'.get a = some (.branch lc0 (les ++ [(sep, rc0)])) ∧
      h'.get b = some (.branch rch1 rest) ∧
      h'.get id = some (.branch c0 (setSep es i promoted)) ∧
      (∀ j, j ≠ a → j ≠ b → j ≠ id → h'.get j = h.get j) ∧ h'.fresh = h.fresh := by
  have hsep' := hsep
  rw [List.getElem?_map] at hsep'
  obtain ⟨e, he⟩ : ∃ e, es[i]? = some e := by
    cases he : es[i]? with
    | none => rw [he] at hsep'; cases hsep'
    | some e => exact ⟨e, rfl⟩
  rw [he, Option.map_some, Option.some.injEq] at hsep'
  obtain ⟨s', c'⟩ := e
  simp only at hsep'
  subst hsep'
  simp only [rotateBranchLeftH, Heap.getBranch_eq hg, ha, hb, he, Heap.getBranch_eq hga,
    Heap.getBranch_eq hgb, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨h1, hs1, hg1, ho1, hf1⟩ := Heap.setBranch_spec (h := h) (id := a) (by simp [hga]) lc0 (les ++ [(s', rc0)])
  rw [hs1]; simp only [Option.bind_some]
  have hgb1 : (h1.get b).isSome := by rw [ho1 b (Ne.symm hab)]; simp [hgb]
  obtain ⟨h2, hs2, hg2, ho2, hf2⟩ := Heap.setBranch_spec hgb1 rch1 rest
  rw [hs2]; simp only [Option.bind_some]
  have hgid2 : (h2.get id).isSome := by
    rw [ho2 id (Ne.symm hbi), ho1 id (Ne.symm hai)]; simp [hg]
  obtain ⟨h3, hs3, hg3, ho3, hf3⟩ := Heap.setBranch_spec hgid2 c0 (setSep es i promoted)
  refine ⟨h3, hs3, ?_, ?_, hg3, ?_, by rw [hf3, hf2, hf1]⟩
  · rw [ho3 a hai, ho2 a hab]; exact hg1
  · rw [ho3 b hbi]; exact hg2
  · intro j hja hjb hji
    rw [ho3 j hji, ho2 j hjb, ho1 j hja]

/-- `merge_branch_pair`: the separator moves down between the two, the
right branch is emptied and freed, its entry leaves the branch. -/
theorem mergeBranchPairH_spec {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {i : Nat} {a b : NodeId} {sep : K} {lc0 rc0 : NodeId} {les res : List (K × NodeId)}
    (hg : h.get id = some (.branch c0 es)) (ha : childAt c0 es i = some a)
    (hb : childAt c0 es (i + 1) = some b) (hsep : (es.map Prod.fst)[i]? = some sep)
    (hga : h.get a = some (.branch lc0 les)) (hgb : h.get b = some (.branch rc0 res))
    (hab : a ≠ b) (hai : a ≠ id) (hbi : b ≠ id) :
    ∃ h', mergeBranchPairH h id i = some h' ∧
      h'.get a = some (.branch lc0 (les ++ (sep, rc0) :: res)) ∧ h'.get b = none ∧
      h'.get id = some (.branch c0 (es.eraseIdx i)) ∧
      (∀ j, j ≠ a → j ≠ b → j ≠ id → h'.get j = h.get j) ∧ h'.fresh = h.fresh := by
  have hsep' := hsep
  rw [List.getElem?_map] at hsep'
  obtain ⟨e, he⟩ : ∃ e, es[i]? = some e := by
    cases he : es[i]? with
    | none => rw [he] at hsep'; cases hsep'
    | some e => exact ⟨e, rfl⟩
  rw [he, Option.map_some, Option.some.injEq] at hsep'
  obtain ⟨s', c'⟩ := e
  simp only at hsep'
  subst hsep'
  simp only [mergeBranchPairH, Heap.getBranch_eq hg, ha, hb, he, Heap.getBranch_eq hga,
    Heap.getBranch_eq hgb, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨h1, hs1, hg1, ho1, hf1⟩ := Heap.setBranch_spec (h := h) (id := id) (by simp [hg]) c0 (es.eraseIdx i)
  rw [hs1]; simp only [Option.bind_some]
  have hga1 : (h1.get a).isSome := by rw [ho1 a hai]; simp [hga]
  obtain ⟨h2, hs2, hg2, ho2, hf2⟩ := Heap.setBranch_spec hga1 lc0 (les ++ (s', rc0) :: res)
  rw [hs2]; simp only [Option.bind_some]
  have hgb2 : (h2.get b).isSome := by rw [ho2 b (Ne.symm hab), ho1 b hbi]; simp [hgb]
  obtain ⟨h3, hs3, hg3, ho3, hf3⟩ := Heap.setBranch_spec hgb2 rc0 []
  rw [hs3]; simp only [Option.bind_some]
  obtain ⟨h4, hfree, hg4, ho4, hf4⟩ := freeEmptiedBranch_spec hg3
  refine ⟨h4, hfree, ?_, hg4, ?_, ?_, by rw [hf4, hf3, hf2, hf1]⟩
  · rw [ho4 a hab, ho3 a hab]; exact hg2
  · rw [ho4 id (Ne.symm hbi), ho3 id (Ne.symm hbi), ho2 id (Ne.symm hai)]; exact hg1
  · intro j hja hjb hji
    rw [ho4 j hjb, ho3 j hjb, ho2 j hja, ho1 j hji]

/-! ## Windows: two adjacent children of a branch -/

/-- A chain survives content changes to its leaves as long as every
leaf keeps its links. -/
theorem linked_congr_links {h h' : Heap K V} {prev next : Option NodeId} {l : List NodeId}
    (hsame : ∀ i ∈ l, ∀ kvs p n, h.get i = some (.leaf kvs p n) →
      ∃ kvs', h'.get i = some (.leaf kvs' p n)) :
    Linked h prev l next → Linked h' prev l next := by
  induction l generalizing prev with
  | nil => intro; trivial
  | cons a t ih =>
    rintro ⟨⟨kvs, hr⟩, hrest⟩
    obtain ⟨kvs', hr'⟩ := hsame a List.mem_cons_self kvs _ _ hr
    exact ⟨⟨kvs', hr'⟩, ih (fun i hi => hsame i (List.mem_cons_of_mem _ hi)) hrest⟩

/-- The pieces around slots `i` and `i + 1` of a branch's children: the
ids, and the reach and leaf lists of the four parts. -/
theorem window_ctx {d : Nat} {h : Heap K V} {c0 : NodeId} {es : List (K × NodeId)} {i : Nat}
    {below lv : List NodeId}
    (hreach : reachIds.reachChildren d h (c0 :: es.map (·.2)) = some below)
    (hlv : leafIds.leafChildren d h (c0 :: es.map (·.2)) = some lv)
    (hi : i + 1 < (c0 :: es.map (·.2)).length) :
    ∃ (csF csB : List NodeId) (a b : NodeId) (LF La Lb LB lvF lva lvb lvB : List NodeId),
      c0 :: es.map (·.2) = csF ++ a :: b :: csB ∧ csF.length = i ∧
      childAt c0 es i = some a ∧ childAt c0 es (i + 1) = some b ∧
      reachIds.reachChildren d h csF = some LF ∧ reachIds d h a = some La ∧
      reachIds d h b = some Lb ∧ reachIds.reachChildren d h csB = some LB ∧
      leafIds.leafChildren d h csF = some lvF ∧ leafIds d h a = some lva ∧
      leafIds d h b = some lvb ∧ leafIds.leafChildren d h csB = some lvB ∧
      below = LF ++ (La ++ (Lb ++ LB)) ∧ lv = lvF ++ (lva ++ (lvb ++ lvB)) := by
  obtain ⟨a, ha⟩ : ∃ a, (c0 :: es.map (·.2))[i]? = some a := by
    rw [List.getElem?_eq_getElem (by omega)]; exact ⟨_, rfl⟩
  obtain ⟨csF, rest, hsplit, hlen⟩ := split_at_getElem? ha
  cases rest with
  | nil => rw [hsplit] at hi; simp at hi; omega
  | cons b csB =>
    have hb : (c0 :: es.map (·.2))[i + 1]? = some b := by
      rw [hsplit, List.getElem?_append_right (by omega)]
      simp [hlen]
    rw [hsplit, reachChildren_append, reachChildren_cons, reachChildren_cons] at hreach
    rw [hsplit, leafChildren_append, leafChildren_cons, leafChildren_cons] at hlv
    rcases hLF : reachIds.reachChildren d h csF with _ | LF
    · rw [hLF] at hreach; cases hreach
    rcases hLa : reachIds d h a with _ | La
    · rw [hLF, hLa] at hreach; cases hreach
    rcases hLb : reachIds d h b with _ | Lb
    · rw [hLF, hLa, hLb] at hreach; cases hreach
    rcases hLB : reachIds.reachChildren d h csB with _ | LB
    · rw [hLF, hLa, hLb, hLB] at hreach; cases hreach
    rw [hLF, hLa, hLb, hLB] at hreach
    simp only [Option.bind_some, Option.some.injEq] at hreach
    rcases hlvF : leafIds.leafChildren d h csF with _ | lvF
    · rw [hlvF] at hlv; cases hlv
    rcases hlva : leafIds d h a with _ | lva
    · rw [hlvF, hlva] at hlv; cases hlv
    rcases hlvb : leafIds d h b with _ | lvb
    · rw [hlvF, hlva, hlvb] at hlv; cases hlv
    rcases hlvB : leafIds.leafChildren d h csB with _ | lvB
    · rw [hlvF, hlva, hlvb, hlvB] at hlv; cases hlv
    rw [hlvF, hlva, hlvb, hlvB] at hlv
    simp only [Option.bind_some, Option.some.injEq] at hlv
    exact ⟨csF, csB, a, b, LF, La, Lb, LB, lvF, lva, lvb, lvB, hsplit, hlen, ha, hb, hLF, hLa,
      hLb, hLB, hlvF, hlva, hlvb, hlvB, hreach.symm, hlv.symm⟩

/-- Mapping over a window: only the two slots differ. -/
theorem map_window {C : Type} (f g : NodeId → C) (csF csB : List NodeId) (a b : NodeId)
    (hF : ∀ c ∈ csF, g c = f c) (hB : ∀ c ∈ csB, g c = f c) :
    (csF ++ a :: b :: csB).map g =
      (((csF ++ a :: b :: csB).map f).set csF.length (g a)).set (csF.length + 1) (g b) := by
  rw [List.map_append, List.map_append, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
    List.set_append_right _ _ (by simp), List.set_append_right _ _ (by simp)]
  simp only [List.length_map, Nat.sub_self, List.set_cons_zero, Nat.add_sub_cancel_left,
    List.set_cons_succ]
  rw [List.map_congr_left hF, List.map_congr_left hB]

theorem map_window_erase {C : Type} (f g : NodeId → C) (csF csB : List NodeId) (a b : NodeId)
    (hF : ∀ c ∈ csF, g c = f c) (hB : ∀ c ∈ csB, g c = f c) :
    (csF ++ a :: csB).map g =
      (((csF ++ a :: b :: csB).map f).set csF.length (g a)).eraseIdx (csF.length + 1) := by
  rw [List.map_append, List.map_append, List.map_cons, List.map_cons, List.map_cons,
    List.set_append_right _ _ (by simp), List.eraseIdx_append_of_length_le (by simp)]
  simp only [List.length_map, Nat.sub_self, List.set_cons_zero, Nat.add_sub_cancel_left,
    List.eraseIdx_cons_succ, List.eraseIdx_cons_zero]
  rw [List.map_congr_left hF, List.map_congr_left hB]

theorem eraseIdx_window2 {α : Type} (csF csB : List α) (a b : α) :
    (csF ++ a :: b :: csB).eraseIdx (csF.length + 1) = csF ++ a :: csB := by
  rw [List.eraseIdx_append_of_length_le (by simp)]
  simp [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero]

/-! ### Reassembling a branch after a repair -/

theorem bounded_of_subset {h h' : Heap K V} (hb : Heap.Bounded h) (hfr : h'.fresh = h.fresh)
    (hs : ∀ i, (h'.get i).isSome → (h.get i).isSome) : Heap.Bounded h' := by
  intro i hi
  rw [hfr]; exact hb i (hs i hi)

theorem reachChildren_mem {d : Nat} {h : Heap K V} {cs L : List NodeId}
    (hL : reachIds.reachChildren d h cs = some L) : ∀ c ∈ cs, ∃ Lc, reachIds d h c = some Lc := by
  induction cs generalizing L with
  | nil => intro c hc; cases hc
  | cons x t ih =>
    intro c hc
    rw [reachChildren_cons] at hL
    rcases hx : reachIds d h x with _ | Lx
    · rw [hx] at hL; cases hL
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨Lx, hx⟩
    · rcases ht : reachIds.reachChildren d h t with _ | Lt
      · rw [hx, ht] at hL; cases hL
      · exact ih ht c hc

/-- A branch record whose children all walk: its `Sub` in array form. -/
theorem sub_branch_mk {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {L lv : List NodeId} (hg : h.get id = some (.branch c0 es))
    (hreach : reachIds.reachChildren d h (c0 :: es.map (·.2)) = some L)
    (hlv : leafIds.leafChildren d h (c0 :: es.map (·.2)) = some lv)
    (hall : ∀ c ∈ c0 :: es.map (·.2), ∃ t, absNode d h c = some t) :
    Sub h (d + 1) id (mkBranch (es.map Prod.fst) ((c0 :: es.map (·.2)).map (absF d h)))
      (id :: L) lv :=
  ⟨absNode_branch_mk hg hall, by rw [reachIds_branch hg, hreach]; rfl,
    by rw [leafIds_branch hg, hlv]⟩

/-- What every repair delivers about the branch: a well-defined subtree
again, ids a subset of the old (the rest freed), the first leaf kept, the
chain intact, and the frame. -/
def FixPost (d : Nat) (h h' : Heap K V) (id : NodeId) (node' : Node K V)
    (below lv : List NodeId) (prev0 next0 : Option NodeId) : Prop :=
  ∃ ids' lv', Sub h' (d + 2) id node' ids' lv' ∧ ids'.Nodup ∧ (∀ i ∈ ids', i ∈ id :: below) ∧
    (∀ i ∈ id :: below, i ∉ ids' → h'.get i = none) ∧ lv'.head? = lv.head? ∧
    Linked h' prev0 lv' next0 ∧ Frame h h' (id :: below) next0 (lv'.getLast?.or prev0)

/-- The common shape of every repair: the window at slots `i`, `i + 1`
becomes `mid` (the same two children rewritten, or the left one alone);
`mid` walks under `h'` to ids drawn from the old window's ids, the
window's leaves start where they did, everything outside the window keeps
its content, and the chain is given. -/
theorem window_reassemble {d : Nat} {h h' : Heap K V} {id c0 c0' : NodeId}
    {es es' : List (K × NodeId)} {csF csB mid : List NodeId} {a b : NodeId}
    {LF La Lb LB lvF lva lvb lvB Lmid lvmid : List NodeId}
    {prev0 next0 : Option NodeId}
    (hcs : c0 :: es.map (·.2) = csF ++ a :: b :: csB)
    (hLF : reachIds.reachChildren (d + 1) h csF = some LF)
    (hLa : reachIds (d + 1) h a = some La) (hLb : reachIds (d + 1) h b = some Lb)
    (hLB : reachIds.reachChildren (d + 1) h csB = some LB)
    (hlvF : leafIds.leafChildren (d + 1) h csF = some lvF)
    (hlva : leafIds (d + 1) h a = some lva)
    (hlvB : leafIds.leafChildren (d + 1) h csB = some lvB)
    (hall : ∀ c ∈ c0 :: es.map (·.2), ∃ t, absNode (d + 1) h c = some t)
    (hnd : (id :: (LF ++ (La ++ (Lb ++ LB)))).Nodup)
    (hid' : h'.get id = some (.branch c0' es')) (hcs' : c0' :: es'.map (·.2) = csF ++ mid ++ csB)
    (hmidR : reachIds.reachChildren (d + 1) h' mid = some Lmid)
    (hmidL : leafIds.leafChildren (d + 1) h' mid = some lvmid)
    (hmidA : ∀ c ∈ mid, ∃ t, absNode (d + 1) h' c = some t)
    (hmidnd : Lmid.Nodup) (hmidsub : ∀ i ∈ Lmid, i ∈ La ++ Lb)
    (hdropped : ∀ i ∈ La ++ Lb, i ∉ Lmid → h'.get i = none)
    (hmidne : lvmid ≠ []) (hhead : lvmid.head? = lva.head?)
    (hsame : ∀ j ∈ LF ++ LB, SameContent (h.get j) (h'.get j))
    (hl' : Linked h' prev0 (lvF ++ (lvmid ++ lvB)) next0)
    (hframe : ∀ i, i ∉ id :: (LF ++ (La ++ (Lb ++ LB))) → next0 ≠ some i → h'.get i = h.get i)
    (hsucc : ∀ o O p n, next0 = some o → h.get o = some (.leaf O p n) →
      h'.get o = some (.leaf O ((lvF ++ (lvmid ++ lvB)).getLast?.or prev0) n)) :
    FixPost d h h' id (mkBranch (es'.map Prod.fst) ((csF ++ mid ++ csB).map (absF (d + 1) h')))
      (LF ++ (La ++ (Lb ++ LB))) (lvF ++ (lva ++ (lvb ++ lvB))) prev0 next0 := by
  obtain ⟨hidnb, hndbelow⟩ := List.nodup_cons.mp hnd
  obtain ⟨hLF', habsF, hlvF'⟩ := children_congr (d + 1) csF LF hLF
    (fun j hj => hsame j (List.mem_append_left _ hj))
  obtain ⟨hLB', habsB, hlvB'⟩ := children_congr (d + 1) csB LB hLB
    (fun j hj => hsame j (List.mem_append_right _ hj))
  have hallF : ∀ c ∈ csF, ∃ t, absNode (d + 1) h c = some t :=
    fun c hc => hall c (by rw [hcs]; exact List.mem_append_left _ hc)
  have hallB : ∀ c ∈ csB, ∃ t, absNode (d + 1) h c = some t :=
    fun c hc => hall c (by
      rw [hcs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)))
  have hall' : ∀ c ∈ c0' :: es'.map (·.2), ∃ t, absNode (d + 1) h' c = some t := by
    rw [hcs']
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_append.mp hc with hc | hc
      · rw [habsF c hc]; exact hallF c hc
      · exact hmidA c hc
    · rw [habsB c hc]; exact hallB c hc
  have hreach' : reachIds.reachChildren (d + 1) h' (csF ++ mid ++ csB) =
      some (LF ++ (Lmid ++ LB)) := by
    rw [reachChildren_append, reachChildren_append, hLF', hmidR, hLB']
    simp [Option.bind_some]
  have hlv'' : leafIds.leafChildren (d + 1) h' (csF ++ mid ++ csB) =
      some (lvF ++ (lvmid ++ lvB)) := by
    rw [leafChildren_append, leafChildren_append, hlvF', hlvF, hmidL, hlvB', hlvB]
    simp [Option.bind_some]
  have hsub := sub_branch_mk hid' (by rw [hcs']; exact hreach') (by rw [hcs']; exact hlv'') hall'
  rw [hcs'] at hsub
  -- pieces of the old Nodup
  rw [nodup_append_iff] at hndbelow
  obtain ⟨hndF, hndR, hdisjF⟩ := hndbelow
  rw [nodup_append_iff] at hndR
  obtain ⟨hndA, hndR, hdisjA⟩ := hndR
  rw [nodup_append_iff] at hndR
  obtain ⟨hndB, hndLB, hdisjB⟩ := hndR
  have hLFdisj : ∀ j ∈ LF, j ∉ La ++ Lb := fun j hj hin =>
    hdisjF j hj j (by rw [← List.append_assoc]; exact List.mem_append_left _ hin) rfl
  have hLBdisj : ∀ j ∈ LB, j ∉ La ++ Lb := fun j hj hin => by
    rcases List.mem_append.mp hin with hin | hin
    · exact hdisjA _ hin j (List.mem_append_right _ hj) rfl
    · exact hdisjB _ hin j hj rfl
  have hlvane : lva ≠ [] := ((leaf_facts (d + 1)).1 h a La lva hLa hlva).1
  refine ⟨id :: (LF ++ (Lmid ++ LB)), lvF ++ (lvmid ++ lvB), hsub, ?_, ?_, ?_, ?_, hl', ?_⟩
  · -- Nodup
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro hin
      apply hidnb
      simp only [List.mem_append] at hin ⊢
      rcases hin with hin | hin | hin
      · exact Or.inl hin
      · have := hmidsub id hin
        simp only [List.mem_append] at this
        rcases this with h1 | h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr hin))
    · rw [nodup_append_iff]
      refine ⟨hndF, ?_, ?_⟩
      · rw [nodup_append_iff]
        refine ⟨hmidnd, hndLB, fun x hx y hy hxy => ?_⟩
        subst hxy
        exact hLBdisj x hy (hmidsub x hx)
      · intro x hx y hy hxy
        subst hxy
        rcases List.mem_append.mp hy with hy | hy
        · exact hLFdisj x hx (hmidsub x hy)
        · exact hdisjF x hx x (List.mem_append_right _ (List.mem_append_right _ hy)) rfl
  · -- subset
    intro i hi
    simp only [List.mem_cons, List.mem_append] at hi ⊢
    rcases hi with hi | hi | hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · have := hmidsub i hi
      simp only [List.mem_append] at this
      rcases this with h1 | h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))
  · -- dropped ids are freed
    intro i hi hni
    simp only [List.mem_cons, List.mem_append, not_or] at hi hni
    rcases hi with hi | hi | hi | hi | hi
    · exact absurd hi hni.1
    · exact absurd hi hni.2.1
    · exact hdropped i (List.mem_append_left _ hi) hni.2.2.1
    · exact hdropped i (List.mem_append_right _ hi) hni.2.2.1
    · exact absurd hi hni.2.2.2
  · -- first leaf
    cases lvF with
    | cons x t => rfl
    | nil =>
      simp only [List.nil_append]
      rw [head?_append_of_ne_nil _ hmidne, head?_append_of_ne_nil _ hlvane, hhead]
  · -- frame: untouched outside, successor's prev
    exact ⟨fun i hi hne _ => hframe i hi hne, fun o O p n ho hgo => hsucc o O p n ho hgo⟩

/-! ### Facts common to every repair on a window -/

theorem nodup_mid_disjoint {α : Type} {l1 m l2 : List α} (hnd : (l1 ++ (m ++ l2)).Nodup) :
    ∀ x ∈ m, x ∉ l1 ++ l2 := by
  rw [nodup_append_iff] at hnd
  obtain ⟨_, hnd2, hdisj⟩ := hnd
  rw [nodup_append_iff] at hnd2
  intro x hx hin
  rcases List.mem_append.mp hin with hin | hin
  · exact hdisj x hin x (List.mem_append_left _ hx) rfl
  · exact hnd2.2.2 x hx x hin rfl

theorem linked_split_mid {h : Heap K V} {prev next : Option NodeId} {l1 l2 : List NodeId}
    {b : NodeId} (hl : Linked h prev (l1 ++ b :: l2) next) :
    ∃ kvs, h.get b = some (.leaf kvs (l1.getLast?.or prev) (l2.head?.or next)) := by
  rw [linked_append] at hl
  exact hl.2.1

/-- A repair rewrites `a`, `b`, `id`, and possibly one leaf `nb` (keeping
its content); from that, the pieces of `FixPost` that do not depend on the
repair, and boundedness. -/
theorem window_frame_facts {d : Nat} {h h' : Heap K V} {id a b : NodeId} {csF csB : List NodeId}
    {LF La Lb LB lv : List NodeId} {prev0 next0 nb : Option NodeId}
    (hLF : reachIds.reachChildren (d + 1) h csF = some LF)
    (hLa : reachIds (d + 1) h a = some La) (hLb : reachIds (d + 1) h b = some Lb)
    (hLB : reachIds.reachChildren (d + 1) h csB = some LB)
    (hnd : (id :: (LF ++ (La ++ (Lb ++ LB)))).Nodup) (hb : Heap.Bounded h)
    (hgid : (h.get id).isSome)
    (hnext : NextOK h (id :: (LF ++ (La ++ (Lb ++ LB)))) lv prev0 next0)
    (hother : ∀ j, j ≠ a → j ≠ b → j ≠ id → nb ≠ some j → h'.get j = h.get j)
    (ho : ∀ o, nb = some o →
      ∃ O p p' n, h.get o = some (.leaf O p n) ∧ h'.get o = some (.leaf O p' n))
    (hnb : ∀ o, nb = some o → o ∈ LF ++ (La ++ (Lb ++ LB)) ∨ next0 = some o)
    (hfr : h'.fresh = h.fresh) :
    (∀ j ∈ LF ++ LB, SameContent (h.get j) (h'.get j)) ∧
    (∀ i, i ∉ id :: (LF ++ (La ++ (Lb ++ LB))) → next0 ≠ some i → h'.get i = h.get i) ∧
    (∀ c ∈ csF, absNode (d + 1) h' c = absNode (d + 1) h c) ∧
    (∀ c ∈ csB, absNode (d + 1) h' c = absNode (d + 1) h c) ∧ Heap.Bounded h' := by
  obtain ⟨hidnb, hndbelow⟩ := List.nodup_cons.mp hnd
  have haLa := mem_reachIds_self hLa
  have hbLb := mem_reachIds_self hLb
  have hamem : a ∈ LF ++ (La ++ (Lb ++ LB)) :=
    List.mem_append_right _ (List.mem_append_left _ haLa)
  have hbmem : b ∈ LF ++ (La ++ (Lb ++ LB)) :=
    List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hbLb))
  have hW : ∀ x ∈ La ++ Lb, x ∉ LF ++ LB := by
    have : LF ++ (La ++ (Lb ++ LB)) = LF ++ ((La ++ Lb) ++ LB) := by simp
    rw [this] at hndbelow
    exact nodup_mid_disjoint hndbelow
  have hsame : ∀ j ∈ LF ++ LB, SameContent (h.get j) (h'.get j) := by
    intro j hj
    have hja : j ≠ a := fun heq => hW a (List.mem_append_left _ haLa) (heq ▸ hj)
    have hjb : j ≠ b := fun heq => hW b (List.mem_append_right _ hbLb) (heq ▸ hj)
    have hji : j ≠ id := fun heq => hidnb (heq ▸ (by
      rcases List.mem_append.mp hj with hj | hj
      · exact List.mem_append_left _ hj
      · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ hj))))
    by_cases hnbj : nb = some j
    · obtain ⟨O, p, p', n, hgo, hgo'⟩ := ho j hnbj
      rw [hgo, hgo']; exact sameContent_leaf
    · exact sameContent_of_eq (hother j hja hjb hji hnbj)
  refine ⟨hsame, ?_, (children_congr (d + 1) csF LF hLF
      (fun j hj => hsame j (List.mem_append_left _ hj))).2.1,
    (children_congr (d + 1) csB LB hLB (fun j hj => hsame j (List.mem_append_right _ hj))).2.1,
    ?_⟩
  · intro i hi hne
    simp only [List.mem_cons, not_or] at hi
    exact hother i (fun heq => hi.2 (heq ▸ hamem)) (fun heq => hi.2 (heq ▸ hbmem)) hi.1
      (fun hnbi => (hnb i hnbi).elim hi.2 hne)
  · refine bounded_of_subset hb hfr (fun i hi => ?_)
    by_cases hia : i = a
    · subst hia; exact mem_reachIds_allocated (d + 1) h i La hLa i haLa
    by_cases hib : i = b
    · subst hib; exact mem_reachIds_allocated (d + 1) h i Lb hLb i hbLb
    by_cases hii : i = id
    · subst hii; exact hgid
    by_cases hnbi : nb = some i
    · obtain ⟨O, p, p', n, hgo, _⟩ := ho i hnbi
      simp [hgo]
    · rw [hother i hia hib hii hnbi] at hi; exact hi

/-- The successor leaf keeps its record when the repair does not touch it. -/
theorem window_succ {d : Nat} {h h' : Heap K V} {id a b : NodeId}
    {LF La Lb LB lv : List NodeId} {prev0 next0 nb : Option NodeId}
    (hLa : reachIds (d + 1) h a = some La) (hLb : reachIds (d + 1) h b = some Lb)
    (hnext : NextOK h (id :: (LF ++ (La ++ (Lb ++ LB)))) lv prev0 next0)
    (hother : ∀ j, j ≠ a → j ≠ b → j ≠ id → nb ≠ some j → h'.get j = h.get j)
    (hnbo : ∀ o, next0 = some o → nb ≠ some o) :
    ∀ o O p n, next0 = some o → h.get o = some (.leaf O p n) →
      h'.get o = some (.leaf O (lv.getLast?.or prev0) n) := by
  intro o O p n ho' hgo
  obtain ⟨hout, O', n', hgo'⟩ := hnext o ho'
  rw [hgo] at hgo'
  cases hgo'
  simp only [List.mem_cons, not_or] at hout
  have haLa := mem_reachIds_self hLa
  have hbLb := mem_reachIds_self hLb
  rw [hother o (fun heq => hout.2 (heq ▸ List.mem_append_right _ (List.mem_append_left _ haLa)))
    (fun heq => hout.2 (heq ▸ List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hbLb)))) hout.1 (hnbo o ho')]
  exact hgo

/-- Everything `fix_branch_child` knows about a branch and the window at
slots `csF.length`, `csF.length + 1` before a repair. -/
structure WinCtx (d : Nat) (h : Heap K V) (id c0 : NodeId) (es : List (K × NodeId))
    (csF csB : List NodeId) (a b : NodeId) (LF La Lb LB lvF lva lvb lvB : List NodeId)
    (prev0 next0 : Option NodeId) : Prop where
  hg : h.get id = some (.branch c0 es)
  hcs : c0 :: es.map (·.2) = csF ++ a :: b :: csB
  hLF : reachIds.reachChildren (d + 1) h csF = some LF
  hLa : reachIds (d + 1) h a = some La
  hLb : reachIds (d + 1) h b = some Lb
  hLB : reachIds.reachChildren (d + 1) h csB = some LB
  hlvF : leafIds.leafChildren (d + 1) h csF = some lvF
  hlva : leafIds (d + 1) h a = some lva
  hlvb : leafIds (d + 1) h b = some lvb
  hlvB : leafIds.leafChildren (d + 1) h csB = some lvB
  hall : ∀ c ∈ c0 :: es.map (·.2), ∃ t, absNode (d + 1) h c = some t
  hnd : (id :: (LF ++ (La ++ (Lb ++ LB)))).Nodup
  hb : Heap.Bounded h
  hl : Linked h prev0 (lvF ++ (lva ++ (lvb ++ lvB))) next0
  hnext : NextOK h (id :: (LF ++ (La ++ (Lb ++ LB)))) (lvF ++ (lva ++ (lvb ++ lvB))) prev0 next0

/-- What a repair simulation concludes: no fault, no allocation, bounded,
and `FixPost` for the arrays the tree model computes. -/
def RepairSim (d : Nat) (h : Heap K V) (id : NodeId) (below lv : List NodeId)
    (prev0 next0 : Option NodeId) (res : Option (Heap K V))
    (arrays : List K × List (Node K V)) : Prop :=
  ∃ h', res = some h' ∧ h'.fresh = h.fresh ∧ Heap.Bounded h' ∧
    FixPost d h h' id (mkBranch arrays.1 arrays.2) below lv prev0 next0

theorem WinCtx.ha {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0) :
    childAt c0 es csF.length = some a := by
  rw [childAt, W.hcs, getElem?_window_fst]

theorem WinCtx.hb' {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0) :
    childAt c0 es (csF.length + 1) = some b := by
  rw [childAt, W.hcs, getElem?_window_snd]

theorem WinCtx.distinct {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0) :
    a ≠ b ∧ a ≠ id ∧ b ≠ id := by
  obtain ⟨hidnb, hndbelow⟩ := List.nodup_cons.mp W.hnd
  have haLa := mem_reachIds_self W.hLa
  have hbLb := mem_reachIds_self W.hLb
  rw [nodup_append_iff] at hndbelow
  obtain ⟨_, hndR, _⟩ := hndbelow
  rw [nodup_append_iff] at hndR
  refine ⟨fun heq => hndR.2.2 a haLa a (List.mem_append_left _ (heq ▸ hbLb)) rfl, ?_, ?_⟩
  · intro heq; subst heq
    exact hidnb (List.mem_append_right _ (List.mem_append_left _ haLa))
  · intro heq; subst heq
    exact hidnb (List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hbLb)))

theorem WinCtx.idx_lt {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0) :
    csF.length < es.length := by
  have := congrArg List.length W.hcs
  simp at this; omega

theorem WinCtx.leaf_shape {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0)
    {L R : Leaf K V} {pa na pb nb : Option NodeId}
    (hga : h.get a = some (.leaf L pa na)) (hgb : h.get b = some (.leaf R pb nb)) :
    La = [a] ∧ Lb = [b] ∧ lva = [a] ∧ lvb = [b] := by
  have h1 := W.hLa; have h2 := W.hLb; have h3 := W.hlva; have h4 := W.hlvb
  rw [reachIds_leaf hga] at h1; rw [reachIds_leaf hgb] at h2
  rw [leafIds_leaf hga] at h3; rw [leafIds_leaf hgb] at h4
  cases h1; cases h2; cases h3; cases h4
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The leaf links seen by `Linked`: `a`'s next is `b`, `b`'s prev is `a`,
and `b`'s next is the following leaf or `next0`. -/
theorem WinCtx.leaf_links {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF [a] [b] lvB prev0 next0)
    {L R : Leaf K V} {pa na pb nb : Option NodeId}
    (hga : h.get a = some (.leaf L pa na)) (hgb : h.get b = some (.leaf R pb nb)) :
    na = some b ∧ pb = some a ∧ nb = lvB.head?.or next0 := by
  have hl := W.hl
  have : lvF ++ ([a] ++ ([b] ++ lvB)) = (lvF ++ [a]) ++ b :: lvB := by simp
  rw [this] at hl
  obtain ⟨kvs, hgb'⟩ := linked_split_mid hl
  rw [hgb] at hgb'
  cases hgb'
  have hl2 := W.hl
  have : lvF ++ ([a] ++ ([b] ++ lvB)) = lvF ++ a :: (b :: lvB) := by simp
  rw [this] at hl2
  obtain ⟨kvs, hga'⟩ := linked_split_mid hl2
  rw [hga] at hga'
  cases hga'
  refine ⟨rfl, ?_, rfl⟩
  simp [List.getLast?_append]

/-! ### The leaf repairs -/

theorem rotateLeafRightH_sim {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0)
    {L R : Leaf K V} {pa na pb nb : Option NodeId}
    (hga : h.get a = some (.leaf L pa na)) (hgb : h.get b = some (.leaf R pb nb)) (hL : L ≠ []) :
    RepairSim d h id (LF ++ (La ++ (Lb ++ LB))) (lvF ++ (lva ++ (lvb ++ lvB))) prev0 next0
      (rotateLeafRightH h id csF.length)
      (rotateLeafRight (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
        csF.length) := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := W.leaf_shape hga hgb
  obtain ⟨hab, hai, hbi⟩ := W.distinct
  obtain ⟨hg, hcs, hLF, hLa, hLb, hLB, hlvF, hlva, hlvb, hlvB, hall, hnd, hb, hl, hnext⟩ := W
  have ha : childAt c0 es csF.length = some a := by rw [childAt, hcs, getElem?_window_fst]
  have hb' : childAt c0 es (csF.length + 1) = some b := by rw [childAt, hcs, getElem?_window_snd]
  have hj : csF.length < es.length := by
    have := congrArg List.length hcs; simp at this; omega
  obtain ⟨last, hlast⟩ := Option.ne_none_iff_exists'.mp
    (fun heq => hL (List.getLast?_eq_none_iff.mp heq))
  obtain ⟨h', hrun, hga', hgb', hgid', hother, hfr⟩ :=
    rotateLeafRightH_spec hg ha hb' hga hgb hab hai hbi hlast
  obtain ⟨hsame, hframe, habsF, habsB, hbd⟩ := window_frame_facts (nb := none) hLF hLa hLb
    hLB hnd hb (by simp [hg]) hnext (fun j hja hjb hji _ => hother j hja hjb hji)
    (fun o ho => by cases ho) (fun o ho => by cases ho) hfr
  have hsucc := window_succ (nb := none) hLa hLb hnext (fun j hja hjb hji _ => hother j hja hjb hji)
    (fun o _ ho => by cases ho)
  refine ⟨h', hrun, hfr, hbd, ?_⟩
  have harr : rotateLeafRight (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
      csF.length =
      ((setSep es csF.length last.1).map Prod.fst,
        (csF ++ a :: b :: csB).map (absF (d + 1) h')) := by
    simp only [rotateLeafRight, List.getElem?_map, getElem?_window_fst, getElem?_window_snd,
      Option.map_some, absF_of_some (absNode_leaf hga d), absF_of_some (absNode_leaf hgb d),
      hlast]
    rw [map_fst_setSep _ _ _ hj, map_window (absF (d + 1) h) (absF (d + 1) h') csF csB a b
      (fun c hc => by simp [absF, habsF c hc]) (fun c hc => by simp [absF, habsB c hc]),
      absF_of_some (absNode_leaf hga' d), absF_of_some (absNode_leaf hgb' d)]
  rw [harr]
  have hmid : c0 :: (setSep es csF.length last.1).map (·.2) = csF ++ [a, b] ++ csB := by
    rw [show (fun x : K × NodeId => x.2) = Prod.snd from rfl, map_snd_setSep, hcs]; simp
  have hlinks : ∀ i ∈ lvF ++ ([a] ++ ([b] ++ lvB)), ∀ kvs p n, h.get i = some (.leaf kvs p n) →
      ∃ kvs', h'.get i = some (.leaf kvs' p n) := by
    intro i _ kvs p n hgi
    by_cases hia : i = a
    · subst hia; rw [hga] at hgi; cases hgi; exact ⟨_, hga'⟩
    by_cases hib : i = b
    · subst hib; rw [hgb] at hgi; cases hgi; exact ⟨_, hgb'⟩
    have hii : i ≠ id := fun heq => by subst heq; rw [hg] at hgi; cases hgi
    exact ⟨kvs, by rw [hother i hia hib hii]; exact hgi⟩
  have hl' := linked_congr_links hlinks hl
  simp only [List.cons_append, List.nil_append] at hl' hsucc ⊢
  have := window_reassemble (mid := [a, b]) (Lmid := [a, b]) (lvmid := [a, b]) (lvb := [b])
    hcs hLF hLa hLb hLB
    hlvF hlva hlvB hall hnd hgid' hmid
    (by simp [reachChildren_cons, reachIds.reachChildren, reachIds_leaf hga', reachIds_leaf hgb'])
    (by simp [leafChildren_cons, leafIds.leafChildren, leafIds_leaf hga', leafIds_leaf hgb'])
    (fun c hc => by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc <;> rw [hc]
      · exact ⟨_, absNode_leaf hga' d⟩
      · exact ⟨_, absNode_leaf hgb' d⟩)
    (by simp [hab]) (fun i hi => by simpa using hi) (fun i hi hni => absurd (by simpa using hi) hni)
    (by simp) rfl hsame (by simpa using hl') hframe (by simpa using hsucc)
  simpa using this

theorem rotateLeafLeftH_sim {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0)
    {L R : Leaf K V} {pa na pb nb : Option NodeId}
    (hga : h.get a = some (.leaf L pa na)) (hgb : h.get b = some (.leaf R pb nb))
    (hR : 2 ≤ R.length) :
    RepairSim d h id (LF ++ (La ++ (Lb ++ LB))) (lvF ++ (lva ++ (lvb ++ lvB))) prev0 next0
      (rotateLeafLeftH h id csF.length)
      (rotateLeafLeft (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
        csF.length) := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := W.leaf_shape hga hgb
  obtain ⟨hab, hai, hbi⟩ := W.distinct
  obtain ⟨hg, hcs, hLF, hLa, hLb, hLB, hlvF, hlva, hlvb, hlvB, hall, hnd, hb, hl, hnext⟩ := W
  have ha : childAt c0 es csF.length = some a := by rw [childAt, hcs, getElem?_window_fst]
  have hb' : childAt c0 es (csF.length + 1) = some b := by rw [childAt, hcs, getElem?_window_snd]
  have hj : csF.length < es.length := by
    have := congrArg List.length hcs; simp at this; omega
  obtain ⟨first, newFirst, R', rfl⟩ : ∃ first newFirst R', R = first :: newFirst :: R' := by
    match R, hR with
    | first :: newFirst :: R', _ => exact ⟨first, newFirst, R', rfl⟩
  obtain ⟨h', hrun, hga', hgb', hgid', hother, hfr⟩ :=
    rotateLeafLeftH_spec hg ha hb' hga hgb hab hai hbi
  obtain ⟨hsame, hframe, habsF, habsB, hbd⟩ := window_frame_facts (nb := none) hLF hLa hLb
    hLB hnd hb (by simp [hg]) hnext (fun j hja hjb hji _ => hother j hja hjb hji)
    (fun o ho => by cases ho) (fun o ho => by cases ho) hfr
  have hsucc := window_succ (nb := none) hLa hLb hnext (fun j hja hjb hji _ => hother j hja hjb hji)
    (fun o _ ho => by cases ho)
  refine ⟨h', hrun, hfr, hbd, ?_⟩
  have harr : rotateLeafLeft (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
      csF.length =
      ((setSep es csF.length newFirst.1).map Prod.fst,
        (csF ++ a :: b :: csB).map (absF (d + 1) h')) := by
    simp only [rotateLeafLeft, List.getElem?_map, getElem?_window_fst, getElem?_window_snd,
      Option.map_some, absF_of_some (absNode_leaf hga d), absF_of_some (absNode_leaf hgb d)]
    rw [map_fst_setSep _ _ _ hj, map_window (absF (d + 1) h) (absF (d + 1) h') csF csB a b
      (fun c hc => by simp [absF, habsF c hc]) (fun c hc => by simp [absF, habsB c hc]),
      absF_of_some (absNode_leaf hga' d), absF_of_some (absNode_leaf hgb' d)]
  rw [harr]
  have hmid : c0 :: (setSep es csF.length newFirst.1).map (·.2) = csF ++ [a, b] ++ csB := by
    rw [show (fun x : K × NodeId => x.2) = Prod.snd from rfl, map_snd_setSep, hcs]; simp
  have hlinks : ∀ i ∈ lvF ++ ([a] ++ ([b] ++ lvB)), ∀ kvs p n, h.get i = some (.leaf kvs p n) →
      ∃ kvs', h'.get i = some (.leaf kvs' p n) := by
    intro i _ kvs p n hgi
    by_cases hia : i = a
    · subst hia; rw [hga] at hgi; cases hgi; exact ⟨_, hga'⟩
    by_cases hib : i = b
    · subst hib; rw [hgb] at hgi; cases hgi; exact ⟨_, hgb'⟩
    have hii : i ≠ id := fun heq => by subst heq; rw [hg] at hgi; cases hgi
    exact ⟨kvs, by rw [hother i hia hib hii]; exact hgi⟩
  have hl' := linked_congr_links hlinks hl
  simp only [List.cons_append, List.nil_append] at hl' hsucc ⊢
  have := window_reassemble (mid := [a, b]) (Lmid := [a, b]) (lvmid := [a, b]) (lvb := [b])
    hcs hLF hLa hLb hLB hlvF hlva hlvB hall hnd hgid' hmid
    (by simp [reachChildren_cons, reachIds.reachChildren, reachIds_leaf hga', reachIds_leaf hgb'])
    (by simp [leafChildren_cons, leafIds.leafChildren, leafIds_leaf hga', leafIds_leaf hgb'])
    (fun c hc => by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc <;> rw [hc]
      · exact ⟨_, absNode_leaf hga' d⟩
      · exact ⟨_, absNode_leaf hgb' d⟩)
    (by simp [hab]) (fun i hi => by simpa using hi) (fun i hi hni => absurd (by simpa using hi) hni)
    (by simp) rfl hsame (by simpa using hl') hframe (by simpa using hsucc)
  simpa using this

theorem mergeLeafPairH_sim {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0)
    {L R : Leaf K V} {pa na pb nb : Option NodeId}
    (hga : h.get a = some (.leaf L pa na)) (hgb : h.get b = some (.leaf R pb nb)) :
    RepairSim d h id (LF ++ (La ++ (Lb ++ LB))) (lvF ++ (lva ++ (lvb ++ lvB))) prev0 next0
      (mergeLeafPairH h id csF.length)
      (mergeLeafPair (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
        csF.length) := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := W.leaf_shape hga hgb
  obtain ⟨hab, hai, hbi⟩ := W.distinct
  obtain ⟨rfl, rfl, hnb⟩ := W.leaf_links hga hgb
  obtain ⟨hg, hcs, hLF, hLa, hLb, hLB, hlvF, hlva, hlvb, hlvB, hall, hnd, hb, hl, hnext⟩ := W
  have ha : childAt c0 es csF.length = some a := by rw [childAt, hcs, getElem?_window_fst]
  have hb' : childAt c0 es (csF.length + 1) = some b := by rw [childAt, hcs, getElem?_window_snd]
  have hj : csF.length < es.length := by
    have := congrArg List.length hcs; simp at this; omega
  obtain ⟨hidnb, hndbelow⟩ := List.nodup_cons.mp hnd
  have hcs' : c0 :: es.map Prod.snd = csF ++ a :: b :: csB := hcs
  have hlvBsub : lvB.Sublist LB := ((leaf_facts (d + 1)).2 h csB LB lvB hLB hlvB).2
  have hlvFsub : lvF.Sublist LF := ((leaf_facts (d + 1)).2 h csF LF lvF hLF hlvF).2
  have hW := nodup_mid_disjoint (l1 := LF) (m := [a] ++ [b]) (l2 := LB) (by simpa using hndbelow)
  have hFB : ∀ x ∈ LF, x ∉ LB := by
    intro x hx hx'
    rw [nodup_append_iff] at hndbelow
    exact hndbelow.2.2 x hx x (by simp [hx']) rfl
  have hLBne : ∀ x ∈ LB, x ≠ a ∧ x ≠ b ∧ x ≠ id :=
    fun x hx => ⟨fun heq => hW a (by simp) (heq ▸ List.mem_append_right _ hx),
      fun heq => hW b (by simp) (heq ▸ List.mem_append_right _ hx),
      fun heq => hidnb (heq ▸ (by simp [hx]))⟩
  -- whoever `nb` names: a leaf, distinct from `a`, `b`, `id`; the first
  -- leaf after the window when there is one, the successor otherwise
  have hnbfacts : ∀ o, nb = some o → o ≠ a ∧ o ≠ b ∧ o ≠ id ∧
      (∃ O po no, h.get o = some (.leaf O po no)) ∧
      ((lvB.head? = some o ∧ o ∈ LB) ∨ (lvB = [] ∧ next0 = some o)) := by
    intro o ho
    cases lvB with
    | nil =>
      simp only [List.head?_nil, Option.none_or] at hnb
      subst hnb
      obtain ⟨hout, O, n, hgo⟩ := hnext o ho
      exact ⟨fun heq => by subst heq; exact hout (by simp),
        fun heq => by subst heq; exact hout (by simp),
        fun heq => by subst heq; exact hout (by simp), ⟨O, _, n, hgo⟩, Or.inr ⟨rfl, ho⟩⟩
    | cons x rest =>
      simp only [List.head?_cons, Option.some_or] at hnb
      have hox : o = x := by rw [hnb] at ho; exact (Option.some.inj ho).symm
      subst hox
      have hxLB : o ∈ LB := hlvBsub.subset List.mem_cons_self
      obtain ⟨h1, h2, h3⟩ := hLBne o hxLB
      refine ⟨h1, h2, h3, ?_, Or.inl ⟨rfl, hxLB⟩⟩
      have hl2 := hl
      have : lvF ++ ([a] ++ ([b] ++ o :: rest)) = (lvF ++ [a] ++ [b]) ++ o :: rest := by simp
      rw [this] at hl2
      obtain ⟨kvs, hgo⟩ := linked_split_mid hl2
      exact ⟨kvs, _, _, hgo⟩
  have hnbmem : ∀ o, nb = some o → o ∈ LF ++ ([a] ++ ([b] ++ LB)) ∨ next0 = some o := by
    intro o ho
    rcases (hnbfacts o ho).2.2.2.2 with ⟨_, hLB'⟩ | ⟨_, hn⟩
    · exact Or.inl (by simp [hLB'])
    · exact Or.inr hn
  obtain ⟨h', hrun, hga', hgb', hgid', hgo', hother, hfr⟩ :=
    mergeLeafPairH_spec hg ha hb' hga hgb hab hai hbi
      (fun o ho => let f := hnbfacts o ho; ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1⟩)
  obtain ⟨hsame, hframe, habsF, habsB, hbd⟩ := window_frame_facts (nb := nb) hLF hLa hLb
    hLB hnd hb (by simp [hg]) hnext hother
    (fun o ho => by
      obtain ⟨_, _, _, ⟨O, po, no, hgo⟩, _⟩ := hnbfacts o ho
      exact ⟨O, po, some a, no, hgo, hgo' o O po no ho hgo⟩)
    hnbmem hfr
  refine ⟨h', hrun, hfr, hbd, ?_⟩
  have harr : mergeLeafPair (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
      csF.length =
      ((es.eraseIdx csF.length).map Prod.fst, (csF ++ a :: csB).map (absF (d + 1) h')) := by
    simp only [mergeLeafPair, List.getElem?_map, getElem?_window_fst, getElem?_window_snd,
      Option.map_some, absF_of_some (absNode_leaf hga d), absF_of_some (absNode_leaf hgb d)]
    rw [map_eraseIdx, map_window_erase (absF (d + 1) h) (absF (d + 1) h') csF csB a b
      (fun c hc => by simp [absF, habsF c hc]) (fun c hc => by simp [absF, habsB c hc]),
      absF_of_some (absNode_leaf hga' d)]
  rw [harr]
  have hmid : c0 :: (es.eraseIdx csF.length).map (·.2) = csF ++ [a] ++ csB := by
    rw [show (fun x : K × NodeId => x.2) = Prod.snd from rfl, cons_map_snd_eraseIdx, hcs',
      eraseIdx_window2]
    simp
  -- the chain: `b` drops out
  have hl' : Linked h' prev0 (lvF ++ ([a] ++ lvB)) next0 := by
    have hl2 := hl
    have : lvF ++ ([a] ++ ([b] ++ lvB)) = lvF ++ a :: b :: lvB := by simp
    rw [this] at hl2
    have := linked_erase (h' := h') (L1 := lvF) (L2 := lvB) hl2
      (fun La' pa' hga2 => by
        rw [hga] at hga2; cases hga2
        exact ⟨L ++ R, by rw [hga', hnb]⟩)
      (fun i hi => by
        have hiLF : i ∈ LF := hlvFsub.subset hi
        refine hother i (fun heq => hW a (by simp) (heq ▸ List.mem_append_left _ hiLF))
          (fun heq => hW b (by simp) (heq ▸ List.mem_append_left _ hiLF))
          (fun heq => hidnb (heq ▸ (by simp [hiLF]))) (fun hnbi => ?_)
        rcases (hnbfacts i hnbi).2.2.2.2 with ⟨_, hiLB⟩ | ⟨_, hn⟩
        · exact hFB i hiLF hiLB
        · exact (hnext i hn).1 (by simp [hiLF]))
      (fun o rest hrest O n hgo => by
        subst hrest
        simp only [List.head?_cons, Option.some_or] at hnb
        exact hgo' o O (some b) n hnb hgo)
      (fun o rest hrest i hi => by
        subst hrest
        simp only [List.head?_cons, Option.some_or] at hnb
        have hiLB : i ∈ LB := hlvBsub.subset (List.mem_cons_of_mem _ hi)
        obtain ⟨h1, h2, h3⟩ := hLBne i hiLB
        have hndlvB : (o :: rest).Nodup := by
          rw [nodup_append_iff, nodup_append_iff, nodup_append_iff] at hndbelow
          exact hndbelow.2.1.2.1.2.1.sublist hlvBsub
        have hoi : o ≠ i := fun heq => (List.nodup_cons.mp hndlvB).1 (heq ▸ hi)
        exact hother i h1 h2 h3 (fun heq => hoi (Option.some.inj (hnb.symm.trans heq))))
    simpa using this
  have hsucc : ∀ o O p n, next0 = some o → h.get o = some (.leaf O p n) →
      h'.get o = some (.leaf O ((lvF ++ ([a] ++ lvB)).getLast?.or prev0) n) := by
    intro o O p n ho hgo
    cases lvB with
    | nil =>
      simp only [List.head?_nil, Option.none_or] at hnb
      rw [hnb] at hgo'
      have := hgo' o O p n ho hgo
      simpa [List.getLast?_append] using this
    | cons x rest =>
      simp only [List.head?_cons, Option.some_or] at hnb
      have hs := window_succ (nb := nb) hLa hLb hnext hother
        (fun o' ho' hnbo' => by
          have hxLB : x ∈ LB := hlvBsub.subset List.mem_cons_self
          have : o' = x := Option.some.inj (hnbo'.symm.trans hnb)
          subst this
          exact (hnext o' ho').1 (by simp [hxLB])) o O p n ho hgo
      rw [getLast?_append_of_ne_nil _ (by simp), getLast?_append_of_ne_nil _ (by simp),
        getLast?_append_of_ne_nil _ (by simp)] at hs
      rw [getLast?_append_of_ne_nil _ (by simp), getLast?_append_of_ne_nil _ (by simp)]
      exact hs
  have := window_reassemble (mid := [a]) (Lmid := [a]) (lvmid := [a]) (lvb := [b])
    hcs hLF hLa hLb hLB hlvF hlva hlvB hall hnd hgid' hmid
    (by simp [reachChildren_cons, reachIds.reachChildren, reachIds_leaf hga'])
    (by simp [leafChildren_cons, leafIds.leafChildren, leafIds_leaf hga'])
    (fun c hc => by rw [List.mem_singleton.mp hc]; exact ⟨_, absNode_leaf hga' d⟩)
    (by simp) (fun i hi => by simp at hi; simp [hi])
    (fun i hi hni => by
      simp at hi hni
      rcases hi with hi | hi
      · exact absurd hi hni
      · rw [hi]; exact hgb')
    (by simp) rfl hsame (by simpa using hl') hframe (by simpa using hsucc)
  simpa using this

/-! ### The branch repairs -/

/-- A branch record in entry form, once its children abstract. -/
theorem absNode_branch_map {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    (hg : h.get id = some (.branch c0 es))
    (hall : ∀ c ∈ c0 :: es.map (·.2), ∃ t, absNode d h c = some t) :
    absNode (d + 1) h id =
      some (.branch (absF d h c0) (es.map fun e => (e.1, absF d h e.2))) := by
  rw [absNode_branch hg]
  obtain ⟨t0, ht0⟩ := hall c0 List.mem_cons_self
  rw [ht0, Option.bind_some, absEntries_of_all_some (fun e he =>
    hall e.2 (List.mem_cons_of_mem _ (List.mem_map_of_mem he))), Option.bind_some,
    absF_of_some ht0]

/-- A branch that abstracts has children that abstract. -/
theorem abs_branch_children {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {t : Node K V} (hg : h.get id = some (.branch c0 es)) (ht : absNode (d + 1) h id = some t) :
    ∀ c ∈ c0 :: es.map (·.2), ∃ t, absNode d h c = some t := by
  rw [absNode_branch hg] at ht
  cases h0 : absNode d h c0 <;> rw [h0] at ht
  · cases ht
  · cases he : absNode.absEntries d h es <;> rw [he] at ht
    · cases ht
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨_, h0⟩
      · obtain ⟨e, he', rfl⟩ := List.mem_map.mp hc
        exact absEntries_child_some he e he'

/-- Under `h'`, the abstraction of a list of untouched children. -/
theorem map_absF_congr {d : Nat} {h h' : Heap K V} {cs : List NodeId}
    (hsame : ∀ c ∈ cs, absNode d h' c = absNode d h c) :
    cs.map (absF d h') = cs.map (absF d h) :=
  List.map_congr_left (fun c hc => by simp [absF, hsame c hc])

theorem map_entries_congr {d : Nat} {h h' : Heap K V} {es : List (K × NodeId)}
    (hsame : ∀ c ∈ es.map (·.2), absNode d h' c = absNode d h c) :
    (es.map fun e => (e.1, absF d h' e.2)) = es.map fun e => (e.1, absF d h e.2) :=
  List.map_congr_left (fun e he => by simp [absF, hsame e.2 (List.mem_map_of_mem he)])

/-- Two adjacent branch children of a window: their walks split as
`a :: LA`, `b :: LB'`; a repair that rewrites only `a`, `b`, `id` leaves
every grandchild and every leaf in place. -/
theorem branch_window_facts {d : Nat} {h h' : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0)
    {lc0 rc0 : NodeId} {les res : List (K × NodeId)}
    (hga : h.get a = some (.branch lc0 les)) (hgb : h.get b = some (.branch rc0 res))
    (hother : ∀ j, j ≠ a → j ≠ b → j ≠ id → h'.get j = h.get j) :
    ∃ LA LB', La = a :: LA ∧ Lb = b :: LB' ∧
      reachIds.reachChildren d h (lc0 :: les.map (·.2)) = some LA ∧
      reachIds.reachChildren d h (rc0 :: res.map (·.2)) = some LB' ∧
      leafIds.leafChildren d h (lc0 :: les.map (·.2)) = some lva ∧
      leafIds.leafChildren d h (rc0 :: res.map (·.2)) = some lvb ∧
      (∀ c ∈ lc0 :: les.map (·.2), ∃ t, absNode d h c = some t) ∧
      (∀ c ∈ rc0 :: res.map (·.2), ∃ t, absNode d h c = some t) ∧
      (∀ i ∈ LA ++ LB', h'.get i = h.get i) ∧
      (∀ i ∈ lvF ++ (lva ++ (lvb ++ lvB)), h'.get i = h.get i) := by
  obtain ⟨hab, hai, hbi⟩ := W.distinct
  have hLa := W.hLa; have hLb := W.hLb; have hlva := W.hlva; have hlvb := W.hlvb
  rw [reachIds_branch hga] at hLa; rw [reachIds_branch hgb] at hLb
  rw [leafIds_branch hga] at hlva; rw [leafIds_branch hgb] at hlvb
  rcases hA : reachIds.reachChildren d h (lc0 :: les.map (·.2)) with _ | LA
  · rw [hA] at hLa; cases hLa
  rcases hB : reachIds.reachChildren d h (rc0 :: res.map (·.2)) with _ | LB'
  · rw [hB] at hLb; cases hLb
  rw [hA] at hLa; rw [hB] at hLb
  simp only [Option.map_some, Option.some.injEq] at hLa hLb
  subst hLa; subst hLb
  obtain ⟨hidnb, hndbelow⟩ := List.nodup_cons.mp W.hnd
  have hW := nodup_mid_disjoint (l1 := LF) (m := (a :: LA) ++ (b :: LB')) (l2 := LB)
    (by simpa using hndbelow)
  have hndmid : ((a :: LA) ++ (b :: LB')).Nodup := by
    rw [nodup_append_iff, nodup_append_iff, nodup_append_iff] at hndbelow
    rw [nodup_append_iff]
    exact ⟨hndbelow.2.1.1, hndbelow.2.1.2.1.1, fun x hx y hy hxy =>
      hndbelow.2.1.2.2 x hx y (List.mem_append_left _ hy) hxy⟩
  obtain ⟨ta, hta⟩ := W.hall a (by rw [W.hcs]; simp)
  obtain ⟨tb, htb⟩ := W.hall b (by rw [W.hcs]; simp)
  refine ⟨LA, LB', rfl, rfl, hA, hB, hlva, hlvb, abs_branch_children hga hta,
    abs_branch_children hgb htb, ?_, ?_⟩
  · intro i hi
    have hi' : i ∈ (a :: LA) ++ (b :: LB') := by
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (List.mem_cons_of_mem _ hi)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hi)
    have hia : i ≠ a := by
      intro heq; subst heq
      rcases List.mem_append.mp hi with hi | hi
      · exact (List.nodup_cons.mp (nodup_append_iff _ _ |>.mp hndmid).1).1 hi
      · exact (nodup_append_iff _ _ |>.mp hndmid).2.2 i List.mem_cons_self i
          (List.mem_cons_of_mem _ hi) rfl
    have hib : i ≠ b := by
      intro heq; subst heq
      rcases List.mem_append.mp hi with hi | hi
      · exact (nodup_append_iff _ _ |>.mp hndmid).2.2 i (List.mem_cons_of_mem _ hi) i
          List.mem_cons_self rfl
      · exact (List.nodup_cons.mp (nodup_append_iff _ _ |>.mp hndmid).2.1).1 hi
    have hmem : i ∈ LF ++ ((a :: LA) ++ ((b :: LB') ++ LB)) := by
      refine List.mem_append_right LF ?_
      rcases List.mem_append.mp hi' with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (List.mem_append_left _ h1)
    have hii : i ≠ id := fun heq => by subst heq; exact hidnb hmem
    exact hother i hia hib hii
  · intro i hi
    obtain ⟨kvs, p, n, hgi⟩ := linked_mem_leaf W.hl hi
    have hia : i ≠ a := fun heq => by subst heq; rw [hga] at hgi; cases hgi
    have hib : i ≠ b := fun heq => by subst heq; rw [hgb] at hgi; cases hgi
    have hii : i ≠ id := fun heq => by subst heq; rw [W.hg] at hgi; cases hgi
    exact hother i hia hib hii

/-- Splitting a children walk at a known point. -/
theorem reachChildren_split {d : Nat} {h : Heap K V} {l1 l2 L : List NodeId}
    (hL : reachIds.reachChildren d h (l1 ++ l2) = some L) :
    ∃ L1 L2, reachIds.reachChildren d h l1 = some L1 ∧ reachIds.reachChildren d h l2 = some L2 ∧
      L = L1 ++ L2 := by
  rw [reachChildren_append] at hL
  rcases h1 : reachIds.reachChildren d h l1 with _ | L1
  · rw [h1] at hL; cases hL
  rcases h2 : reachIds.reachChildren d h l2 with _ | L2
  · rw [h1, h2] at hL; cases hL
  rw [h1, h2] at hL
  simp only [Option.bind_some, Option.some.injEq] at hL
  exact ⟨L1, L2, rfl, rfl, hL.symm⟩

theorem leafChildren_split {d : Nat} {h : Heap K V} {l1 l2 L : List NodeId}
    (hL : leafIds.leafChildren d h (l1 ++ l2) = some L) :
    ∃ L1 L2, leafIds.leafChildren d h l1 = some L1 ∧ leafIds.leafChildren d h l2 = some L2 ∧
      L = L1 ++ L2 := by
  rw [leafChildren_append] at hL
  rcases h1 : leafIds.leafChildren d h l1 with _ | L1
  · rw [h1] at hL; cases hL
  rcases h2 : leafIds.leafChildren d h l2 with _ | L2
  · rw [h1, h2] at hL; cases hL
  rw [h1, h2] at hL
  simp only [Option.bind_some, Option.some.injEq] at hL
  exact ⟨L1, L2, rfl, rfl, hL.symm⟩

theorem reachChildren_singleton {d : Nat} {h : Heap K V} {c : NodeId} {L : List NodeId}
    (hL : reachIds.reachChildren d h [c] = some L) : reachIds d h c = some L := by
  rw [reachChildren_cons] at hL
  rcases hc : reachIds d h c with _ | Lc
  · rw [hc] at hL; cases hL
  rw [hc] at hL
  simp only [reachIds.reachChildren, Option.bind_some, List.append_nil, Option.some.injEq] at hL
  rw [hL]

theorem leafChildren_singleton {d : Nat} {h : Heap K V} {c : NodeId} {L : List NodeId}
    (hL : leafIds.leafChildren d h [c] = some L) : leafIds d h c = some L := by
  rw [leafChildren_cons] at hL
  rcases hc : leafIds d h c with _ | Lc
  · rw [hc] at hL; cases hL
  rw [hc] at hL
  simp only [leafIds.leafChildren, Option.bind_some, List.append_nil, Option.some.injEq] at hL
  rw [hL]

theorem reachChildren_join {d : Nat} {h : Heap K V} {l1 l2 L1 L2 : List NodeId}
    (h1 : reachIds.reachChildren d h l1 = some L1) (h2 : reachIds.reachChildren d h l2 = some L2) :
    reachIds.reachChildren d h (l1 ++ l2) = some (L1 ++ L2) := by
  rw [reachChildren_append, h1, h2]; rfl

theorem leafChildren_join {d : Nat} {h : Heap K V} {l1 l2 L1 L2 : List NodeId}
    (h1 : leafIds.leafChildren d h l1 = some L1) (h2 : leafIds.leafChildren d h l2 = some L2) :
    leafIds.leafChildren d h (l1 ++ l2) = some (L1 ++ L2) := by
  rw [leafChildren_append, h1, h2]; rfl

theorem rotateBranchRightH_sim {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0)
    {lc0 rc0 : NodeId} {les res : List (K × NodeId)}
    (hga : h.get a = some (.branch lc0 les)) (hgb : h.get b = some (.branch rc0 res))
    (hles : les ≠ []) :
    RepairSim d h id (LF ++ (La ++ (Lb ++ LB))) (lvF ++ (lva ++ (lvb ++ lvB))) prev0 next0
      (rotateBranchRightH h id csF.length)
      (rotateBranchRight (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
        csF.length) := by
  obtain ⟨hab, hai, hbi⟩ := W.distinct
  have ha := W.ha; have hb' := W.hb'; have hj := W.idx_lt
  obtain ⟨sep, hsep⟩ : ∃ sep, (es.map Prod.fst)[csF.length]? = some sep := by
    rw [List.getElem?_eq_getElem (by simpa using hj)]; exact ⟨_, rfl⟩
  obtain ⟨L0, pm, rfl⟩ : ∃ L0 pm, les = L0 ++ [pm] := by
    obtain ⟨pm, hpm⟩ := Option.ne_none_iff_exists'.mp
      (fun heq => hles (List.getLast?_eq_none_iff.mp heq))
    obtain ⟨L0, hL0⟩ := List.getLast?_eq_some_iff.mp hpm
    exact ⟨L0, pm, hL0⟩
  obtain ⟨promoted, m⟩ := pm
  have hlast : (L0 ++ [(promoted, m)]).getLast? = some (promoted, m) := by simp
  obtain ⟨h', hrun, hga', hgb', hgid', hother, hfr⟩ :=
    rotateBranchRightH_spec W.hg ha hb' hsep hga hgb hab hai hbi hlast
  rw [List.dropLast_concat] at hga'
  obtain ⟨LA, LB', rfl, rfl, hA, hB, hlvA, hlvB', hallA, hallB, hgc, hleaves⟩ :=
    branch_window_facts W hga hgb hother
  obtain ⟨hg, hcs, hLF, hLa, hLb, hLB, hlvF, hlva, hlvb, hlvB, hall, hnd, hb, hl, hnext⟩ := W
  obtain ⟨hsame, hframe, habsF, habsB, hbd⟩ := window_frame_facts (nb := none) hLF hLa hLb
    hLB hnd hb (by simp [hg]) hnext (fun j hja hjb hji _ => hother j hja hjb hji)
    (fun o ho => by cases ho) (fun o ho => by cases ho) hfr
  have hsucc := window_succ (nb := none) hLa hLb hnext (fun j hja hjb hji _ => hother j hja hjb hji)
    (fun o _ ho => by cases ho)
  refine ⟨h', hrun, hfr, hbd, ?_⟩
  -- the grandchildren, split at the moved child
  have hsplitA : lc0 :: (L0 ++ [(promoted, m)]).map (·.2) = (lc0 :: L0.map (·.2)) ++ [m] := by simp
  rw [hsplitA] at hA hlvA hallA
  obtain ⟨LA0, Lm, hA0, hAm, rfl⟩ := reachChildren_split hA
  obtain ⟨lvA0, lvm, hlvA0, hlvAm, rfl⟩ := leafChildren_split hlvA
  have hAm' := reachChildren_singleton hAm
  have hlvAm' := leafChildren_singleton hlvAm
  have hgc' : ∀ i ∈ (LA0 ++ Lm) ++ LB', SameContent (h.get i) (h'.get i) :=
    fun i hi => sameContent_of_eq (hgc i hi)
  obtain ⟨hA0', habsA0, hlvA0'⟩ := children_congr d (lc0 :: L0.map (·.2)) LA0 hA0
    (fun i hi => hgc' i (List.mem_append_left _ (List.mem_append_left _ hi)))
  obtain ⟨hAm'', habsm, hlvm'⟩ := walks_congr d h h' m Lm hAm'
    (fun i hi => hgc' i (List.mem_append_left _ (List.mem_append_right _ hi)))
  obtain ⟨hB', habsB', hlvB''⟩ := children_congr d (rc0 :: res.map (·.2)) LB' hB
    (fun i hi => hgc' i (List.mem_append_right _ hi))
  rw [hlvA0] at hlvA0'; rw [hlvAm'] at hlvm'; rw [hlvB'] at hlvB''
  -- the new children lists walk under `h'`
  have hcsA' : lc0 :: L0.map (·.2) = lc0 :: L0.map (·.2) := rfl
  have hcsB' : m :: ((sep, rc0) :: res).map (·.2) = [m] ++ (rc0 :: res.map (·.2)) := by simp
  have hreachA' : reachIds.reachChildren d h' (lc0 :: L0.map (·.2)) = some LA0 := hA0'
  have hreachB' : reachIds.reachChildren d h' (m :: ((sep, rc0) :: res).map (·.2)) =
      some (Lm ++ LB') := by
    rw [hcsB']; exact reachChildren_join (by simp [reachChildren_cons, reachIds.reachChildren, hAm'']) hB'
  have hlvA' : leafIds.leafChildren d h' (lc0 :: L0.map (·.2)) = some lvA0 := hlvA0'
  have hlvBn : leafIds.leafChildren d h' (m :: ((sep, rc0) :: res).map (·.2)) =
      some (lvm ++ lvb) := by
    rw [hcsB']; exact leafChildren_join (by simp [leafChildren_cons, leafIds.leafChildren, hlvm']) hlvB''
  have hallA' : ∀ c ∈ lc0 :: L0.map (·.2), ∃ t, absNode d h' c = some t := fun c hc => by
    rw [habsA0 c hc]; exact hallA c (List.mem_append_left _ hc)
  have hallB' : ∀ c ∈ m :: ((sep, rc0) :: res).map (·.2), ∃ t, absNode d h' c = some t := by
    intro c hc
    rw [hcsB'] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [List.mem_singleton.mp hc, habsm]; exact hallA m (by simp)
    · rw [habsB' c hc]; exact hallB c hc
  have hsubA := sub_branch_mk hga' hreachA' hlvA' hallA'
  have hsubB := sub_branch_mk hgb' hreachB' hlvBn hallB'
  -- the tree side
  have hcs' : c0 :: es.map Prod.snd = csF ++ a :: b :: csB := hcs
  have harr : rotateBranchRight (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
      csF.length =
      ((setSep es csF.length promoted).map Prod.fst,
        (csF ++ a :: b :: csB).map (absF (d + 1) h')) := by
    have hlesLast : ((L0 ++ [(promoted, m)]).map fun e => (e.1, absF d h e.2)).getLast? =
        some (promoted, absF d h m) := by simp
    have hlesDrop : ((L0 ++ [(promoted, m)]).map fun e => (e.1, absF d h e.2)).dropLast =
        L0.map fun e => (e.1, absF d h e.2) := by simp
    simp only [rotateBranchRight, List.getElem?_map, getElem?_window_fst, getElem?_window_snd,
      Option.map_some, hsep, absF_of_some (absNode_branch_map hga (by rw [hsplitA]; exact hallA)),
      absF_of_some (absNode_branch_map hgb hallB), hlesLast, hlesDrop]
    rw [map_fst_setSep _ _ _ hj, map_window (absF (d + 1) h) (absF (d + 1) h') csF csB a b
      (fun c hc => by simp [absF, habsF c hc]) (fun c hc => by simp [absF, habsB c hc]),
      absF_of_some (absNode_branch_map hga' hallA'), absF_of_some (absNode_branch_map hgb' hallB')]
    have hmapL0 : (L0.map fun e => (e.1, absF d h' e.2)) = L0.map fun e => (e.1, absF d h e.2) :=
      map_entries_congr (fun c hc => habsA0 c (List.mem_cons_of_mem _ hc))
    have hmapRes : (res.map fun e => (e.1, absF d h' e.2)) = res.map fun e => (e.1, absF d h e.2) :=
      map_entries_congr (fun c hc => habsB' c (List.mem_cons_of_mem _ hc))
    have h1 : absF d h' lc0 = absF d h lc0 := by simp [absF, habsA0 lc0 List.mem_cons_self]
    have h2 : absF d h' m = absF d h m := by simp [absF, habsm]
    have h3 : absF d h' rc0 = absF d h rc0 := by simp [absF, habsB' rc0 List.mem_cons_self]
    simp only [List.map_cons, hmapL0, hmapRes, h1, h2, h3]
  rw [harr]
  have hmid : c0 :: (setSep es csF.length promoted).map (·.2) = csF ++ [a, b] ++ csB := by
    rw [show (fun x : K × NodeId => x.2) = Prod.snd from rfl, map_snd_setSep, hcs']; simp
  have hl' : Linked h' prev0 (lvF ++ ((lvA0 ++ (lvm ++ lvb)) ++ lvB)) next0 := by
    have := linked_congr hleaves hl
    simpa [List.append_assoc] using this
  have hperm : ((a :: LA0) ++ (b :: (Lm ++ LB'))).Perm ((a :: (LA0 ++ Lm)) ++ (b :: LB')) := by
    simp only [List.cons_append, List.append_assoc]
    exact List.Perm.cons a (List.Perm.append_left LA0 List.perm_middle.symm)
  have hndab : ((a :: (LA0 ++ Lm)) ++ (b :: LB')).Nodup := by
    refine List.Nodup.sublist ?_ hnd
    refine List.Sublist.trans ?_ (List.sublist_cons_self id _)
    refine List.Sublist.trans ?_ (List.sublist_append_right LF _)
    rw [← List.append_assoc]; exact List.sublist_append_left _ _
  have hlvA0ne : lvA0 ≠ [] :=
    ((leaf_facts d).2 h (lc0 :: L0.map (·.2)) LA0 lvA0 hA0 hlvA0).1 (by simp)
  have := window_reassemble (mid := [a, b]) (Lmid := (a :: LA0) ++ (b :: (Lm ++ LB')))
    (lvmid := lvA0 ++ (lvm ++ lvb)) (lvb := lvb) hcs hLF hLa hLb hLB hlvF hlva hlvB hall hnd hgid' hmid
    (by
      rw [reachChildren_cons, reachIds_branch hga', hreachA', reachChildren_cons,
        reachIds_branch hgb', hreachB']
      simp [reachIds.reachChildren])
    (by
      rw [leafChildren_cons, leafIds_branch hga', hlvA', leafChildren_cons, leafIds_branch hgb',
        hlvBn]
      simp [leafIds.leafChildren])
    (fun c hc => by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc <;> rw [hc]
      · exact ⟨_, hsubA.abs⟩
      · exact ⟨_, hsubB.abs⟩)
    (hperm.nodup_iff.mpr hndab) (fun i hi => hperm.mem_iff.mp hi)
    (fun i hi hni => absurd (hperm.mem_iff.mpr hi) hni)
    (List.append_ne_nil_of_left_ne_nil hlvA0ne _)
    (by rw [head?_append_of_ne_nil _ hlvA0ne, head?_append_of_ne_nil _ hlvA0ne])
    hsame hl' hframe (by simpa [List.append_assoc] using hsucc)
  simpa using this

theorem rotateBranchLeftH_sim {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0)
    {lc0 rc0 : NodeId} {les res : List (K × NodeId)}
    (hga : h.get a = some (.branch lc0 les)) (hgb : h.get b = some (.branch rc0 res))
    (hres : res ≠ []) :
    RepairSim d h id (LF ++ (La ++ (Lb ++ LB))) (lvF ++ (lva ++ (lvb ++ lvB))) prev0 next0
      (rotateBranchLeftH h id csF.length)
      (rotateBranchLeft (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
        csF.length) := by
  obtain ⟨hab, hai, hbi⟩ := W.distinct
  have ha := W.ha; have hb' := W.hb'; have hj := W.idx_lt
  obtain ⟨sep, hsep⟩ : ∃ sep, (es.map Prod.fst)[csF.length]? = some sep := by
    rw [List.getElem?_eq_getElem (by simpa using hj)]; exact ⟨_, rfl⟩
  obtain ⟨⟨promoted, rch1⟩, rest, rfl⟩ : ∃ pr rest, res = pr :: rest := by
    cases res with
    | nil => exact absurd rfl hres
    | cons pr rest => exact ⟨pr, rest, rfl⟩
  obtain ⟨h', hrun, hga', hgb', hgid', hother, hfr⟩ :=
    rotateBranchLeftH_spec W.hg ha hb' hsep hga hgb hab hai hbi
  obtain ⟨LA, LB', rfl, rfl, hA, hB, hlvA, hlvB', hallA, hallB, hgc, hleaves⟩ :=
    branch_window_facts W hga hgb hother
  obtain ⟨hg, hcs, hLF, hLa, hLb, hLB, hlvF, hlva, hlvb, hlvB, hall, hnd, hb, hl, hnext⟩ := W
  obtain ⟨hsame, hframe, habsF, habsB, hbd⟩ := window_frame_facts (nb := none) hLF hLa hLb
    hLB hnd hb (by simp [hg]) hnext (fun j hja hjb hji _ => hother j hja hjb hji)
    (fun o ho => by cases ho) (fun o ho => by cases ho) hfr
  have hsucc := window_succ (nb := none) hLa hLb hnext (fun j hja hjb hji _ => hother j hja hjb hji)
    (fun o _ ho => by cases ho)
  refine ⟨h', hrun, hfr, hbd, ?_⟩
  -- the grandchildren of `b`, split after its first
  have hsplitB : rc0 :: ((promoted, rch1) :: rest).map (·.2) = [rc0] ++ (rch1 :: rest.map (·.2)) := by
    simp
  rw [hsplitB] at hB hlvB' hallB
  obtain ⟨Lr, LB1, hBr, hB1, rfl⟩ := reachChildren_split hB
  obtain ⟨lvr, lvB1, hlvBr, hlvB1, rfl⟩ := leafChildren_split hlvB'
  have hBr' := reachChildren_singleton hBr
  have hlvBr' := leafChildren_singleton hlvBr
  have hgc' : ∀ i ∈ LA ++ (Lr ++ LB1), SameContent (h.get i) (h'.get i) :=
    fun i hi => sameContent_of_eq (hgc i hi)
  obtain ⟨hA', habsA, hlvA'⟩ := children_congr d (lc0 :: les.map (·.2)) LA hA
    (fun i hi => hgc' i (List.mem_append_left _ hi))
  obtain ⟨hBr'', habsr, hlvr'⟩ := walks_congr d h h' rc0 Lr hBr'
    (fun i hi => hgc' i (List.mem_append_right _ (List.mem_append_left _ hi)))
  obtain ⟨hB1', habsB1, hlvB1'⟩ := children_congr d (rch1 :: rest.map (·.2)) LB1 hB1
    (fun i hi => hgc' i (List.mem_append_right _ (List.mem_append_right _ hi)))
  rw [hlvA] at hlvA'; rw [hlvBr'] at hlvr'; rw [hlvB1] at hlvB1'
  -- the new children lists walk under `h'`
  have hcsA' : lc0 :: (les ++ [(sep, rc0)]).map (·.2) = (lc0 :: les.map (·.2)) ++ [rc0] := by simp
  have hreachA' : reachIds.reachChildren d h' (lc0 :: (les ++ [(sep, rc0)]).map (·.2)) =
      some (LA ++ Lr) := by
    rw [hcsA']
    exact reachChildren_join hA' (by simp [reachChildren_cons, reachIds.reachChildren, hBr''])
  have hlvAn : leafIds.leafChildren d h' (lc0 :: (les ++ [(sep, rc0)]).map (·.2)) =
      some (lva ++ lvr) := by
    rw [hcsA']
    exact leafChildren_join hlvA' (by simp [leafChildren_cons, leafIds.leafChildren, hlvr'])
  have hreachB' : reachIds.reachChildren d h' (rch1 :: rest.map (·.2)) = some LB1 := hB1'
  have hlvBn : leafIds.leafChildren d h' (rch1 :: rest.map (·.2)) = some lvB1 := hlvB1'
  have hallA' : ∀ c ∈ lc0 :: (les ++ [(sep, rc0)]).map (·.2), ∃ t, absNode d h' c = some t := by
    intro c hc
    rw [hcsA'] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [habsA c hc]; exact hallA c hc
    · rw [List.mem_singleton.mp hc, habsr]; exact hallB rc0 (by simp)
  have hallB' : ∀ c ∈ rch1 :: rest.map (·.2), ∃ t, absNode d h' c = some t := fun c hc => by
    rw [habsB1 c hc]; exact hallB c (List.mem_append_right _ hc)
  have hsubA := sub_branch_mk hga' hreachA' hlvAn hallA'
  have hsubB := sub_branch_mk hgb' hreachB' hlvBn hallB'
  -- the tree side
  have hcs' : c0 :: es.map Prod.snd = csF ++ a :: b :: csB := hcs
  have harr : rotateBranchLeft (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
      csF.length =
      ((setSep es csF.length promoted).map Prod.fst,
        (csF ++ a :: b :: csB).map (absF (d + 1) h')) := by
    have hresMap : (((promoted, rch1) :: rest).map fun e => (e.1, absF d h e.2)) =
        (promoted, absF d h rch1) :: rest.map fun e => (e.1, absF d h e.2) := rfl
    simp only [rotateBranchLeft, List.getElem?_map, getElem?_window_fst, getElem?_window_snd,
      Option.map_some, hsep, absF_of_some (absNode_branch_map hga hallA),
      absF_of_some (absNode_branch_map hgb (by rw [hsplitB]; exact hallB)), hresMap]
    rw [map_fst_setSep _ _ _ hj, map_window (absF (d + 1) h) (absF (d + 1) h') csF csB a b
      (fun c hc => by simp [absF, habsF c hc]) (fun c hc => by simp [absF, habsB c hc]),
      absF_of_some (absNode_branch_map hga' hallA'), absF_of_some (absNode_branch_map hgb' hallB')]
    have hmapLes : (les.map fun e => (e.1, absF d h' e.2)) = les.map fun e => (e.1, absF d h e.2) :=
      map_entries_congr (fun c hc => habsA c (List.mem_cons_of_mem _ hc))
    have hmapRest : (rest.map fun e => (e.1, absF d h' e.2)) =
        rest.map fun e => (e.1, absF d h e.2) :=
      map_entries_congr (fun c hc => habsB1 c (List.mem_cons_of_mem _ hc))
    have h1 : absF d h' lc0 = absF d h lc0 := by simp [absF, habsA lc0 List.mem_cons_self]
    have h2 : absF d h' rc0 = absF d h rc0 := by simp [absF, habsr]
    have h3 : absF d h' rch1 = absF d h rch1 := by simp [absF, habsB1 rch1 List.mem_cons_self]
    simp only [List.map_append, List.map_cons, List.map_nil, hmapLes, hmapRest, h1, h2, h3]
  rw [harr]
  have hmid : c0 :: (setSep es csF.length promoted).map (·.2) = csF ++ [a, b] ++ csB := by
    rw [show (fun x : K × NodeId => x.2) = Prod.snd from rfl, map_snd_setSep, hcs']; simp
  have hl' : Linked h' prev0 (lvF ++ (((lva ++ lvr) ++ lvB1) ++ lvB)) next0 := by
    have := linked_congr hleaves hl
    simpa [List.append_assoc] using this
  have hperm : ((a :: (LA ++ Lr)) ++ (b :: LB1)).Perm ((a :: LA) ++ (b :: (Lr ++ LB1))) := by
    simp only [List.cons_append, List.append_assoc]
    exact List.Perm.cons a (List.Perm.append_left LA List.perm_middle)
  have hndab : ((a :: LA) ++ (b :: (Lr ++ LB1))).Nodup := by
    refine List.Nodup.sublist ?_ hnd
    refine List.Sublist.trans ?_ (List.sublist_cons_self id _)
    refine List.Sublist.trans ?_ (List.sublist_append_right LF _)
    rw [← List.append_assoc]; exact List.sublist_append_left _ _
  have hlvane : lva ≠ [] :=
    ((leaf_facts d).2 h (lc0 :: les.map (·.2)) LA lva hA hlvA).1 (by simp)
  have := window_reassemble (mid := [a, b]) (Lmid := (a :: (LA ++ Lr)) ++ (b :: LB1))
    (lvmid := (lva ++ lvr) ++ lvB1) (lvb := lvr ++ lvB1) hcs hLF hLa hLb hLB hlvF hlva hlvB hall hnd
    hgid' hmid
    (by
      rw [reachChildren_cons, reachIds_branch hga', hreachA', reachChildren_cons,
        reachIds_branch hgb', hreachB']
      simp [reachIds.reachChildren])
    (by
      rw [leafChildren_cons, leafIds_branch hga', hlvAn, leafChildren_cons, leafIds_branch hgb',
        hlvBn]
      simp [leafIds.leafChildren])
    (fun c hc => by
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc <;> rw [hc]
      · exact ⟨_, hsubA.abs⟩
      · exact ⟨_, hsubB.abs⟩)
    (hperm.nodup_iff.mpr hndab) (fun i hi => hperm.mem_iff.mp hi)
    (fun i hi hni => absurd (hperm.mem_iff.mpr hi) hni)
    (List.append_ne_nil_of_left_ne_nil (List.append_ne_nil_of_left_ne_nil hlvane _) _)
    (by rw [head?_append_of_ne_nil _ (List.append_ne_nil_of_left_ne_nil hlvane _),
      head?_append_of_ne_nil _ hlvane])
    hsame hl' hframe (by simpa [List.append_assoc] using hsucc)
  simpa using this

theorem mergeBranchPairH_sim {d : Nat} {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)}
    {csF csB : List NodeId} {a b : NodeId} {LF La Lb LB lvF lva lvb lvB : List NodeId}
    {prev0 next0 : Option NodeId}
    (W : WinCtx d h id c0 es csF csB a b LF La Lb LB lvF lva lvb lvB prev0 next0)
    {lc0 rc0 : NodeId} {les res : List (K × NodeId)}
    (hga : h.get a = some (.branch lc0 les)) (hgb : h.get b = some (.branch rc0 res)) :
    RepairSim d h id (LF ++ (La ++ (Lb ++ LB))) (lvF ++ (lva ++ (lvb ++ lvB))) prev0 next0
      (mergeBranchPairH h id csF.length)
      (mergeBranchPair (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
        csF.length) := by
  obtain ⟨hab, hai, hbi⟩ := W.distinct
  have ha := W.ha; have hb' := W.hb'; have hj := W.idx_lt
  obtain ⟨sep, hsep⟩ : ∃ sep, (es.map Prod.fst)[csF.length]? = some sep := by
    rw [List.getElem?_eq_getElem (by simpa using hj)]; exact ⟨_, rfl⟩
  obtain ⟨h', hrun, hga', hgb', hgid', hother, hfr⟩ :=
    mergeBranchPairH_spec W.hg ha hb' hsep hga hgb hab hai hbi
  obtain ⟨LA, LB', rfl, rfl, hA, hB, hlvA, hlvB', hallA, hallB, hgc, hleaves⟩ :=
    branch_window_facts W hga hgb hother
  obtain ⟨hg, hcs, hLF, hLa, hLb, hLB, hlvF, hlva, hlvb, hlvB, hall, hnd, hb, hl, hnext⟩ := W
  obtain ⟨hsame, hframe, habsF, habsB, hbd⟩ := window_frame_facts (nb := none) hLF hLa hLb
    hLB hnd hb (by simp [hg]) hnext (fun j hja hjb hji _ => hother j hja hjb hji)
    (fun o ho => by cases ho) (fun o ho => by cases ho) hfr
  have hsucc := window_succ (nb := none) hLa hLb hnext (fun j hja hjb hji _ => hother j hja hjb hji)
    (fun o _ ho => by cases ho)
  refine ⟨h', hrun, hfr, hbd, ?_⟩
  have hgc' : ∀ i ∈ LA ++ LB', SameContent (h.get i) (h'.get i) :=
    fun i hi => sameContent_of_eq (hgc i hi)
  obtain ⟨hA', habsA, hlvA'⟩ := children_congr d (lc0 :: les.map (·.2)) LA hA
    (fun i hi => hgc' i (List.mem_append_left _ hi))
  obtain ⟨hB', habsB', hlvB''⟩ := children_congr d (rc0 :: res.map (·.2)) LB' hB
    (fun i hi => hgc' i (List.mem_append_right _ hi))
  rw [hlvA] at hlvA'; rw [hlvB'] at hlvB''
  have hcsA' : lc0 :: (les ++ (sep, rc0) :: res).map (·.2) =
      (lc0 :: les.map (·.2)) ++ (rc0 :: res.map (·.2)) := by simp
  have hreachA' : reachIds.reachChildren d h' (lc0 :: (les ++ (sep, rc0) :: res).map (·.2)) =
      some (LA ++ LB') := by
    rw [hcsA']; exact reachChildren_join hA' hB'
  have hlvAn : leafIds.leafChildren d h' (lc0 :: (les ++ (sep, rc0) :: res).map (·.2)) =
      some (lva ++ lvb) := by
    rw [hcsA']; exact leafChildren_join hlvA' hlvB''
  have hallA' : ∀ c ∈ lc0 :: (les ++ (sep, rc0) :: res).map (·.2), ∃ t, absNode d h' c = some t := by
    intro c hc
    rw [hcsA'] at hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [habsA c hc]; exact hallA c hc
    · rw [habsB' c hc]; exact hallB c hc
  have hsubA := sub_branch_mk hga' hreachA' hlvAn hallA'
  have hcs' : c0 :: es.map Prod.snd = csF ++ a :: b :: csB := hcs
  have harr : mergeBranchPair (es.map Prod.fst) ((csF ++ a :: b :: csB).map (absF (d + 1) h))
      csF.length =
      ((es.eraseIdx csF.length).map Prod.fst, (csF ++ a :: csB).map (absF (d + 1) h')) := by
    simp only [mergeBranchPair, List.getElem?_map, getElem?_window_fst, getElem?_window_snd,
      Option.map_some, hsep, absF_of_some (absNode_branch_map hga hallA),
      absF_of_some (absNode_branch_map hgb hallB)]
    rw [map_eraseIdx, map_window_erase (absF (d + 1) h) (absF (d + 1) h') csF csB a b
      (fun c hc => by simp [absF, habsF c hc]) (fun c hc => by simp [absF, habsB c hc]),
      absF_of_some (absNode_branch_map hga' hallA')]
    have hmapLes : (les.map fun e => (e.1, absF d h' e.2)) = les.map fun e => (e.1, absF d h e.2) :=
      map_entries_congr (fun c hc => habsA c (List.mem_cons_of_mem _ hc))
    have hmapRes : (res.map fun e => (e.1, absF d h' e.2)) = res.map fun e => (e.1, absF d h e.2) :=
      map_entries_congr (fun c hc => habsB' c (List.mem_cons_of_mem _ hc))
    have h1 : absF d h' lc0 = absF d h lc0 := by simp [absF, habsA lc0 List.mem_cons_self]
    have h2 : absF d h' rc0 = absF d h rc0 := by simp [absF, habsB' rc0 List.mem_cons_self]
    simp only [List.map_append, List.map_cons, hmapLes, hmapRes, h1, h2]
  rw [harr]
  have hmid : c0 :: (es.eraseIdx csF.length).map (·.2) = csF ++ [a] ++ csB := by
    rw [show (fun x : K × NodeId => x.2) = Prod.snd from rfl, cons_map_snd_eraseIdx, hcs',
      eraseIdx_window2]
    simp
  have hl' : Linked h' prev0 (lvF ++ ((lva ++ lvb) ++ lvB)) next0 := by
    have := linked_congr hleaves hl
    simpa [List.append_assoc] using this
  have hsub : (a :: (LA ++ LB')).Sublist ((a :: LA) ++ (b :: LB')) := by
    simp only [List.cons_append]
    exact List.Sublist.cons₂ a ((List.Sublist.refl LA).append (List.sublist_cons_self b LB'))
  have hndab : ((a :: LA) ++ (b :: LB')).Nodup := by
    refine List.Nodup.sublist ?_ hnd
    refine List.Sublist.trans ?_ (List.sublist_cons_self id _)
    refine List.Sublist.trans ?_ (List.sublist_append_right LF _)
    rw [← List.append_assoc]; exact List.sublist_append_left _ _
  have hlvane : lva ≠ [] :=
    ((leaf_facts d).2 h (lc0 :: les.map (·.2)) LA lva hA hlvA).1 (by simp)
  have := window_reassemble (mid := [a]) (Lmid := a :: (LA ++ LB')) (lvmid := lva ++ lvb)
    (lvb := lvb) hcs hLF hLa hLb hLB hlvF hlva hlvB hall hnd hgid' hmid
    (by
      rw [reachChildren_cons, reachIds_branch hga', hreachA']
      simp [reachIds.reachChildren])
    (by
      rw [leafChildren_cons, leafIds_branch hga', hlvAn]
      simp [leafIds.leafChildren])
    (fun c hc => by rw [List.mem_singleton.mp hc]; exact ⟨_, hsubA.abs⟩)
    (hndab.sublist hsub) (fun i hi => hsub.subset hi)
    (fun i hi hni => by
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hi hni
      have : i = b := by
        rcases hi with hi | hi | hi | hi
        · exact absurd (Or.inl hi) hni
        · exact absurd (Or.inr (Or.inl hi)) hni
        · exact hi
        · exact absurd (Or.inr (Or.inr hi)) hni
      rw [this]; exact hgb')
    (List.append_ne_nil_of_left_ne_nil hlvane _)
    (by rw [head?_append_of_ne_nil _ hlvane])
    hsame hl' hframe (by simpa [List.append_assoc] using hsucc)
  simpa using this

end HeapRemove

end BPlusTree
