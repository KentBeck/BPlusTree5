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

end HeapRemove

end BPlusTree
