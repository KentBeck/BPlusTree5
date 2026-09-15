import BPlusTree.Proofs.HeapRead

/-!
# The heap model: `clear` and the ledger

The value-token accounting. The models are functional, so "dropped
twice" is not a thing they can say directly; what the Rust's ownership
discipline amounts to is a conservation law, and that they can say:
every entry ever inserted is, at every moment, in exactly one place: a
leaf slot, handed back to the caller by `insert` or `remove`, or dropped
by `clear`, and never in two.

Two pieces. `dropSubtreeH` (the `Drop` / `clear` path) frees exactly the
subtree's nodes, each once, so every slot's contents are dropped once:
on the heap model `free` faults on an id that is not allocated, so "no
fault" is "no double free", and "the store is empty afterwards" is "no
leak". Then a ledger over whole operation sequences: the heap model runs
any sequence of `insert`, `remove` and `clear` from the empty map without
faulting, hands back what the tree model hands back, and the tree model's
live entries plus everything handed back plus everything dropped is a
permutation of everything inserted.
-/

namespace BPlusTree

open Std

set_option linter.unusedSectionVars false

section HeapLedger

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-! ## `drop_subtree` -/

/-- Freeing a subtree frees exactly its ids, each once, and nothing else. -/
theorem dropSubtreeH_spec :
    ∀ (d fuel : Nat) (h : Heap K V) (id : NodeId) (ids : List NodeId), d ≤ fuel →
      reachIds d h id = some ids → ids.Nodup →
      ∃ h', dropSubtreeH fuel h id = some h' ∧ (∀ i ∈ ids, h'.get i = none) ∧
        (∀ i, i ∉ ids → h'.get i = h.get i) ∧ h'.fresh = h.fresh := by
  intro d
  induction d with
  | zero => intro fuel h id ids _ hr; simp [reachIds] at hr
  | succ d ih =>
    intro fuel h id ids hfuel hr hnd
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
    · simp [reachIds, hg] at hr
    · rw [reachIds_leaf hg] at hr
      cases hr
      obtain ⟨h', hf⟩ := Heap.free_some (h := h) (id := id) (by simp [hg])
      refine ⟨h', by simp [dropSubtreeH, hg, hf], ?_, ?_, Heap.fresh_free hf⟩
      · intro i hi; rw [List.mem_singleton.mp hi]; exact Heap.get_free_self hf
      · intro i hi; exact Heap.get_free_other hf (by simpa using hi)
    · rw [reachIds_branch hg] at hr
      rcases hb : reachIds.reachChildren d h (c0 :: es.map (·.2)) with _ | below
      · rw [hb] at hr; cases hr
      rw [hb] at hr
      simp only [Option.map_some, Option.some.injEq] at hr
      subst hr
      obtain ⟨hidnb, hndb⟩ := List.nodup_cons.mp hnd
      -- the children, one after another
      have hch : ∀ (es : List (K × NodeId)) (h1 : Heap K V) (L : List NodeId),
          reachIds.reachChildren d h1 (es.map (·.2)) = some L → L.Nodup →
          ∃ h2, dropSubtreeH.dropChildrenH f h1 es = some h2 ∧ (∀ i ∈ L, h2.get i = none) ∧
            (∀ i, i ∉ L → h2.get i = h1.get i) ∧ h2.fresh = h1.fresh := by
        intro es
        induction es with
        | nil =>
          intro h1 L hL _
          simp only [List.map_nil, reachIds.reachChildren, Option.some.injEq] at hL
          subst hL
          exact ⟨h1, by simp [dropSubtreeH.dropChildrenH], (fun i hi => by cases hi),
            (fun i _ => rfl), rfl⟩
        | cons e rest ihe =>
          intro h1 L hL hndL
          obtain ⟨s, c⟩ := e
          simp only [List.map_cons] at hL
          rw [reachChildren_cons] at hL
          rcases hLc : reachIds d h1 c with _ | Lc
          · rw [hLc] at hL; cases hL
          rcases hLr : reachIds.reachChildren d h1 (rest.map (·.2)) with _ | Lr
          · rw [hLc, hLr] at hL; cases hL
          rw [hLc, hLr] at hL
          simp only [Option.bind_some, Option.some.injEq] at hL
          subst hL
          rw [nodup_append_iff] at hndL
          obtain ⟨hndc, hndr, hdisj⟩ := hndL
          obtain ⟨h1', hd1, hfree1, hother1, hfr1⟩ := ih f h1 c Lc (by omega) hLc hndc
          have hsame : ∀ i ∈ Lr, SameContent (h1.get i) (h1'.get i) := fun i hi =>
            sameContent_of_eq (hother1 i (fun hin => hdisj i hin i hi rfl))
          obtain ⟨hLr', -, -⟩ := children_congr d (rest.map (·.2)) Lr hLr hsame
          obtain ⟨h2, hd2, hfree2, hother2, hfr2⟩ := ihe h1' Lr hLr' hndr
          refine ⟨h2, by simp [dropSubtreeH.dropChildrenH, hd1, hd2], ?_, ?_, hfr2.trans hfr1⟩
          · intro i hi
            rcases List.mem_append.mp hi with hi | hi
            · rw [hother2 i (fun hin => hdisj i hi i hin rfl)]; exact hfree1 i hi
            · exact hfree2 i hi
          · intro i hi
            simp only [List.mem_append, not_or] at hi
            rw [hother2 i hi.2, hother1 i hi.1]
      rw [reachChildren_cons] at hb
      rcases hL0 : reachIds d h c0 with _ | L0
      · rw [hL0] at hb; cases hb
      rcases hLr : reachIds.reachChildren d h (es.map (·.2)) with _ | Lr
      · rw [hL0, hLr] at hb; cases hb
      rw [hL0, hLr] at hb
      simp only [Option.bind_some, Option.some.injEq] at hb
      subst hb
      rw [nodup_append_iff] at hndb
      obtain ⟨hnd0, hndr, hdisj⟩ := hndb
      obtain ⟨h1, hd1, hfree1, hother1, hfr1⟩ := ih f h c0 L0 (by omega) hL0 hnd0
      have hsame : ∀ i ∈ Lr, SameContent (h.get i) (h1.get i) := fun i hi =>
        sameContent_of_eq (hother1 i (fun hin => hdisj i hin i hi rfl))
      obtain ⟨hLr', -, -⟩ := children_congr d (es.map (·.2)) Lr hLr hsame
      obtain ⟨h2, hd2, hfree2, hother2, hfr2⟩ := hch es h1 Lr hLr' hndr
      have hid2 : h2.get id = some (.branch c0 es) := by
        rw [hother2 id (fun hin => hidnb (List.mem_append_right _ hin)),
          hother1 id (fun hin => hidnb (List.mem_append_left _ hin))]
        exact hg
      obtain ⟨h3, hf3⟩ := Heap.free_some (h := h2) (id := id) (by simp [hid2])
      refine ⟨h3, ?_, ?_, ?_, by rw [Heap.fresh_free hf3, hfr2, hfr1]⟩
      · simp only [dropSubtreeH, hg, hd1, Option.bind_eq_bind, Option.bind_some, hd2, hf3]
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact Heap.get_free_self hf3
        have hii : i ≠ id := fun heq => hidnb (heq ▸ hi)
        rw [Heap.get_free_other hf3 hii]
        rcases List.mem_append.mp hi with hi | hi
        · rw [hother2 i (fun hin => hdisj i hi i hin rfl)]; exact hfree1 i hi
        · exact hfree2 i hi
      · intro i hi
        simp only [List.mem_cons, List.mem_append, not_or] at hi
        rw [Heap.get_free_other hf3 hi.1, hother2 i hi.2.2, hother1 i hi.2.1]

/-- `clear`: the store is empty afterwards, so every node was freed exactly
once and with it every slot's contents dropped exactly once. -/
theorem clearH_sim {d fuel : Nat} (hfuel : d + 1 ≤ fuel) {m : HeapMap K V} {t : Node K V}
    (hinv : HeapInv m d t) :
    ∃ h', clearH fuel m = some ⟨h', none, 0⟩ ∧ ∀ i, h'.get i = none := by
  obtain ⟨root, ids, lv, hroot, hsub, hnd, -, hdom, -, -⟩ := hinv
  obtain ⟨h', hd, hfree, hother, -⟩ := dropSubtreeH_spec (d + 1) fuel m.heap root ids hfuel
    hsub.reach hnd
  refine ⟨h', by simp [clearH, hroot, hd], fun i => ?_⟩
  by_cases hi : i ∈ ids
  · exact hfree i hi
  · rw [hother i hi]
    rcases hg : m.heap.get i with _ | r
    · rfl
    · exact absurd ((hdom i).mp (by simp [hg])) hi

/-! ## The empty map -/

theorem wf_empty_leaf (lc bc : Nat) : WF lc bc 0 true none none (Node.leaf ([] : Leaf K V)) :=
  ⟨List.Pairwise.nil, (fun _ h => by cases h), Nat.zero_le _, Or.inl rfl⟩

/-- A fresh empty leaf over an empty store is a heap map for the empty tree. -/
theorem heapInv_fresh_leaf {h : Heap K V} (hempty : ∀ i, h.get i = none) :
    HeapInv ⟨(h.alloc (.leaf [] none none)).2, some (h.alloc (.leaf [] none none)).1, 0⟩ 0
      (.leaf []) := by
  have hg := Heap.get_alloc_self h (.leaf ([] : Leaf K V) none none)
  refine ⟨h.fresh, [h.fresh], [h.fresh], rfl,
    ⟨absNode_leaf hg 0, reachIds_leaf hg 0, leafIds_leaf hg 0⟩, by simp,
    Heap.bounded_alloc _ (fun i hi => by rw [hempty i] at hi; cases hi), ?_,
    linked_singleton.mpr ⟨[], hg⟩, rfl⟩
  have hg' : (h.alloc (.leaf [] none none)).2.get h.fresh = some (.leaf ([] : Leaf K V) none none) := hg
  intro i
  by_cases hi : i = h.fresh
  · subst hi; simp [hg']
  · rw [Heap.get_alloc_other h _ hi, hempty i]; simp [hi]

theorem heapInv_new : HeapInv (HeapMap.new : HeapMap K V) 0 (.leaf []) :=
  heapInv_fresh_leaf (fun i => by simp [Heap.get, Heap.empty])

/-- `insert` on a rootless map is `insert` on a fresh root leaf. -/
theorem insertH_rootless (lc bc fuel : Nat) {m : HeapMap K V} (hroot : m.root = none) (k : K)
    (v : V) :
    insertH lc bc fuel m k v =
      insertH lc bc fuel ⟨(m.heap.alloc (.leaf [] none none)).2,
        some (m.heap.alloc (.leaf [] none none)).1, m.count⟩ k v := by
  simp only [insertH, hroot]

theorem removeTree_empty (lc bc : Nat) (k : K) :
    removeTree lc bc (Node.leaf ([] : Leaf K V)) k = none := by
  simp [removeTree, removeRec, leafRemove]

/-! ## Sorted lists as multisets -/

theorem perm_shuffle {α : Type} (a x b c : List α) : (a ++ (x ++ b) ++ c).Perm ((a ++ b ++ c) ++ x) := by
  simp only [List.append_assoc]
  refine List.Perm.append_left a ?_
  calc (x ++ (b ++ c)).Perm ((b ++ c) ++ x) := List.perm_append_comm
    _ = b ++ (c ++ x) := by rw [List.append_assoc]

/-- Where a present key sits in a sorted list: at the cut, and its entry is
the one that was there. -/
theorem sorted_split_present {l : List (K × V)} (hs : Sorted l) {k : K} {o : V}
    (hmem : (k, o) ∈ l) :
    ∃ A B, l = A ++ (k, o) :: B ∧ ∀ e ∈ A, e.1 < k := by
  obtain ⟨A, B, rfl, -, hA, hB⟩ := lowerBound_spec l k hs
  cases B with
  | nil =>
    rw [List.append_nil] at hmem
    exact (lt_irrefl (hA _ hmem)).elim
  | cons e B' =>
    rcases List.mem_append.mp hmem with hm | hm
    · exact (lt_irrefl (hA _ hm)).elim
    rcases List.mem_cons.mp hm with hm | hm
    · rw [← hm]; exact ⟨A, B', rfl, hA⟩
    · exfalso
      have hp := hs
      simp only [Sorted, List.pairwise_append, List.pairwise_cons] at hp
      exact hB e List.mem_cons_self (hp.2.1.1 _ hm)

theorem insertSorted_perm_absent {l : List (K × V)} (hs : Sorted l) {k : K} (v : V)
    (habs : ∀ e ∈ l, e.1 ≠ k) : (insertSorted k v l).Perm (l ++ [(k, v)]) := by
  obtain ⟨A, B, rfl, -, hA, hB⟩ := lowerBound_spec l k hs
  have hB' : ∀ e ∈ B, k < e.1 := by
    intro e he
    rcases lt_trichotomy k e.1 with h | h | h
    · exact h
    · exact absurd h.symm (habs e (List.mem_append_right _ he))
    · exact absurd h (hB e he)
  rw [insertSorted_absent A B hA hB', List.append_assoc]
  exact List.Perm.append_left A (List.perm_append_comm (l₁ := [(k, v)]) (l₂ := B))

theorem insertSorted_perm_present {l : List (K × V)} (hs : Sorted l) {k : K} (v : V) {o : V}
    (hmem : (k, o) ∈ l) : (insertSorted k v l ++ [(k, o)]).Perm (l ++ [(k, v)]) := by
  obtain ⟨A, B, rfl, hA⟩ := sorted_split_present hs hmem
  rw [insertSorted_present A (k, o) B hA rfl, List.append_assoc, List.append_assoc]
  refine List.Perm.append_left A ?_
  exact (List.Perm.cons _ (List.perm_append_comm (l₁ := B) (l₂ := [(k, o)]))).trans
    ((List.Perm.swap (k, o) (k, v) B).trans
      (List.Perm.cons _ (List.perm_append_comm (l₁ := [(k, v)]) (l₂ := B))))

theorem eraseSorted_perm {l : List (K × V)} (hs : Sorted l) {k : K} {v : V}
    (hmem : (k, v) ∈ l) : (eraseSorted k l ++ [(k, v)]).Perm l := by
  obtain ⟨A, B, rfl, hA⟩ := sorted_split_present hs hmem
  rw [eraseSorted_present A (k, v) B hA rfl, List.append_assoc]
  exact List.Perm.append_left A (List.perm_append_comm (l₁ := B) (l₂ := [(k, v)]))

/-! ## Operation traces -/

/-- The operations that move entries. -/
inductive Op (K V : Type) where
  | ins (k : K) (v : V)
  | rem (k : K)
  | clear

/-- The tree model's run: the final tree, the entries handed back to the
caller, the entries dropped by `clear`. -/
def runT (lc bc : Nat) : List (Op K V) → Node K V → Node K V × List (K × V) × List (K × V)
  | [], t => (t, [], [])
  | .ins k v :: ops, t =>
    match runT lc bc ops (insertTree lc bc t k v).1 with
    | (t', outs, dropped) => (t', ((insertTree lc bc t k v).2.map fun o => (k, o)).toList ++ outs, dropped)
  | .rem k :: ops, t =>
    match removeTree lc bc t k with
    | none => runT lc bc ops t
    | some (v, t1) =>
      match runT lc bc ops t1 with
      | (t', outs, dropped) => (t', (k, v) :: outs, dropped)
  | .clear :: ops, t =>
    match runT lc bc ops (.leaf []) with
    | (t', outs, dropped) => (t', outs, t.toList ++ dropped)

/-- Everything a run inserts. -/
def inserted : List (Op K V) → List (K × V)
  | [] => []
  | .ins k v :: ops => (k, v) :: inserted ops
  | .rem _ :: ops => inserted ops
  | .clear :: ops => inserted ops

/-- The ledger balances: after any run from a well-formed tree, the live
entries plus the entries handed back plus the entries dropped are a
permutation of the starting entries plus everything inserted. -/
theorem ledger (lc bc : Nat) (hlc : 4 ≤ lc) (hbc : 4 ≤ bc) :
    ∀ (ops : List (Op K V)) (t : Node K V) (ht : Nat), WF lc bc ht true none none t →
      ((runT lc bc ops t).1.toList ++ (runT lc bc ops t).2.1 ++ (runT lc bc ops t).2.2).Perm
        (t.toList ++ inserted ops) := by
  intro ops
  induction ops with
  | nil => intro t ht _; simp [runT, inserted]
  | cons op ops ih =>
    intro t ht hwf
    have hsorted := wf_toList_sorted lc bc ht t true none none hwf
    cases op with
    | ins k v =>
      have hwf' : ∃ ht', WF lc bc ht' true none none (insertTree lc bc t k v).1 := by
        rcases insertTree_wf lc bc (by omega) (by omega) ht t k v hwf with h | h
        · exact ⟨ht, h⟩
        · exact ⟨ht + 1, h⟩
      obtain ⟨ht', hwf'⟩ := hwf'
      have hrec := ih (insertTree lc bc t k v).1 ht' hwf'
      obtain ⟨htl, hsome, hnone⟩ := insertTree_toList lc bc (by omega) (by omega) ht t k v hwf
      simp only [runT, inserted]
      rcases hr : runT lc bc ops (insertTree lc bc t k v).1 with ⟨t', outs, dropped⟩
      rw [hr] at hrec
      simp only at hrec ⊢
      have hfin : ∀ (old' : List (K × V)),
          ((insertTree lc bc t k v).1.toList ++ old').Perm (t.toList ++ [(k, v)]) →
          (t'.toList ++ (old' ++ outs) ++ dropped).Perm (t.toList ++ (k, v) :: inserted ops) := by
        intro old' hins
        refine (perm_shuffle _ _ _ _).trans ((hrec.append_right _).trans ?_)
        have h1 : ((insertTree lc bc t k v).1.toList ++ inserted ops ++ old').Perm
            ((insertTree lc bc t k v).1.toList ++ old' ++ inserted ops) := by
          rw [List.append_assoc, List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
        have h2 := hins.append_right (inserted ops)
        have h3 : t.toList ++ [(k, v)] ++ inserted ops = t.toList ++ (k, v) :: inserted ops := by simp
        exact h1.trans (h3 ▸ h2)
      rcases hold : (insertTree lc bc t k v).2 with _ | o
      · simp only [Option.map_none, Option.toList_none]
        apply hfin
        rw [List.append_nil, htl]
        exact insertSorted_perm_absent hsorted v (hnone hold)
      · simp only [Option.map_some, Option.toList_some]
        apply hfin
        rw [htl]
        exact insertSorted_perm_present hsorted v (hsome o hold)
    | rem k =>
      have hspec := removeTree_spec lc bc hlc hbc ht t k hwf
      simp only [runT, inserted]
      rcases hrt : removeTree lc bc t k with _ | ⟨v, t1⟩
      · exact ih t ht hwf
      · simp only [hrt] at hspec
        obtain ⟨hmem, htl, ht1, -, hwf1⟩ := hspec
        have hrec := ih t1 ht1 hwf1
        dsimp only
        rcases hr : runT lc bc ops t1 with ⟨t', outs, dropped⟩
        rw [hr] at hrec
        simp only at hrec ⊢
        have h1 : (t'.toList ++ (k, v) :: outs ++ dropped).Perm
            ((t'.toList ++ outs ++ dropped) ++ [(k, v)]) :=
          perm_shuffle t'.toList [(k, v)] outs dropped
        have h2 := hrec.append_right [(k, v)]
        have h3 : (t1.toList ++ inserted ops ++ [(k, v)]).Perm
            (t1.toList ++ [(k, v)] ++ inserted ops) := by
          rw [List.append_assoc, List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
        have h4 : (t1.toList ++ [(k, v)] ++ inserted ops).Perm (t.toList ++ inserted ops) := by
          rw [htl]; exact (eraseSorted_perm hsorted hmem).append_right _
        exact h1.trans (h2.trans (h3.trans h4))
    | clear =>
      have hrec := ih (.leaf []) 0 (wf_empty_leaf lc bc)
      simp only [runT, inserted]
      rcases hr : runT lc bc ops (.leaf []) with ⟨t', outs, dropped⟩
      rw [hr] at hrec
      simp only [Node.toList, List.nil_append] at hrec ⊢
      have h1 : (t'.toList ++ outs ++ (t.toList ++ dropped)).Perm
          ((t'.toList ++ outs ++ dropped) ++ t.toList) := by
        rw [List.append_assoc, List.append_assoc, List.append_assoc]
        exact List.Perm.append_left _ (List.Perm.append_left _ List.perm_append_comm)
      exact h1.trans ((hrec.append_right _).trans List.perm_append_comm)

/-! ## The heap model runs the same trace -/

/-- One operation on the heap model, with the entries it hands back. -/
def stepH (lc bc fuel : Nat) (m : HeapMap K V) : Op K V → Option (HeapMap K V × List (K × V))
  | .ins k v => (insertH lc bc fuel m k v).map fun r => (r.2, (r.1.map fun o => (k, o)).toList)
  | .rem k => (removeH lc bc fuel m k).map fun r => (r.2, (r.1.map fun v => (k, v)).toList)
  | .clear => (clearH fuel m).map fun m' => (m', [])

/-- A whole trace; `none` is a fault somewhere along it. -/
def runH (lc bc fuel : Nat) : List (Op K V) → HeapMap K V → Option (HeapMap K V × List (K × V))
  | [], m => some (m, [])
  | op :: ops, m => do
    let (m1, outs1) ← stepH lc bc fuel m op
    let (m', outs) ← runH lc bc fuel ops m1
    some (m', outs1 ++ outs)

/-- The heap map mirrors a tree, or is the rootless empty map `clear` leaves. -/
def MapOK (m : HeapMap K V) (d : Nat) (t : Node K V) : Prop :=
  HeapInv m d t ∨ (m.root = none ∧ (∀ i, m.heap.get i = none) ∧ m.count = 0 ∧ t = .leaf [])

/-- The live entries of a heap map are its tree's entries, in chain order. -/
theorem heapInv_live {m : HeapMap K V} {d : Nat} {t : Node K V} (hinv : HeapInv m d t) :
    ∃ lv, Linked m.heap none lv none ∧ t.toList = flat m.heap lv := by
  obtain ⟨root, ids, lv, -, hsub, -, -, -, hchain, -⟩ := hinv
  exact ⟨lv, hchain, (toList_eq_flat (d + 1)).1 m.heap root t lv hsub.abs hsub.leaves⟩

/-- The heap model runs any trace without faulting, hands back what the
tree model hands back, and ends mirroring the tree model's final tree. -/
theorem runH_sim (lc bc : Nat) (hlc : 4 ≤ lc) (hbc : 4 ≤ bc) (fuel : Nat) :
    ∀ (ops : List (Op K V)) (m : HeapMap K V) (t : Node K V) (d ht : Nat),
      MapOK m d t → WF lc bc ht true none none t → d + ops.length + 1 ≤ fuel →
      ∃ m', runH lc bc fuel ops m = some (m', (runT lc bc ops t).2.1) ∧
        ∃ d', MapOK m' d' (runT lc bc ops t).1 := by
  intro ops
  induction ops with
  | nil => intro m t d ht hok _ _; exact ⟨m, rfl, d, hok⟩
  | cons op ops ih =>
    intro m t d ht hok hwf hfuel
    simp only [List.length_cons] at hfuel
    cases op with
    | ins k v =>
      have hstart : ∃ m0 d0, insertH lc bc fuel m k v = insertH lc bc fuel m0 k v ∧
          HeapInv m0 d0 t ∧ d0 ≤ d := by
        rcases hok with hinv | ⟨hroot, hempty, hcount, rfl⟩
        · exact ⟨m, d, rfl, hinv, Nat.le_refl _⟩
        · refine ⟨_, 0, insertH_rootless lc bc fuel hroot k v, ?_, Nat.zero_le _⟩
          rw [hcount]
          exact heapInv_fresh_leaf hempty
      obtain ⟨m0, d0, heq, hinv0, hd0⟩ := hstart
      obtain ⟨old, m1, hins, hold, d1, hd1, hinv1⟩ :=
        insertH_sim lc bc (by omega) (by omega) d0 fuel (by omega) m0 t hinv0 k v ht hwf
      have hwf1 : ∃ ht1, WF lc bc ht1 true none none (insertTree lc bc t k v).1 := by
        rcases insertTree_wf lc bc (by omega) (by omega) ht t k v hwf with h | h
        · exact ⟨ht, h⟩
        · exact ⟨ht + 1, h⟩
      obtain ⟨ht1, hwf1⟩ := hwf1
      obtain ⟨m', hrun, d', hok'⟩ :=
        ih m1 (insertTree lc bc t k v).1 d1 ht1 (Or.inl hinv1) hwf1 (by omega)
      refine ⟨m', ?_, d', ?_⟩
      · simp only [runH, stepH, heq, hins, Option.map_some, Option.bind_eq_bind, Option.bind_some,
          hrun, runT, hold]
      · simp only [runT]
        rcases hr : runT lc bc ops (insertTree lc bc t k v).1 with ⟨t', outs, dropped⟩
        rw [hr] at hok'
        exact hok'
    | rem k =>
      rcases hok with hinv | ⟨hroot, hempty, hcount, rfl⟩
      · obtain ⟨res, m1, hrem, hnone, hsome⟩ :=
          removeH_sim lc bc hlc hbc d fuel (by omega) m t hinv k ht hwf
        have hspec := removeTree_spec lc bc hlc hbc ht t k hwf
        rcases hrt : removeTree lc bc t k with _ | ⟨v, t1⟩
        · obtain ⟨hres, hm1⟩ := hnone hrt
          subst hres; subst hm1
          obtain ⟨m', hrun, d', hok'⟩ := ih _ t d ht (Or.inl hinv) hwf (by omega)
          refine ⟨m', ?_, d', ?_⟩
          · simp only [runH, stepH, hrem, Option.map_some, Option.map_none, Option.toList_none,
              Option.bind_eq_bind, Option.bind_some, hrun, runT, hrt, List.nil_append]
          · simp only [runT, hrt]; exact hok'
        · simp only [hrt] at hspec
          obtain ⟨-, -, ht1, -, hwf1⟩ := hspec
          obtain ⟨hres, d1, hd1, hinv1⟩ := hsome v t1 hrt
          subst hres
          obtain ⟨m', hrun, d', hok'⟩ := ih m1 t1 d1 ht1 (Or.inl hinv1) hwf1 (by omega)
          refine ⟨m', ?_, d', ?_⟩
          · simp only [runH, stepH, hrem, Option.map_some, Option.toList_some, Option.bind_eq_bind,
              Option.bind_some, hrun, runT, hrt]
            rcases hr : runT lc bc ops t1 with ⟨t', outs, dropped⟩
            try rfl
          · simp only [runT, hrt]
            rcases hr : runT lc bc ops t1 with ⟨t', outs, dropped⟩
            rw [hr] at hok'
            exact hok'
      · have hrem : removeH lc bc fuel m k = some (none, m) := by simp [removeH, hroot]
        obtain ⟨m', hrun, d', hok'⟩ :=
          ih m (.leaf []) d ht (Or.inr ⟨hroot, hempty, hcount, rfl⟩) hwf (by omega)
        refine ⟨m', ?_, d', ?_⟩
        · simp only [runH, stepH, hrem, Option.map_some, Option.map_none, Option.toList_none,
            Option.bind_eq_bind, Option.bind_some, hrun, runT, removeTree_empty, List.nil_append]
        · simp only [runT, removeTree_empty]; exact hok'
    | clear =>
      rcases hok with hinv | ⟨hroot, hempty, hcount, rfl⟩
      · obtain ⟨h', hcl, hempty'⟩ := clearH_sim (by omega : d + 1 ≤ fuel) hinv
        obtain ⟨m', hrun, d', hok'⟩ := ih ⟨h', none, 0⟩ (.leaf []) 0 0
          (Or.inr ⟨rfl, hempty', rfl, rfl⟩) (wf_empty_leaf lc bc) (by omega)
        refine ⟨m', ?_, d', ?_⟩
        · simp only [runH, stepH, hcl, Option.map_some, Option.bind_eq_bind, Option.bind_some, hrun,
            runT, List.nil_append]
        · simp only [runT]
          rcases hr : runT lc bc ops (.leaf []) with ⟨t', outs, dropped⟩
          rw [hr] at hok'
          exact hok'
      · have hcl : clearH fuel m = some { m with count := 0 } := by simp [clearH, hroot]
        obtain ⟨m', hrun, d', hok'⟩ := ih { m with count := 0 } (.leaf []) d 0
          (Or.inr ⟨hroot, hempty, rfl, rfl⟩) (wf_empty_leaf lc bc) (by omega)
        refine ⟨m', ?_, d', ?_⟩
        · simp only [runH, stepH, hcl, Option.map_some, Option.bind_eq_bind, Option.bind_some, hrun,
            runT, List.nil_append]
        · simp only [runT]
          rcases hr : runT lc bc ops (.leaf []) with ⟨t', outs, dropped⟩
          rw [hr] at hok'
          exact hok'

/-- From the empty map: any trace runs without a fault, the heap model
hands back exactly what the tree model hands back, it ends mirroring the
tree model's tree, and the ledger balances: live entries plus entries
handed back plus entries dropped is a permutation of everything inserted.
So every entry is, at the end, in exactly one place. -/
theorem runH_ledger (lc bc : Nat) (hlc : 4 ≤ lc) (hbc : 4 ≤ bc) (fuel : Nat)
    (ops : List (Op K V)) (hfuel : ops.length + 1 ≤ fuel) :
    ∃ m' d', runH lc bc fuel ops (HeapMap.new : HeapMap K V) =
        some (m', (runT lc bc ops (.leaf [])).2.1) ∧
      MapOK m' d' (runT lc bc ops (.leaf [])).1 ∧
      ((runT lc bc ops (.leaf [])).1.toList ++ (runT lc bc ops (.leaf [])).2.1 ++
        (runT lc bc ops (.leaf [])).2.2).Perm (inserted ops) := by
  obtain ⟨m', hrun, d', hok⟩ := runH_sim lc bc hlc hbc fuel ops HeapMap.new (.leaf []) 0 0
    (Or.inl heapInv_new) (wf_empty_leaf lc bc) (by omega)
  refine ⟨m', d', hrun, hok, ?_⟩
  have := ledger lc bc hlc hbc ops (.leaf []) 0 (wf_empty_leaf lc bc)
  simpa [Node.toList] using this

end HeapLedger

end BPlusTree
