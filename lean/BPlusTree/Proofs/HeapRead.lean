import BPlusTree.Proofs.HeapRemove
import BPlusTree.Proofs.Read

/-!
# The heap model: the reads

`get`, `first`, `last` and `range` on the heap model return what the tree
model returns, given `HeapInv`. The bridge is the leaf chain: a subtree's
entries are the concatenation of its leaves' contents in chain order, so
the leaf `leaf_for_key` lands on splits the chain exactly where the tree
model's `leafForKey` splits the entries, and `Items::next` hopping along
`next` reads the same slice of the entries that `make_items` describes
by two indices.
-/

namespace BPlusTree

open Std

set_option linter.unusedSectionVars false

section HeapRead

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-! ## Leaves as entries -/

/-- The contents of a leaf record (empty for anything else). -/
def leafKvs (h : Heap K V) (l : NodeId) : Leaf K V :=
  match h.get l with
  | some (.leaf kvs _ _) => kvs
  | _ => []

/-- The entries of a run of leaves, in order. -/
def flat (h : Heap K V) (lv : List NodeId) : List (K × V) := (lv.map (leafKvs h)).flatten

theorem leafKvs_eq {h : Heap K V} {l : NodeId} {kvs : Leaf K V} {p n : Option NodeId}
    (hg : h.get l = some (.leaf kvs p n)) : leafKvs h l = kvs := by
  simp [leafKvs, hg]

theorem flat_nil (h : Heap K V) : flat h [] = [] := rfl

theorem flat_cons (h : Heap K V) (l : NodeId) (lv : List NodeId) :
    flat h (l :: lv) = leafKvs h l ++ flat h lv := by
  simp [flat]

theorem flat_append (h : Heap K V) (l1 l2 : List NodeId) :
    flat h (l1 ++ l2) = flat h l1 ++ flat h l2 := by
  simp [flat]

theorem flat_singleton (h : Heap K V) (l : NodeId) : flat h [l] = leafKvs h l := by
  simp [flat]

/-- A subtree's entries are its leaves' contents in chain order. -/
theorem toList_eq_flat (d : Nat) :
    (∀ (h : Heap K V) (id : NodeId) (t : Node K V) (lv : List NodeId),
      absNode d h id = some t → leafIds d h id = some lv → t.toList = flat h lv) ∧
    (∀ (h : Heap K V) (es : List (K × NodeId)) (ts : List (K × Node K V)) (lv : List NodeId),
      absNode.absEntries d h es = some ts → leafIds.leafChildren d h (es.map (·.2)) = some lv →
        entriesToList ts = flat h lv) := by
  induction d with
  | zero =>
    refine ⟨fun h id t lv ha => by simp [absNode] at ha, ?_⟩
    intro h es ts lv he hl
    cases es with
    | nil =>
      simp only [absNode.absEntries, Option.some.injEq] at he
      simp only [List.map_nil, leafIds.leafChildren, Option.some.injEq] at hl
      subst he; subst hl; rfl
    | cons e rest =>
      obtain ⟨s, c⟩ := e
      simp [absNode.absEntries, absNode] at he
  | succ d ih =>
    have hnode : ∀ (h : Heap K V) (id : NodeId) (t : Node K V) (lv : List NodeId),
        absNode (d + 1) h id = some t → leafIds (d + 1) h id = some lv → t.toList = flat h lv := by
      intro h id t lv ha hl
      rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
      · simp [absNode, hg] at ha
      · rw [absNode_leaf hg] at ha; rw [leafIds_leaf hg] at hl
        cases ha; cases hl
        simp [Node.toList, flat, leafKvs, hg]
      · rw [absNode_branch hg] at ha; rw [leafIds_branch hg] at hl
        rcases h0 : absNode d h c0 with _ | t0 <;> rw [h0] at ha
        · cases ha
        rcases he : absNode.absEntries d h es with _ | ts <;> rw [he] at ha
        · cases ha
        simp only [Option.bind_some, Option.some.injEq] at ha
        subst ha
        rw [leafChildren_cons] at hl
        rcases hl0 : leafIds d h c0 with _ | lv0 <;> rw [hl0] at hl
        · cases hl
        rcases hlr : leafIds.leafChildren d h (es.map (·.2)) with _ | lvr <;> rw [hlr] at hl
        · cases hl
        simp only [Option.bind_some, Option.some.injEq] at hl
        subst hl
        simp only [Node.toList, flat_append]
        rw [ih.1 h c0 t0 lv0 h0 hl0, ih.2 h es ts lvr he hlr]
    refine ⟨hnode, ?_⟩
    intro h es
    induction es with
    | nil =>
      intro ts lv he hl
      simp only [absNode.absEntries, Option.some.injEq] at he
      simp only [List.map_nil, leafIds.leafChildren, Option.some.injEq] at hl
      subst he; subst hl; rfl
    | cons e rest ihe =>
      intro ts lv he hl
      obtain ⟨s, c⟩ := e
      obtain ⟨tc, tr, hc, hr, rfl⟩ := absEntries_cons_inv he
      simp only [List.map_cons] at hl
      rw [leafChildren_cons] at hl
      rcases hlc : leafIds (d + 1) h c with _ | lvc <;> rw [hlc] at hl
      · cases hl
      rcases hlr : leafIds.leafChildren (d + 1) h (rest.map (·.2)) with _ | lvr <;> rw [hlr] at hl
      · cases hl
      simp only [Option.bind_some, Option.some.injEq] at hl
      subst hl
      simp only [entriesToList, flat_append]
      rw [hnode h c tc lvc hc hlc, ihe tr lvr hr hlr]

/-- The entries before the picked child are the leaves before it. -/
theorem frontList_eq_flat {d : Nat} {h : Heap K V} :
    ∀ (c0 : NodeId) (t0 : Node K V) (A : List (K × NodeId)) (tsA : List (K × Node K V))
      (lvF : List NodeId), absNode d h c0 = some t0 → absNode.absEntries d h A = some tsA →
      leafIds.leafChildren d h (frontIds c0 A) = some lvF → frontList t0 tsA = flat h lvF := by
  intro c0 t0 A
  induction A generalizing c0 t0 with
  | nil =>
    intro tsA lvF h0 hA hl
    simp only [absNode.absEntries, Option.some.injEq] at hA
    simp only [frontIds, leafIds.leafChildren, Option.some.injEq] at hl
    subst hA; subst hl; rfl
  | cons e rest ih =>
    intro tsA lvF h0 hA hl
    obtain ⟨s, c⟩ := e
    obtain ⟨tc, tr, hc, hr, rfl⟩ := absEntries_cons_inv hA
    simp only [frontIds] at hl
    rw [leafChildren_cons] at hl
    rcases hl0 : leafIds d h c0 with _ | lv0 <;> rw [hl0] at hl
    · cases hl
    rcases hlr : leafIds.leafChildren d h (frontIds c rest) with _ | lvr <;> rw [hlr] at hl
    · cases hl
    simp only [Option.bind_some, Option.some.injEq] at hl
    subst hl
    simp only [frontList, flat_append]
    rw [(toList_eq_flat d).1 h c0 t0 lv0 h0 hl0, ih c tc tr lvr hc hr hlr]

/-! ## Descents -/

/-- `leaf_for_key` lands on the leaf that splits the chain where the tree
model's `leafForKey` splits the entries. -/
theorem leafForKeyH_sim (k : K) :
    ∀ (d fuel : Nat) (h : Heap K V) (id : NodeId) (t : Node K V) (ids lv : List NodeId),
      d ≤ fuel → Sub h d id t ids lv →
      ∃ l L1 L2, leafForKeyH k fuel h id = some l ∧ lv = L1 ++ l :: L2 ∧
        leafForKey k t = (flat h L1, leafKvs h l, flat h L2) ∧
        ∃ p n, h.get l = some (.leaf (leafKvs h l) p n) := by
  intro d
  induction d with
  | zero => intro fuel h id t ids lv _ hsub; have := hsub.reach; simp [reachIds] at this
  | succ d ih =>
    intro fuel h id t ids lv hfuel hsub
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
    · exfalso; have := hsub.reach; simp [reachIds, hg] at this
    · obtain ⟨rfl, rfl, rfl⟩ := sub_leaf_inv hg hsub
      refine ⟨id, [], [], by simp [leafForKeyH, hg], rfl, ?_, p, n, by rw [leafKvs_eq hg]; exact hg⟩
      simp [leafForKey, flat, leafKvs_eq hg]
    · obtain ⟨t0, ts, below, h0, hes, rfl, hbelow, rfl, hlvb⟩ := sub_branch_inv hg hsub
      have hesAB := takeWhile_append_dropWhile_entries k es
      obtain ⟨htsA, htsB⟩ := absEntries_takeWhile k hes
      have hcs : c0 :: es.map (·.2) =
          frontIds c0 (es.takeWhile (sepLE k)) ++
            lastChild c0 (es.takeWhile (sepLE k)) :: (es.dropWhile (sepLE k)).map (·.2) := by
        have := cons_map_split c0 (es.takeWhile (sepLE k)) (es.dropWhile (sepLE k))
        rwa [← hesAB] at this
      rw [hcs, reachChildren_append, reachChildren_cons] at hbelow
      rw [hcs, leafChildren_append, leafChildren_cons] at hlvb
      rcases hLf : reachIds.reachChildren d h (frontIds c0 (es.takeWhile (sepLE k))) with _ | Lf
      · rw [hLf] at hbelow; cases hbelow
      rcases hLc : reachIds d h (lastChild c0 (es.takeWhile (sepLE k))) with _ | Lc
      · rw [hLf, hLc] at hbelow; cases hbelow
      rcases hlvF : leafIds.leafChildren d h (frontIds c0 (es.takeWhile (sepLE k))) with _ | lvF
      · rw [hlvF] at hlvb; cases hlvb
      rcases hlvC : leafIds d h (lastChild c0 (es.takeWhile (sepLE k))) with _ | lvC
      · rw [hlvF, hlvC] at hlvb; cases hlvb
      rcases hlvB : leafIds.leafChildren d h ((es.dropWhile (sepLE k)).map (·.2)) with _ | lvB
      · rw [hlvF, hlvC, hlvB] at hlvb; cases hlvb
      rw [hlvF, hlvC, hlvB] at hlvb
      simp only [Option.bind_some, Option.some.injEq] at hlvb
      subst hlvb
      have hsubC : Sub h d (lastChild c0 (es.takeWhile (sepLE k)))
          (lastChild t0 (ts.takeWhile (sepLE k))) Lc lvC :=
        ⟨absNode_lastChild h0 htsA, hLc, hlvC⟩
      obtain ⟨l, L1, L2, hrun, hlvC', hleaf, hrec⟩ := ih f h _ _ Lc lvC (by omega) hsubC
      have hfront := frontList_eq_flat c0 t0 _ _ lvF h0 htsA hlvF
      have hback := (toList_eq_flat d).2 h _ _ lvB htsB hlvB
      refine ⟨l, lvF ++ L1, L2 ++ lvB, by simp [leafForKeyH, hg, hrun], by simp [hlvC'], ?_, hrec⟩
      rw [leafForKey]
      simp only [hleaf, hfront, hback, flat_append]

/-- `leftmost_leaf` is the chain's first leaf. -/
theorem leftmostLeafH_sim :
    ∀ (d fuel : Nat) (h : Heap K V) (id : NodeId) (t : Node K V) (ids lv : List NodeId),
      d ≤ fuel → Sub h d id t ids lv →
      ∃ l L2, leftmostLeafH fuel h id = some l ∧ lv = l :: L2 ∧ leftmostLeaf t = leafKvs h l ∧
        ∃ p n, h.get l = some (.leaf (leafKvs h l) p n) := by
  intro d
  induction d with
  | zero => intro fuel h id t ids lv _ hsub; have := hsub.reach; simp [reachIds] at this
  | succ d ih =>
    intro fuel h id t ids lv hfuel hsub
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
    · exfalso; have := hsub.reach; simp [reachIds, hg] at this
    · obtain ⟨rfl, rfl, rfl⟩ := sub_leaf_inv hg hsub
      exact ⟨id, [], by simp [leftmostLeafH, hg], rfl, by simp [leftmostLeaf, leafKvs_eq hg], p, n,
        by rw [leafKvs_eq hg]; exact hg⟩
    · obtain ⟨t0, ts, below, h0, hes, rfl, hbelow, rfl, hlvb⟩ := sub_branch_inv hg hsub
      rw [reachChildren_cons] at hbelow
      rw [leafChildren_cons] at hlvb
      rcases hL0 : reachIds d h c0 with _ | L0
      · rw [hL0] at hbelow; cases hbelow
      rcases hlv0 : leafIds d h c0 with _ | lv0
      · rw [hlv0] at hlvb; cases hlvb
      rcases hlvr : leafIds.leafChildren d h (es.map (·.2)) with _ | lvr
      · rw [hlv0, hlvr] at hlvb; cases hlvb
      rw [hlv0, hlvr] at hlvb
      simp only [Option.bind_some, Option.some.injEq] at hlvb
      subst hlvb
      obtain ⟨l, L2, hrun, hlv0', hleaf, hrec⟩ := ih f h c0 t0 L0 lv0 (by omega) ⟨h0, hL0, hlv0⟩
      exact ⟨l, L2 ++ lvr, by simp [leftmostLeafH, hg, hrun], by simp [hlv0'],
        by simp [leftmostLeaf, hleaf], hrec⟩

/-- `rightmost_leaf` is the chain's last leaf. -/
theorem rightmostLeafH_sim :
    ∀ (d fuel : Nat) (h : Heap K V) (id : NodeId) (t : Node K V) (ids lv : List NodeId),
      d ≤ fuel → Sub h d id t ids lv →
      ∃ l L1, rightmostLeafH fuel h id = some l ∧ lv = L1 ++ [l] ∧
        rightmostLeaf t = leafKvs h l ∧ ∃ p n, h.get l = some (.leaf (leafKvs h l) p n) := by
  intro d
  induction d with
  | zero => intro fuel h id t ids lv _ hsub; have := hsub.reach; simp [reachIds] at this
  | succ d ih =>
    intro fuel h id t ids lv hfuel hsub
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
    · exfalso; have := hsub.reach; simp [reachIds, hg] at this
    · obtain ⟨rfl, rfl, rfl⟩ := sub_leaf_inv hg hsub
      exact ⟨id, [], by simp [rightmostLeafH, hg], rfl, by simp [rightmostLeaf, leafKvs_eq hg],
        p, n, by rw [leafKvs_eq hg]; exact hg⟩
    · obtain ⟨t0, ts, below, h0, hes, rfl, hbelow, rfl, hlvb⟩ := sub_branch_inv hg hsub
      rw [cons_map_eq_front_last, reachChildren_append] at hbelow
      rw [cons_map_eq_front_last, leafChildren_append] at hlvb
      rcases hLf : reachIds.reachChildren d h (frontIds c0 es) with _ | Lf
      · rw [hLf] at hbelow; cases hbelow
      rcases hLc : reachIds.reachChildren d h [lastChild c0 es] with _ | Lc
      · rw [hLf, hLc] at hbelow; cases hbelow
      rcases hlvF : leafIds.leafChildren d h (frontIds c0 es) with _ | lvF
      · rw [hlvF] at hlvb; cases hlvb
      rcases hlvC : leafIds.leafChildren d h [lastChild c0 es] with _ | lvC
      · rw [hlvF, hlvC] at hlvb; cases hlvb
      rw [hlvF, hlvC] at hlvb
      simp only [Option.bind_some, Option.some.injEq] at hlvb
      subst hlvb
      have hsubC : Sub h d (lastChild c0 es) (lastChild t0 ts) Lc lvC :=
        ⟨absNode_lastChild h0 hes, reachChildren_singleton hLc, leafChildren_singleton hlvC⟩
      obtain ⟨l, L1, hrun, hlvC', hleaf, hrec⟩ := ih f h _ _ Lc lvC (by omega) hsubC
      refine ⟨l, lvF ++ L1, by simp [rightmostLeafH, hg, hrun], by simp [hlvC'], ?_, hrec⟩
      rw [rightmostLeaf]; exact hleaf

/-! ## `get`, `first`, `last` -/

theorem getH_sim {d fuel : Nat} (hfuel : d + 1 ≤ fuel) {m : HeapMap K V} {t : Node K V}
    (hinv : HeapInv m d t) (k : K) : getH fuel m k = some (getTree t k) := by
  obtain ⟨root, ids, lv, hroot, hsub, -, -, -, -, -⟩ := hinv
  obtain ⟨l, L1, L2, hrun, -, hleaf, p, n, hgl⟩ := leafForKeyH_sim k (d + 1) fuel m.heap root t ids lv hfuel hsub
  simp only [getH, hroot, hrun, Heap.getLeaf_eq hgl, Option.bind_eq_bind, Option.bind_some,
    getTree, hleaf]

theorem firstH_sim {d fuel : Nat} (hfuel : d + 1 ≤ fuel) {m : HeapMap K V} {t : Node K V}
    (hinv : HeapInv m d t) : firstH fuel m = some (firstTree t) := by
  obtain ⟨root, ids, lv, hroot, hsub, -, -, -, -, -⟩ := hinv
  obtain ⟨l, L2, hrun, -, hleaf, p, n, hgl⟩ := leftmostLeafH_sim (d + 1) fuel m.heap root t ids lv hfuel hsub
  simp only [firstH, hroot, hrun, Heap.getLeaf_eq hgl, Option.bind_eq_bind, Option.bind_some,
    firstTree, hleaf]

theorem lastH_sim {d fuel : Nat} (hfuel : d + 1 ≤ fuel) {m : HeapMap K V} {t : Node K V}
    (hinv : HeapInv m d t) : lastH fuel m = some (lastTree t) := by
  obtain ⟨root, ids, lv, hroot, hsub, -, -, -, -, -⟩ := hinv
  obtain ⟨l, L1, hrun, -, hleaf, p, n, hgl⟩ := rightmostLeafH_sim (d + 1) fuel m.heap root t ids lv hfuel hsub
  simp only [lastH, hroot, hrun, Heap.getLeaf_eq hgl, Option.bind_eq_bind, Option.bind_some,
    lastTree, hleaf]

/-! ## Nonempty leaves -/

/-- Which child a leaf belongs to. -/
theorem leaf_in_child {d : Nat} {h : Heap K V} :
    ∀ (cs L lv : List NodeId), reachIds.reachChildren d h cs = some L →
      leafIds.leafChildren d h cs = some lv →
      ∀ l ∈ lv, ∃ c ∈ cs, ∃ Lc lvc, reachIds d h c = some Lc ∧ leafIds d h c = some lvc ∧ l ∈ lvc := by
  intro cs
  induction cs with
  | nil =>
    intro L lv _ hl l hin
    simp only [leafIds.leafChildren, Option.some.injEq] at hl
    subst hl; cases hin
  | cons c rest ih =>
    intro L lv hL hl l hin
    rw [reachChildren_cons] at hL
    rw [leafChildren_cons] at hl
    rcases hLc : reachIds d h c with _ | Lc
    · rw [hLc] at hL; cases hL
    rcases hLr : reachIds.reachChildren d h rest with _ | Lr
    · rw [hLc, hLr] at hL; cases hL
    rcases hlc : leafIds d h c with _ | lvc
    · rw [hlc] at hl; cases hl
    rcases hlr : leafIds.leafChildren d h rest with _ | lvr
    · rw [hlc, hlr] at hl; cases hl
    rw [hlc, hlr] at hl
    simp only [Option.bind_some, Option.some.injEq] at hl
    subst hl
    rcases List.mem_append.mp hin with hin | hin
    · exact ⟨c, List.mem_cons_self, Lc, lvc, hLc, hlc, hin⟩
    · obtain ⟨c', hc', Lc', lvc', h1, h2, h3⟩ := ih Lr lvr hLr hlr l hin
      exact ⟨c', List.mem_cons_of_mem _ hc', Lc', lvc', h1, h2, h3⟩

/-- Below a well-formed node, every leaf is nonempty (a root leaf aside). -/
theorem leaves_nonempty (lc bc : Nat) (hlc : 2 ≤ lc) :
    ∀ (d : Nat) (h : Heap K V) (id : NodeId) (t : Node K V) (ids lv : List NodeId)
      (hgt : Nat) (isRoot : Bool) (lo hi : Option K),
      Sub h d id t ids lv → WF lc bc hgt isRoot lo hi t → (isRoot = false ∨ 0 < hgt) →
      ∀ l ∈ lv, leafKvs h l ≠ [] := by
  intro d
  induction d with
  | zero => intro h id t ids lv _ _ _ _ hsub; have := hsub.reach; simp [reachIds] at this
  | succ d ih =>
    intro h id t ids lv hgt isRoot lo hi hsub hwf hr l hl
    rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
    · exfalso; have := hsub.reach; simp [reachIds, hg] at this
    · obtain ⟨rfl, rfl, rfl⟩ := sub_leaf_inv hg hsub
      rw [List.mem_singleton.mp hl, leafKvs_eq hg]
      cases hgt with
      | zero =>
        obtain ⟨-, -, -, hfill⟩ := hwf
        rcases hr with hr | hr
        · subst hr
          rcases hfill with h1 | h1
          · cases h1
          · intro hnil; rw [hnil] at h1; simp at h1; omega
        · omega
      | succ g => exact absurd hwf (fun x => x)
    · obtain ⟨t0, ts, below, h0, hes, rfl, hbelow, rfl, hlvb⟩ := sub_branch_inv hg hsub
      cases hgt with
      | zero => exact absurd hwf (fun x => x)
      | succ g =>
        obtain ⟨-, -, -, -, hchain⟩ := hwf
        obtain ⟨c, hc, Lc, lvc, hLc, hlc, hlin⟩ := leaf_in_child _ _ _ hbelow hlvb l hl
        obtain ⟨tc, htc⟩ := abs_branch_children hg hsub.abs c hc
        have hchildrenAbs : t0 :: ts.map (·.2) = (c0 :: es.map (·.2)).map (absF d h) := by
          rw [absEntries_eq_map hes, ← absF_of_some h0]; simp [Function.comp_def]
        obtain ⟨lo', hi', hwfc⟩ := chain_children lo hi t0 ts hchain (absF d h c)
          (by rw [hchildrenAbs]; exact List.mem_map_of_mem hc)
        rw [absF_of_some htc] at hwfc
        exact ih h c tc Lc lvc g false lo' hi' ⟨htc, hLc, hlc⟩ hwfc (Or.inl rfl) l hlin

/-- A chain of at least two leaves hangs under a branch. -/
theorem branch_of_two_leaves {d : Nat} {h : Heap K V} {id : NodeId} {t : Node K V}
    {ids lv : List NodeId} (hsub : Sub h (d + 1) id t ids lv) (hlen : 2 ≤ lv.length) :
    ∃ c0 es, h.get id = some (.branch c0 es) := by
  rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
  · exfalso; have := hsub.reach; simp [reachIds, hg] at this
  · obtain ⟨-, -, rfl⟩ := sub_leaf_inv hg hsub; simp at hlen
  · exact ⟨c0, es, rfl⟩

/-! ## Positions in the chain -/

theorem split_unique {α : Type} :
    ∀ {l1 l1' l2 l2' : List α} {a : α}, l1 ++ a :: l2 = l1' ++ a :: l2' → (l1 ++ a :: l2).Nodup →
      l1 = l1' ∧ l2 = l2' := by
  intro l1
  induction l1 with
  | nil =>
    intro l1' l2 l2' a heq hnd
    cases l1' with
    | nil => simp at heq; exact ⟨rfl, heq⟩
    | cons x t =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact absurd (List.mem_append_right _ List.mem_cons_self) (List.nodup_cons.mp hnd).1
  | cons x t ih =>
    intro l1' l2 l2' a heq hnd
    cases l1' with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact absurd (List.mem_append_right _ List.mem_cons_self) (List.nodup_cons.mp hnd).1
    | cons y t' =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, heq⟩ := heq
      obtain ⟨h1, h2⟩ := ih heq (List.nodup_cons.mp hnd).2
      exact ⟨by rw [h1], h2⟩

theorem length_le_length_flat {h : Heap K V} {lv : List NodeId}
    (hne : ∀ l ∈ lv, leafKvs h l ≠ []) : lv.length ≤ (flat h lv).length := by
  induction lv with
  | nil => simp [flat]
  | cons l rest ih =>
    rw [flat_cons, List.length_append, List.length_cons]
    have h1 := ih (fun l hl => hne l (List.mem_cons_of_mem _ hl))
    have h2 : 0 < (leafKvs h l).length := List.length_pos_iff.mpr (hne l List.mem_cons_self)
    omega

theorem take_drop_prefix {α : Type} (l1 l2 : List α) (fi bi : Nat) (hbi : bi ≤ l1.length) :
    ((l1 ++ l2).drop fi).take (bi - fi) = (l1.drop fi).take (bi - fi) := by
  by_cases hfi : fi ≤ l1.length
  · rw [List.drop_append_of_le_length hfi, List.take_append_of_le_length]
    rw [List.length_drop]; omega
  · have : bi - fi = 0 := by omega
    simp [this]

theorem take_drop_step {α : Type} (l1 l2 : List α) (fi n : Nat) (hfi : fi ≤ l1.length) :
    ((l1 ++ l2).drop fi).take (l1.length + n - fi) = l1.drop fi ++ l2.take n := by
  rw [List.drop_append_of_le_length hfi, List.take_append, List.length_drop]
  have h1 : (l1.drop fi).take (l1.length + n - fi) = l1.drop fi :=
    List.take_of_length_le (by rw [List.length_drop]; omega)
  have h2 : l1.length + n - fi - (l1.length - fi) = n := by omega
  rw [h1, h2]

/-- `Items::next` drained from `(fl, fi)` to `(bl, bi)`: the slice of the
chain's entries between the two positions. -/
theorem drainH_sim {h : Heap K V} :
    ∀ (M : List NodeId) (hops : Nat) (L1 L2 : List NodeId) (fl bl : NodeId) (fi bi : Nat),
      M.length + 1 < hops → Linked h none (L1 ++ fl :: (M ++ bl :: L2)) none →
      (L1 ++ fl :: (M ++ bl :: L2)).Nodup → fi ≤ (leafKvs h fl).length →
      bi ≤ (leafKvs h bl).length →
      drainH hops h (fl, fi) (bl, bi) =
        some (((flat h (fl :: (M ++ bl :: L2))).drop fi).take ((flat h (fl :: M)).length + bi - fi)) := by
  intro M
  induction M with
  | nil =>
    intro hops L1 L2 fl bl fi bi hhops hl hnd hfi hbi
    obtain ⟨hops, rfl⟩ : ∃ k, hops = k + 1 := ⟨hops - 1, by omega⟩
    obtain ⟨kvs, hgf⟩ := linked_split_mid (l1 := L1) (l2 := bl :: L2) hl
    have hne : fl ≠ bl := by
      intro heq; subst heq
      rw [nodup_append_iff] at hnd
      exact (List.nodup_cons.mp hnd.2.1).1 (by simp)
    simp only [drainH, Heap.getLeaf_eq hgf, Option.bind_eq_bind, Option.bind_some, List.nil_append,
      List.head?_cons, Option.some_or, beq_iff_eq, hne, if_false]
    obtain ⟨hops, rfl⟩ : ∃ k, hops = k + 1 := ⟨hops - 1, by omega⟩
    obtain ⟨kvsb, hgb⟩ := linked_split_mid (l1 := L1 ++ [fl]) (l2 := L2)
      (by simpa using hl)
    simp only [drainH, Heap.getLeaf_eq hgb, Option.bind_eq_bind, Option.bind_some, beq_self_eq_true,
      if_true, Nat.sub_zero, List.drop_zero]
    rw [leafKvs_eq hgf] at hfi; rw [leafKvs_eq hgb] at hbi
    have e1 : flat h (fl :: bl :: L2) = kvs ++ (kvsb ++ flat h L2) := by
      rw [flat_cons, flat_cons, leafKvs_eq hgf, leafKvs_eq hgb]
    have e2 : (flat h [fl]).length + bi - fi = kvs.length + bi - fi := by
      rw [flat_singleton, leafKvs_eq hgf]
    rw [e1, e2, take_drop_step _ _ _ _ hfi, List.take_append_of_le_length hbi]
  | cons m M ih =>
    intro hops L1 L2 fl bl fi bi hhops hl hnd hfi hbi
    obtain ⟨hops, rfl⟩ : ∃ k, hops = k + 1 := ⟨hops - 1, by omega⟩
    obtain ⟨kvs, hgf⟩ := linked_split_mid (l1 := L1) (l2 := (m :: M) ++ bl :: L2) hl
    have hne : fl ≠ bl := by
      intro heq; subst heq
      rw [nodup_append_iff] at hnd
      exact (List.nodup_cons.mp hnd.2.1).1 (by simp)
    simp only [drainH, Heap.getLeaf_eq hgf, Option.bind_eq_bind, Option.bind_some, List.cons_append,
      List.head?_cons, Option.some_or, beq_iff_eq, hne, if_false]
    have hrec := ih hops (L1 ++ [fl]) L2 m bl 0 bi (by simp at hhops; omega)
      (by simpa using hl) (by simpa using hnd) (Nat.zero_le _) hbi
    rw [hrec]
    simp only [Option.bind_some, List.drop_zero, Nat.sub_zero, Option.some.injEq]
    rw [leafKvs_eq hgf] at hfi
    have e1 : flat h (fl :: m :: (M ++ bl :: L2)) = kvs ++ (leafKvs h m ++ flat h (M ++ bl :: L2)) := by
      rw [flat_cons, flat_cons, leafKvs_eq hgf]
    have e2 : (flat h (fl :: m :: M)).length + bi - fi =
        kvs.length + ((leafKvs h m ++ flat h M).length + bi) - fi := by
      simp only [flat_cons, leafKvs_eq hgf, List.length_append]; omega
    rw [e1, e2, take_drop_step _ _ _ _ hfi]
    simp only [flat_cons]

theorem drop_append_length {α : Type} (l1 l2 : List α) (n : Nat) :
    (l1 ++ l2).drop (l1.length + n) = l2.drop n := by
  rw [List.drop_append, List.drop_of_length_le (by omega), Nat.add_sub_cancel_left, List.nil_append]

theorem length_takeWhile_le' {α : Type} (p : α → Bool) (l : List α) :
    (l.takeWhile p).length ≤ l.length :=
  (List.takeWhile_sublist p).length_le

/-- Under a well-formed root, a chain of two or more leaves has only
nonempty leaves. -/
theorem chain_leaves_nonempty (lc bc : Nat) (hlc : 2 ≤ lc) {d : Nat} {h : Heap K V}
    {root : NodeId} {t : Node K V} {ids lv : List NodeId} {ht : Nat}
    (hsub : Sub h (d + 1) root t ids lv) (hwf : WF lc bc ht true none none t) :
    2 ≤ lv.length → ∀ l ∈ lv, leafKvs h l ≠ [] := by
  intro hlen
  obtain ⟨c0, es, hg⟩ := branch_of_two_leaves hsub hlen
  obtain ⟨t0, ts, -, -, -, rfl, -, -, -⟩ := sub_branch_inv hg hsub
  cases ht with
  | zero => exact absurd hwf (fun x => x)
  | succ g =>
    exact leaves_nonempty lc bc hlc (d + 1) h root _ ids lv (g + 1) true none none hsub hwf
      (Or.inr (Nat.succ_pos g))

/-! ## Resolving the bounds -/

/-- `cut_in_leaf` on the heap: the leaf `leaf_for_key` lands on, with the
tree model's cut, and that leaf's links. -/
theorem cutInLeafH_sim {d fuel : Nat} (hfuel : d + 1 ≤ fuel) {h : Heap K V} {root : NodeId}
    {t : Node K V} {ids lv : List NodeId} (hsub : Sub h (d + 1) root t ids lv)
    (hchain : Linked h none lv none) (k : K) (ae : Bool) :
    ∃ l L1 L2 cut, cutInLeafH fuel h root k ae = some (l, cut, (leafKvs h l).length) ∧
      lv = L1 ++ l :: L2 ∧ cutInLeaf t k ae = (flat h L1, leafKvs h l, cut, flat h L2) ∧
      cut ≤ (leafKvs h l).length ∧
      h.get l = some (.leaf (leafKvs h l) (L1.getLast?.or none) (L2.head?.or none)) := by
  obtain ⟨l, L1, L2, hrun, hlv, hleaf, p, n, hgl⟩ :=
    leafForKeyH_sim k (d + 1) fuel h root t ids lv hfuel hsub
  have hlink := linked_split_mid (hlv ▸ hchain)
  obtain ⟨kvs', hgl'⟩ := hlink
  rw [hgl] at hgl'
  cases hgl'
  refine ⟨l, L1, L2, if ae then ((leafKvs h l).takeWhile fun e => decide (¬ k < e.1)).length
    else ((leafKvs h l).takeWhile fun e => decide (e.1 < k)).length, ?_, hlv, ?_, ?_, hgl⟩
  · simp only [cutInLeafH, hrun, Heap.getLeaf_eq hgl, Option.bind_eq_bind, Option.bind_some]
  · simp only [cutInLeaf, hleaf]
  · split <;> exact length_takeWhile_le' _ _

theorem resolveFrontH_sim {d fuel : Nat} (hfuel : d + 1 ≤ fuel) {h : Heap K V} {root : NodeId}
    {t : Node K V} {ids lv : List NodeId} (hsub : Sub h (d + 1) root t ids lv)
    (hchain : Linked h none lv none) (hne : 2 ≤ lv.length → ∀ l ∈ lv, leafKvs h l ≠ [])
    (start : Bound K) :
    (resolveFrontH fuel h root start = some none ∧ resolveFront t start = none) ∨
    (∃ l i L1 L2, resolveFrontH fuel h root start = some (some (l, i)) ∧ lv = L1 ++ l :: L2 ∧
      resolveFront t start = some ((flat h L1).length + i) ∧ i < (leafKvs h l).length) := by
  -- the two keyed cases share everything but `afterEqual`
  have keyed : ∀ (k : K) (ae : Bool),
      (∃ l L1 L2 cut, cutInLeafH fuel h root k ae = some (l, cut, (leafKvs h l).length) ∧
        lv = L1 ++ l :: L2 ∧ cutInLeaf t k ae = (flat h L1, leafKvs h l, cut, flat h L2) ∧
        h.get l = some (.leaf (leafKvs h l) (L1.getLast?.or none) (L2.head?.or none)) ∧
        ((cut < (leafKvs h l).length ∧ True) ∨
          (¬ cut < (leafKvs h l).length ∧
            ((L2 = [] ∧ flat h L2 = []) ∨
              ∃ n L2', L2 = n :: L2' ∧ flat h L2 ≠ [] ∧ 0 < (leafKvs h n).length ∧
                lv = (L1 ++ [l]) ++ n :: L2' ∧
                (flat h (L1 ++ [l])).length = (flat h L1).length + (leafKvs h l).length)))) := by
    intro k ae
    obtain ⟨l, L1, L2, cut, hrun, hlv, hcut, -, hgl⟩ := cutInLeafH_sim hfuel hsub hchain k ae
    refine ⟨l, L1, L2, cut, hrun, hlv, hcut, hgl, ?_⟩
    by_cases hlt : cut < (leafKvs h l).length
    · exact Or.inl ⟨hlt, trivial⟩
    · refine Or.inr ⟨hlt, ?_⟩
      cases L2 with
      | nil => exact Or.inl ⟨rfl, rfl⟩
      | cons n L2' =>
        have hlen : 2 ≤ lv.length := by rw [hlv]; simp; omega
        have hnne := hne hlen n (by rw [hlv]; simp)
        refine Or.inr ⟨n, L2', rfl, ?_, List.length_pos_iff.mpr hnne, by simp [hlv], ?_⟩
        · rw [flat_cons]; exact List.append_ne_nil_of_left_ne_nil hnne _
        · rw [flat_append, flat_singleton, List.length_append]
  cases start with
  | unbounded =>
    obtain ⟨l, L2, hrun, hlv, hleaf, p, n, hgl⟩ :=
      leftmostLeafH_sim (d + 1) fuel h root t ids lv hfuel hsub
    simp only [resolveFrontH, Bound.key, hrun, Heap.getLeaf_eq hgl, Option.bind_eq_bind,
      Option.bind_some, resolveFront, hleaf]
    by_cases hpos : (leafKvs h l).length > 0
    · right
      exact ⟨l, 0, [], L2, by simp [hpos], hlv, by simp [hpos, flat], hpos⟩
    · left
      simp [hpos]
  | included k =>
    obtain ⟨l, L1, L2, cut, hrun, hlv, hcut, hgl, hcase⟩ := keyed k false
    simp only [resolveFrontH, Bound.key, hrun, Heap.getLeaf_eq hgl, Option.bind_eq_bind,
      Option.bind_some, resolveFront, hcut]
    rcases hcase with ⟨hlt, -⟩ | ⟨hlt, hL2⟩
    · right
      exact ⟨l, cut, L1, L2, by simp [hlt], hlv, by simp [hlt], hlt⟩
    · rcases hL2 with ⟨rfl, hflat⟩ | ⟨n, L2', rfl, hflat, hnpos, hlv', hlen⟩
      · left
        simp [hlt, hflat]
      · right
        refine ⟨n, 0, L1 ++ [l], L2', by simp [hlt], hlv', ?_, hnpos⟩
        simp only [hlt, if_false, hlen, Nat.add_zero]
  | excluded k =>
    obtain ⟨l, L1, L2, cut, hrun, hlv, hcut, hgl, hcase⟩ := keyed k true
    simp only [resolveFrontH, Bound.key, hrun, Heap.getLeaf_eq hgl, Option.bind_eq_bind,
      Option.bind_some, resolveFront, hcut]
    rcases hcase with ⟨hlt, -⟩ | ⟨hlt, hL2⟩
    · right
      exact ⟨l, cut, L1, L2, by simp [hlt], hlv, by simp [hlt], hlt⟩
    · rcases hL2 with ⟨rfl, hflat⟩ | ⟨n, L2', rfl, hflat, hnpos, hlv', hlen⟩
      · left
        simp [hlt, hflat]
      · right
        refine ⟨n, 0, L1 ++ [l], L2', by simp [hlt], hlv', ?_, hnpos⟩
        simp only [hlt, if_false, hlen, Nat.add_zero]

theorem resolveBackH_sim {d fuel : Nat} (hfuel : d + 1 ≤ fuel) {h : Heap K V} {root : NodeId}
    {t : Node K V} {ids lv : List NodeId} (hsub : Sub h (d + 1) root t ids lv)
    (hchain : Linked h none lv none) (hne : 2 ≤ lv.length → ∀ l ∈ lv, leafKvs h l ≠ [])
    (stop : Bound K) :
    (resolveBackH fuel h root stop = some none ∧ resolveBack t stop = none) ∨
    (∃ l i L1 L2, resolveBackH fuel h root stop = some (some (l, i)) ∧ lv = L1 ++ l :: L2 ∧
      resolveBack t stop = some ((flat h L1).length + i) ∧ i ≤ (leafKvs h l).length) := by
  have htl : t.toList = flat h lv := (toList_eq_flat (d + 1)).1 h root t lv hsub.abs hsub.leaves
  have keyed : ∀ (k : K) (ae : Bool),
      (∃ l L1 L2 cut, cutInLeafH fuel h root k ae = some (l, cut, (leafKvs h l).length) ∧
        lv = L1 ++ l :: L2 ∧ cutInLeaf t k ae = (flat h L1, leafKvs h l, cut, flat h L2) ∧
        h.get l = some (.leaf (leafKvs h l) (L1.getLast?.or none) (L2.head?.or none)) ∧
        cut ≤ (leafKvs h l).length ∧
        ((0 < cut ∧ True) ∨
          (¬ 0 < cut ∧
            ((L1 = [] ∧ flat h L1 = []) ∨
              ∃ L1' p, L1 = L1' ++ [p] ∧ flat h L1 ≠ [] ∧
                (∃ pp pn, h.get p = some (.leaf (leafKvs h p) pp pn)) ∧
                lv = L1' ++ p :: (l :: L2) ∧
                (flat h L1).length = (flat h L1').length + (leafKvs h p).length)))) := by
    intro k ae
    obtain ⟨l, L1, L2, cut, hrun, hlv, hcut, hle, hgl⟩ := cutInLeafH_sim hfuel hsub hchain k ae
    refine ⟨l, L1, L2, cut, hrun, hlv, hcut, hgl, hle, ?_⟩
    by_cases hpos : 0 < cut
    · exact Or.inl ⟨hpos, trivial⟩
    · refine Or.inr ⟨hpos, ?_⟩
      rcases L1.eq_nil_or_concat with rfl | ⟨L1', p, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · simp only [List.concat_eq_append] at hlv ⊢
        have hlen : 2 ≤ lv.length := by rw [hlv]; simp; omega
        have hpne := hne hlen p (by rw [hlv]; simp)
        have hlv' : lv = L1' ++ p :: (l :: L2) := by rw [hlv]; simp
        obtain ⟨kvs', hgp⟩ := linked_split_mid (hlv' ▸ hchain)
        refine Or.inr ⟨L1', p, rfl, ?_, ⟨_, _, by rw [leafKvs_eq hgp]; exact hgp⟩, hlv', ?_⟩
        · rw [flat_append, flat_singleton]; exact List.append_ne_nil_of_right_ne_nil _ hpne
        · rw [flat_append, flat_singleton, List.length_append]
  cases stop with
  | unbounded =>
    obtain ⟨l, L1, hrun, hlv, hleaf, p, n, hgl⟩ :=
      rightmostLeafH_sim (d + 1) fuel h root t ids lv hfuel hsub
    simp only [resolveBackH, Bound.key, hrun, Heap.getLeaf_eq hgl, Option.bind_eq_bind,
      Option.bind_some, resolveBack, hleaf]
    by_cases hpos : (leafKvs h l).length > 0
    · right
      refine ⟨l, (leafKvs h l).length, L1, [], by simp [hpos], hlv, ?_, Nat.le_refl _⟩
      simp only [hpos, if_true, htl, hlv, flat_append, flat_singleton, List.length_append]
    · left
      simp [hpos]
  | included k =>
    obtain ⟨l, L1, L2, cut, hrun, hlv, hcut, hgl, hle, hcase⟩ := keyed k true
    simp only [resolveBackH, Bound.key, hrun, Heap.getLeaf_eq hgl, Option.bind_eq_bind,
      Option.bind_some, resolveBack, hcut]
    rcases hcase with ⟨hpos, -⟩ | ⟨hpos, hL1⟩
    · right
      exact ⟨l, cut, L1, L2, by simp [hpos], hlv, by simp [hpos], hle⟩
    · rcases hL1 with ⟨rfl, hflat⟩ | ⟨L1', p, rfl, hflat, ⟨pp, pn, hgp⟩, hlv', hlen⟩
      · left
        simp [hpos, hflat]
      · right
        refine ⟨p, (leafKvs h p).length, L1', l :: L2, ?_, hlv', ?_, Nat.le_refl _⟩
        · simp [hpos, Heap.getLeaf_eq hgp]
        · simp only [hpos, if_false, hlen]
  | excluded k =>
    obtain ⟨l, L1, L2, cut, hrun, hlv, hcut, hgl, hle, hcase⟩ := keyed k false
    simp only [resolveBackH, Bound.key, hrun, Heap.getLeaf_eq hgl, Option.bind_eq_bind,
      Option.bind_some, resolveBack, hcut]
    rcases hcase with ⟨hpos, -⟩ | ⟨hpos, hL1⟩
    · right
      exact ⟨l, cut, L1, L2, by simp [hpos], hlv, by simp [hpos], hle⟩
    · rcases hL1 with ⟨rfl, hflat⟩ | ⟨L1', p, rfl, hflat, ⟨pp, pn, hgp⟩, hlv', hlen⟩
      · left
        simp [hpos, hflat]
      · right
        refine ⟨p, (leafKvs h p).length, L1', l :: L2, ?_, hlv', ?_, Nat.le_refl _⟩
        · simp [hpos, Heap.getLeaf_eq hgp]
        · simp only [hpos, if_false, hlen]

/-! ## `range` -/

/-- The back position is past the front one when the front item is in range. -/
theorem front_lt_back {l : List (K × V)} (hs : Sorted l) (stop : Bound K) {f : Nat}
    {first : K × V} (hf : l[f]? = some first) (hin : stop.admitsTo first = true) :
    f < l.countP stop.admitsTo := by
  have hmono := within_mono hs stop
  have hflt : f < l.length := by
    rcases Nat.lt_or_ge f l.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hf; cases hf
  have hsplit : l = l.take (f + 1) ++ l.drop (f + 1) := (List.take_append_drop _ _).symm
  have htake : l.take (f + 1) = l.take f ++ [first] := by
    rw [List.take_add_one, hf]; rfl
  have hall : ∀ x ∈ l.take (f + 1), stop.admitsTo x = true := by
    intro x hx
    rw [htake] at hx
    rcases List.mem_append.mp hx with hx | hx
    · have hp := hmono
      rw [hsplit, htake, List.pairwise_append] at hp
      obtain ⟨hp1, -, -⟩ := hp
      rw [List.pairwise_append] at hp1
      exact hp1.2.2 x hx first List.mem_cons_self hin
    · rw [List.mem_singleton.mp hx]; exact hin
  have hcount : (l.take (f + 1)).countP stop.admitsTo = f + 1 := by
    rw [List.countP_eq_length.mpr hall, List.length_take_of_le (by omega)]
  calc f < f + 1 := Nat.lt_succ_self f
    _ = (l.take (f + 1)).countP stop.admitsTo := hcount.symm
    _ ≤ (l.take (f + 1)).countP stop.admitsTo + (l.drop (f + 1)).countP stop.admitsTo :=
        Nat.le_add_right _ _
    _ = l.countP stop.admitsTo := by rw [← List.countP_append, List.take_append_drop]

/-- `range` on the heap model yields what the tree model's `range` yields. -/
theorem rangeH_sim (lc bc : Nat) (hlc : 2 ≤ lc) {d fuel hops : Nat} (hfuel : d + 1 ≤ fuel)
    {m : HeapMap K V} {t : Node K V} (hinv : HeapInv m d t) {ht : Nat}
    (hwf : WF lc bc ht true none none t) (hhops : m.count + 2 ≤ hops) (start stop : Bound K) :
    rangeH fuel hops m start stop = some (rangeTree t start stop) := by
  obtain ⟨root, ids, lv, hroot, hsub, hnd, -, -, hchain, hcount⟩ := hinv
  have hsorted := wf_toList_sorted lc bc ht t true none none hwf
  have hlvnd : lv.Nodup :=
    hnd.sublist ((leaf_facts (d + 1)).1 m.heap root ids lv hsub.reach hsub.leaves).2
  have hne := chain_leaves_nonempty lc bc hlc hsub hwf
  have htl : t.toList = flat m.heap lv :=
    (toList_eq_flat (d + 1)).1 m.heap root t lv hsub.abs hsub.leaves
  have hlvlen : lv.length ≤ m.count + 1 := by
    by_cases h2 : 2 ≤ lv.length
    · have := length_le_length_flat (hne h2)
      rw [← htl, ← hcount] at this
      omega
    · omega
  obtain ⟨hFs, -⟩ := resolveFront_spec lc bc ht hlc t hwf start
  obtain ⟨hBs, -⟩ := resolveBack_spec lc bc ht hlc t hwf stop
  simp only [rangeH, hroot, Option.bind_eq_bind, Option.bind_some, rangeTree]
  rcases resolveFrontH_sim hfuel hsub hchain hne start with ⟨hF, hFt⟩ |
    ⟨fl, fi, L1, R, hF, hlv1, hFt, hfi⟩
  · rw [hF, makeItems_eq_front_none hFt]; rfl
  rw [hF]
  simp only [Option.bind_some]
  rcases resolveBackH_sim hfuel hsub hchain hne stop with ⟨hB, hBt⟩ |
    ⟨bl, bi, L1b, Rb, hB, hlv2, hBt, hbi⟩
  · rw [hB, makeItems_eq_back_none hFt hBt]; rfl
  rw [hB]
  simp only [Option.bind_some]
  obtain ⟨kvs, hgf⟩ := linked_split_mid (hlv1 ▸ hchain)
  have hkf : leafKvs m.heap fl = kvs := leafKvs_eq hgf
  rw [hkf] at hfi
  obtain ⟨first, hfirst⟩ : ∃ first, kvs[fi]? = some first := by
    rw [List.getElem?_eq_getElem hfi]; exact ⟨_, rfl⟩
  have htlsplit : t.toList = flat m.heap L1 ++ (kvs ++ flat m.heap R) := by
    rw [htl, hlv1, flat_append, flat_cons, hkf]
  have hfirst' : t.toList[(flat m.heap L1).length + fi]? = some first := by
    rw [htlsplit, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left hfi, hfirst]
  simp only [Heap.getLeaf_eq hgf, hfirst, Option.bind_eq_bind, Option.bind_some]
  rw [makeItems_eq hFt hBt hfirst']
  have tail : stop.admitsTo first = true →
      drainH hops m.heap (fl, fi) (bl, bi) =
        some ((t.toList.drop ((flat m.heap L1).length + fi)).take
          ((flat m.heap L1b).length + bi - ((flat m.heap L1).length + fi))) := by
    intro hin
    have hlt : (flat m.heap L1).length + fi < (flat m.heap L1b).length + bi := by
      rw [hBs _ hBt]
      exact front_lt_back hsorted stop hfirst' hin
    have hdrop : t.toList.drop ((flat m.heap L1).length + fi) = (kvs ++ flat m.heap R).drop fi := by
      rw [htlsplit, drop_append_length]
    have hblmem : bl ∈ lv := by rw [hlv2]; simp
    rw [hlv1] at hblmem
    rcases List.mem_append.mp hblmem with hbl | hbl
    · -- `bl` before `fl`: impossible, the back position would not be past the front
      exfalso
      obtain ⟨P1, P2, hP⟩ := List.append_of_mem hbl
      have heq : L1b ++ bl :: Rb = P1 ++ bl :: (P2 ++ fl :: R) := by
        rw [← hlv2, hlv1, hP]; simp
      obtain ⟨hL1b, -⟩ := split_unique heq (by rw [← hlv2]; exact hlvnd)
      have : (flat m.heap L1).length = (flat m.heap P1).length + (leafKvs m.heap bl).length +
          (flat m.heap P2).length := by
        rw [hP]; simp only [flat_append, flat_cons, List.length_append]; omega
      rw [hL1b] at hlt
      omega
    rcases List.mem_cons.mp hbl with hbf | hbl
    · -- same leaf
      subst hbf
      obtain ⟨hL1eq, -⟩ := split_unique (hlv2.symm.trans hlv1) (by rw [← hlv2]; exact hlvnd)
      obtain ⟨k, rfl⟩ : ∃ k, hops = k + 1 := ⟨hops - 1, by omega⟩
      simp only [drainH, Heap.getLeaf_eq hgf, Option.bind_eq_bind, Option.bind_some,
        beq_self_eq_true, if_true, hdrop, hL1eq, Nat.add_sub_add_left, Option.some.injEq]
      rw [hkf] at hbi
      exact (take_drop_prefix kvs (flat m.heap R) fi bi hbi).symm
    · -- `bl` after `fl`
      obtain ⟨M, L2, rfl⟩ := List.append_of_mem hbl
      have heq : L1b ++ bl :: Rb = (L1 ++ fl :: M) ++ bl :: L2 := by
        rw [← hlv2, hlv1]; simp
      obtain ⟨hL1b, -⟩ := split_unique heq (by rw [← hlv2]; exact hlvnd)
      subst hL1b
      have hM : M.length + 1 < hops := by
        have : lv.length = L1.length + (M.length + L2.length + 2) := by rw [hlv1]; simp; omega
        omega
      have hd := drainH_sim M hops L1 L2 fl bl fi bi hM (hlv1 ▸ hchain) (hlv1 ▸ hlvnd)
        (by rw [hkf]; exact Nat.le_of_lt hfi) hbi
      rw [hd, hdrop]
      have hlen : (flat m.heap (fl :: M)).length + bi - fi =
          (flat m.heap (L1 ++ fl :: M)).length + bi - ((flat m.heap L1).length + fi) := by
        simp only [flat_cons, flat_append, List.length_append]; omega
      rw [hlen, flat_cons, hkf]
  cases stop <;> simp only [Bound.admitsTo] <;> split <;> rename_i hc
  all_goals first
    | exact tail rfl
    | exact absurd (by trivial) hc
    | (simp only [hc, if_true]; exact tail hc)
    | (simp [hc]; done)
    | (simp [hc]; exact tail hc)

end HeapRead

end BPlusTree
