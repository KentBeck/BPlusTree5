import BPlusTree.Model.Heap
import BPlusTree.Proofs.Leaf
import BPlusTree.Proofs.Branch
import BPlusTree.Proofs.Tree
import BPlusTree.Proofs.Read
import BPlusTree.Proofs.Check

/-!
# The heap model: primitives, the sibling chain, and insert

Layered: the store primitives (what a read sees after a write, alloc or
free), the leaf-record helpers, the chain predicate `Linked` with its
append law and what `linkLeafAfter` does to it, frame lemmas for the
abstraction and the id lists, and then the insert simulation.
-/

namespace BPlusTree

open Std

set_option linter.unusedSectionVars false

/-- `omega` does not look through the `NodeId` abbreviation; unfold it first. -/
macro "omega_id" : tactic => `(tactic| ((try dsimp only [NodeId] at *); omega))

section HeapProofs

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-! ## The store -/

namespace Heap

theorem get_write_self {h h' : Heap K V} {id : NodeId} {r : NodeRec K V}
    (hw : h.write id r = some h') : h'.get id = some r := by
  simp only [write] at hw
  split at hw
  · cases hw; simp [get]
  · cases hw

theorem get_write_other {h h' : Heap K V} {id i : NodeId} {r : NodeRec K V}
    (hw : h.write id r = some h') (hne : i ≠ id) : h'.get i = h.get i := by
  simp only [write] at hw
  split at hw
  · cases hw; simp [get, Std.HashMap.getElem?_insert, Ne.symm hne]
  · cases hw

theorem fresh_write {h h' : Heap K V} {id : NodeId} {r : NodeRec K V}
    (hw : h.write id r = some h') : h'.fresh = h.fresh := by
  simp only [write] at hw
  split at hw
  · cases hw; rfl
  · cases hw

theorem write_some {h : Heap K V} {id : NodeId} {r : NodeRec K V}
    (ha : (h.get id).isSome) : ∃ h', h.write id r = some h' := by
  simp only [write, Std.HashMap.contains_eq_isSome_getElem?]
  simp only [get] at ha
  rw [if_pos ha]
  exact ⟨_, rfl⟩

theorem get_alloc_self (h : Heap K V) (r : NodeRec K V) :
    (h.alloc r).2.get (h.alloc r).1 = some r := by
  simp [alloc, get]

theorem get_alloc_other (h : Heap K V) (r : NodeRec K V) {i : NodeId} (hne : i ≠ h.fresh) :
    (h.alloc r).2.get i = h.get i := by
  simp [alloc, get, Std.HashMap.getElem?_insert, Ne.symm hne]

theorem fresh_alloc (h : Heap K V) (r : NodeRec K V) : (h.alloc r).2.fresh = h.fresh + 1 := rfl

theorem fst_alloc (h : Heap K V) (r : NodeRec K V) : (h.alloc r).1 = h.fresh := rfl

theorem get_free_self {h h' : Heap K V} {id : NodeId} (hf : h.free id = some h') :
    h'.get id = none := by
  simp only [free] at hf
  split at hf
  · cases hf; simp [get]
  · cases hf

theorem get_free_other {h h' : Heap K V} {id i : NodeId} (hf : h.free id = some h')
    (hne : i ≠ id) : h'.get i = h.get i := by
  simp only [free] at hf
  split at hf
  · cases hf; simp [get, Std.HashMap.getElem?_erase, Ne.symm hne]
  · cases hf

theorem fresh_free {h h' : Heap K V} {id : NodeId} (hf : h.free id = some h') :
    h'.fresh = h.fresh := by
  simp only [free] at hf
  split at hf
  · cases hf; rfl
  · cases hf

theorem free_some {h : Heap K V} {id : NodeId} (ha : (h.get id).isSome) :
    ∃ h', h.free id = some h' := by
  simp only [free, Std.HashMap.contains_eq_isSome_getElem?]
  simp only [get] at ha
  rw [if_pos ha]
  exact ⟨_, rfl⟩

/-- Every allocated id is below `fresh`. -/
def Bounded (h : Heap K V) : Prop := ∀ i, (h.get i).isSome → i < h.fresh

theorem bounded_write {h h' : Heap K V} {id : NodeId} {r : NodeRec K V}
    (hw : h.write id r = some h') (hb : Bounded h) : Bounded h' := by
  intro i hi
  rw [fresh_write hw]
  by_cases hne : i = id
  · subst hne
    simp only [write] at hw
    split at hw
    · rename_i hc
      apply hb
      simp only [get]
      rw [← Std.HashMap.contains_eq_isSome_getElem?]
      exact hc
    · cases hw
  · rw [get_write_other hw hne] at hi
    exact hb i hi

theorem bounded_alloc {h : Heap K V} (r : NodeRec K V) (hb : Bounded h) :
    Bounded (h.alloc r).2 := by
  intro i hi
  rw [fresh_alloc]
  by_cases hne : i = h.fresh
  · rw [hne]; exact Nat.lt_succ_self _
  · rw [get_alloc_other h r hne] at hi
    exact Nat.lt_succ_of_lt (hb i hi)

theorem bounded_free {h h' : Heap K V} {id : NodeId} (hf : h.free id = some h')
    (hb : Bounded h) : Bounded h' := by
  intro i hi
  rw [fresh_free hf]
  by_cases hne : i = id
  · subst hne; rw [get_free_self hf] at hi; cases hi
  · rw [get_free_other hf hne] at hi
    exact hb i hi

theorem not_allocated_of_bounded {h : Heap K V} (hb : Bounded h) {i : NodeId}
    (hi : h.fresh ≤ i) : h.get i = none := by
  rcases hg : h.get i with _ | r
  · rfl
  · have := hb i (by simp [hg])
    exact absurd (Nat.lt_of_lt_of_le this hi) (Nat.lt_irrefl _)

/-! ### Leaf helpers -/

theorem getLeaf_eq {h : Heap K V} {id : NodeId} {kvs : Leaf K V} {p n : Option NodeId}
    (hg : h.get id = some (.leaf kvs p n)) : h.getLeaf id = some (kvs, p, n) := by
  simp [getLeaf, hg]

theorem getLeaf_some {h : Heap K V} {id : NodeId} {kvs : Leaf K V} {p n : Option NodeId}
    (hl : h.getLeaf id = some (kvs, p, n)) : h.get id = some (.leaf kvs p n) := by
  simp only [getLeaf] at hl
  split at hl
  · rename_i kvs' p' n' hg
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact hg
  · cases hl

/-- `setPrev` on an allocated leaf: only that record's `prev` changes. -/
theorem setPrev_spec {h : Heap K V} {id : NodeId} {kvs : Leaf K V} {p n : Option NodeId}
    (hg : h.get id = some (.leaf kvs p n)) (p' : Option NodeId) :
    ∃ h', h.setPrev id p' = some h' ∧ h'.get id = some (.leaf kvs p' n) ∧
      (∀ i, i ≠ id → h'.get i = h.get i) ∧ h'.fresh = h.fresh := by
  simp only [setPrev, getLeaf_eq hg]
  obtain ⟨h', hw⟩ := write_some (h := h) (id := id) (r := .leaf kvs p' n) (by simp [hg])
  exact ⟨h', hw, get_write_self hw, fun i hi => get_write_other hw hi, fresh_write hw⟩

theorem setNext_spec {h : Heap K V} {id : NodeId} {kvs : Leaf K V} {p n : Option NodeId}
    (hg : h.get id = some (.leaf kvs p n)) (n' : Option NodeId) :
    ∃ h', h.setNext id n' = some h' ∧ h'.get id = some (.leaf kvs p n') ∧
      (∀ i, i ≠ id → h'.get i = h.get i) ∧ h'.fresh = h.fresh := by
  simp only [setNext, getLeaf_eq hg]
  obtain ⟨h', hw⟩ := write_some (h := h) (id := id) (r := .leaf kvs p n') (by simp [hg])
  exact ⟨h', hw, get_write_self hw, fun i hi => get_write_other hw hi, fresh_write hw⟩

theorem setLeaf_spec {h : Heap K V} {id : NodeId} {kvs : Leaf K V} {p n : Option NodeId}
    (hg : h.get id = some (.leaf kvs p n)) (kvs' : Leaf K V) :
    ∃ h', h.setLeaf id kvs' = some h' ∧ h'.get id = some (.leaf kvs' p n) ∧
      (∀ i, i ≠ id → h'.get i = h.get i) ∧ h'.fresh = h.fresh := by
  simp only [setLeaf, getLeaf_eq hg]
  obtain ⟨h', hw⟩ := write_some (h := h) (id := id) (r := .leaf kvs' p n) (by simp [hg])
  exact ⟨h', hw, get_write_self hw, fun i hi => get_write_other hw hi, fresh_write hw⟩

end Heap

/-! ## The sibling chain -/

/-- The leaves `l` are chained from `prev` to `next`: each one's `prev` is
the one before it (`prev` for the first) and its `next` the one after
(`next` for the last). -/
def Linked (h : Heap K V) : Option NodeId → List NodeId → Option NodeId → Prop
  | _, [], _ => True
  | prev, id :: rest, next =>
    (∃ kvs, h.get id = some (.leaf kvs prev (rest.head?.or next))) ∧
      Linked h (some id) rest next

theorem getLast?_cons_or {α : Type} (a : α) (l : List α) :
    (a :: l).getLast? = l.getLast?.or (some a) := by
  rw [List.getLast?_cons]
  cases l.getLast? <;> rfl

theorem linked_append (h : Heap K V) (prev next : Option NodeId) (l1 l2 : List NodeId) :
    Linked h prev (l1 ++ l2) next ↔
      Linked h prev l1 (l2.head?.or next) ∧ Linked h (l1.getLast?.or prev) l2 next := by
  induction l1 generalizing prev with
  | nil => simp [Linked]
  | cons a t ih =>
    simp only [List.cons_append, Linked, getLast?_cons_or]
    have hhead : (t ++ l2).head?.or next = t.head?.or (l2.head?.or next) := by
      cases t <;> simp [Option.or]
    rw [hhead, ih (some a)]
    have : t.getLast?.or (some a) = (t.getLast?.or (some a)).or prev := by
      cases t.getLast? <;> rfl
    rw [← this]
    constructor
    · rintro ⟨hr, h1, h2⟩; exact ⟨⟨hr, h1⟩, h2⟩
    · rintro ⟨⟨hr, h1⟩, h2⟩; exact ⟨hr, h1, h2⟩

/-- `Linked` reads only the records of the listed leaves. -/
theorem linked_congr {h h' : Heap K V} {prev next : Option NodeId} {l : List NodeId}
    (hsame : ∀ i ∈ l, h'.get i = h.get i) : Linked h prev l next → Linked h' prev l next := by
  induction l generalizing prev with
  | nil => intro; trivial
  | cons a t ih =>
    rintro ⟨⟨kvs, hr⟩, hrest⟩
    refine ⟨⟨kvs, ?_⟩, ih (fun i hi => hsame i (List.mem_cons_of_mem _ hi)) hrest⟩
    rw [hsame a List.mem_cons_self]; exact hr

theorem linked_mem_leaf {h : Heap K V} {prev next : Option NodeId} {l : List NodeId}
    (hl : Linked h prev l next) {i : NodeId} (hi : i ∈ l) :
    ∃ kvs p n, h.get i = some (.leaf kvs p n) := by
  induction l generalizing prev with
  | nil => cases hi
  | cons a t ih =>
    obtain ⟨⟨kvs, hr⟩, hrest⟩ := hl
    rcases List.mem_cons.mp hi with rfl | hi
    · exact ⟨kvs, _, _, hr⟩
    · exact ih hrest hi

/-- The records `Linked` fixes for a single leaf. -/
theorem linked_singleton {h : Heap K V} {prev next : Option NodeId} {id : NodeId} :
    Linked h prev [id] next ↔ ∃ kvs, h.get id = some (.leaf kvs prev next) := by
  simp [Linked, Option.or]

/-- What `linkLeafAfter` does: `leaf`'s `next` becomes `right`, `right` is
linked between `leaf` and `leaf`'s old successor, whose `prev` becomes
`right`; nothing else changes. -/
theorem linkLeafAfter_spec {h : Heap K V} {leaf right : NodeId} {L R : Leaf K V}
    {prev oldNext pr nr : Option NodeId}
    (hleaf : h.get leaf = some (.leaf L prev oldNext))
    (hright : h.get right = some (.leaf R pr nr)) (hne : right ≠ leaf)
    (hold : ∀ o, oldNext = some o → o ≠ leaf ∧ o ≠ right ∧
      ∃ O po no, h.get o = some (.leaf O po no)) :
    ∃ h', linkLeafAfter h leaf right = some h' ∧
      h'.get leaf = some (.leaf L prev (some right)) ∧
      h'.get right = some (.leaf R (some leaf) oldNext) ∧
      (∀ o O po no, oldNext = some o → h.get o = some (.leaf O po no) →
        h'.get o = some (.leaf O (some right) no)) ∧
      (∀ i, i ≠ leaf → i ≠ right → oldNext ≠ some i → h'.get i = h.get i) ∧
      h'.fresh = h.fresh := by
  simp only [linkLeafAfter, Heap.getLeaf_eq hleaf, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨h1, hs1, hg1, ho1, hf1⟩ := Heap.setNext_spec hleaf (some right)
  rw [hs1]; simp only [Option.bind_some]
  have hright1 : h1.get right = some (.leaf R pr nr) := by rw [ho1 right hne]; exact hright
  obtain ⟨h2, hs2, hg2, ho2, hf2⟩ := Heap.setNext_spec hright1 oldNext
  rw [hs2]; simp only [Option.bind_some]
  obtain ⟨h3, hs3, hg3, ho3, hf3⟩ := Heap.setPrev_spec hg2 (some leaf)
  rw [hs3]; simp only [Option.bind_some]
  have hleaf3 : h3.get leaf = some (.leaf L prev (some right)) := by
    rw [ho3 leaf (Ne.symm hne), ho2 leaf (Ne.symm hne)]; exact hg1
  rcases oldNext with _ | o
  · refine ⟨h3, rfl, hleaf3, hg3, (fun o _ _ _ h => by cases h), ?_, by rw [hf3, hf2, hf1]⟩
    intro i hi1 hi2 _
    rw [ho3 i hi2, ho2 i hi2, ho1 i hi1]
  · obtain ⟨hol, hor, O, po, no, hgo⟩ := hold o rfl
    have hgo3 : h3.get o = some (.leaf O po no) := by
      rw [ho3 o hor, ho2 o hor, ho1 o hol]; exact hgo
    obtain ⟨h4, hs4, hg4, ho4, hf4⟩ := Heap.setPrev_spec hgo3 (some right)
    refine ⟨h4, hs4, ?_, ?_, ?_, ?_, by rw [hf4, hf3, hf2, hf1]⟩
    · rw [ho4 leaf (Ne.symm hol)]; exact hleaf3
    · rw [ho4 right (Ne.symm hor)]; exact hg3
    · intro o' O' po' no' ho' hgo'
      cases ho'
      rw [hgo] at hgo'
      cases hgo'
      exact hg4
    · intro i hi1 hi2 hi3
      have hio : i ≠ o := fun heq => hi3 (by rw [heq])
      rw [ho4 i hio, ho3 i hi2, ho2 i hi2, ho1 i hi1]

/-! ## The abstraction and the id lists -/

/-- Records that agree up to a leaf's links: what the abstraction and
the id walks see. -/
def SameContent : Option (NodeRec K V) → Option (NodeRec K V) → Prop
  | some (.leaf kvs _ _), some (.leaf kvs' _ _) => kvs = kvs'
  | a, b => a = b

theorem sameContent_refl (r : Option (NodeRec K V)) : SameContent r r := by
  rcases r with _ | (_ | _) <;> simp [SameContent]

theorem sameContent_of_eq {r r' : Option (NodeRec K V)} (h : r' = r) : SameContent r r' := by
  subst h; exact sameContent_refl _

theorem sameContent_leaf {kvs : Leaf K V} {p n p' n' : Option NodeId} :
    SameContent (some (.leaf kvs p n)) (some (.leaf kvs p' n')) := rfl

theorem sameContent_leaf_inv {kvs : Leaf K V} {p n : Option NodeId} {r : Option (NodeRec K V)}
    (h : SameContent (some (.leaf kvs p n)) r) : ∃ p' n', r = some (.leaf kvs p' n') := by
  rcases r with _ | (_ | _)
  · cases h
  · rename_i kvs' p' n'
    simp only [SameContent] at h
    subst h
    exact ⟨p', n', rfl⟩
  · cases h

theorem sameContent_branch_inv {c0 : NodeId} {es : List (K × NodeId)} {r : Option (NodeRec K V)}
    (h : SameContent (some (.branch c0 es)) r) : r = some (.branch c0 es) := by
  rcases r with _ | (_ | _)
  · cases h
  · cases h
  · exact h.symm

/-! ### Unfolding -/

theorem absNode_leaf {h : Heap K V} {id : NodeId} {kvs : Leaf K V} {p n : Option NodeId}
    (hg : h.get id = some (.leaf kvs p n)) (d : Nat) :
    absNode (d + 1) h id = some (.leaf kvs) := by
  simp [absNode, hg]

theorem absNode_branch {h : Heap K V} {id : NodeId} {c0 : NodeId} {es : List (K × NodeId)}
    (hg : h.get id = some (.branch c0 es)) (d : Nat) :
    absNode (d + 1) h id =
      (absNode d h c0).bind fun c0' =>
        (absNode.absEntries d h es).bind fun es' => some (.branch c0' es') := by
  simp [absNode, hg]

theorem reachIds_leaf {h : Heap K V} {id : NodeId} {kvs : Leaf K V} {p n : Option NodeId}
    (hg : h.get id = some (.leaf kvs p n)) (d : Nat) : reachIds (d + 1) h id = some [id] := by
  simp [reachIds, hg]

theorem reachIds_branch {h : Heap K V} {id : NodeId} {c0 : NodeId} {es : List (K × NodeId)}
    (hg : h.get id = some (.branch c0 es)) (d : Nat) :
    reachIds (d + 1) h id =
      (reachIds.reachChildren d h (c0 :: es.map (·.2))).map fun below => id :: below := by
  simp only [reachIds, hg]
  cases reachIds.reachChildren d h (c0 :: es.map (·.2)) <;> rfl

theorem leafIds_leaf {h : Heap K V} {id : NodeId} {kvs : Leaf K V} {p n : Option NodeId}
    (hg : h.get id = some (.leaf kvs p n)) (d : Nat) : leafIds (d + 1) h id = some [id] := by
  simp [leafIds, hg]

theorem leafIds_branch {h : Heap K V} {id : NodeId} {c0 : NodeId} {es : List (K × NodeId)}
    (hg : h.get id = some (.branch c0 es)) (d : Nat) :
    leafIds (d + 1) h id = leafIds.leafChildren d h (c0 :: es.map (·.2)) := by
  simp [leafIds, hg]

/-! ### Append laws for the children walks -/

theorem reachChildren_append (d : Nat) (h : Heap K V) (l1 l2 : List NodeId) :
    reachIds.reachChildren d h (l1 ++ l2) =
      (reachIds.reachChildren d h l1).bind fun a =>
        (reachIds.reachChildren d h l2).bind fun b => some (a ++ b) := by
  induction l1 with
  | nil =>
    simp only [List.nil_append, reachIds.reachChildren]
    cases reachIds.reachChildren d h l2 <;> rfl
  | cons c rest ih =>
    simp only [List.cons_append, reachIds.reachChildren, ih]
    cases reachIds d h c <;> simp only [Option.bind_eq_bind, Option.bind_none, Option.bind_some]
    cases reachIds.reachChildren d h rest <;> simp only [Option.bind_none, Option.bind_some]
    cases reachIds.reachChildren d h l2 <;> simp [Option.bind_none, Option.bind_some, List.append_assoc]

theorem leafChildren_append (d : Nat) (h : Heap K V) (l1 l2 : List NodeId) :
    leafIds.leafChildren d h (l1 ++ l2) =
      (leafIds.leafChildren d h l1).bind fun a =>
        (leafIds.leafChildren d h l2).bind fun b => some (a ++ b) := by
  induction l1 with
  | nil =>
    simp only [List.nil_append, leafIds.leafChildren]
    cases leafIds.leafChildren d h l2 <;> rfl
  | cons c rest ih =>
    simp only [List.cons_append, leafIds.leafChildren, ih]
    cases leafIds d h c <;> simp only [Option.bind_eq_bind, Option.bind_none, Option.bind_some]
    cases leafIds.leafChildren d h rest <;> simp only [Option.bind_none, Option.bind_some]
    cases leafIds.leafChildren d h l2 <;> simp [Option.bind_none, Option.bind_some, List.append_assoc]

theorem absEntries_append (d : Nat) (h : Heap K V) (l1 l2 : List (K × NodeId)) :
    absNode.absEntries d h (l1 ++ l2) =
      (absNode.absEntries d h l1).bind fun a =>
        (absNode.absEntries d h l2).bind fun b => some (a ++ b) := by
  induction l1 with
  | nil =>
    simp only [List.nil_append, absNode.absEntries]
    cases absNode.absEntries d h l2 <;> rfl
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    simp only [List.cons_append, absNode.absEntries, ih]
    cases absNode d h c <;> simp only [Option.bind_eq_bind, Option.bind_none, Option.bind_some]
    cases absNode.absEntries d h rest <;> simp only [Option.bind_none, Option.bind_some]
    cases absNode.absEntries d h l2 <;> simp [Option.bind_none, Option.bind_some]

/-! ### Membership in the walks -/

theorem mem_reachIds_self {d : Nat} {h : Heap K V} {id : NodeId} {ids : List NodeId}
    (hr : reachIds d h id = some ids) : id ∈ ids := by
  cases d with
  | zero => simp [reachIds] at hr
  | succ d =>
    simp only [reachIds] at hr
    split at hr
    · cases hr
    · cases hr; simp
    · cases hb : reachIds.reachChildren d h _ <;> rw [hb] at hr
      · cases hr
      · cases hr; simp

theorem reachIds_allocated {d : Nat} {h : Heap K V} {id : NodeId} {ids : List NodeId}
    (hr : reachIds d h id = some ids) : (h.get id).isSome := by
  cases d with
  | zero => simp [reachIds] at hr
  | succ d =>
    simp only [reachIds] at hr
    split at hr
    · cases hr
    · rename_i hg; simp [hg]
    · rename_i hg; simp [hg]

/-- Everything a walk from `c` visits is allocated. -/
theorem mem_reachIds_allocated (d : Nat) :
    ∀ (h : Heap K V) (id : NodeId) (ids : List NodeId), reachIds d h id = some ids →
      ∀ i ∈ ids, (h.get i).isSome := by
  induction d with
  | zero => intro h id ids hr; simp [reachIds] at hr
  | succ d ih =>
    intro h id ids hr i hi
    simp only [reachIds] at hr
    split at hr
    · cases hr
    · rename_i hg
      cases hr
      rw [List.mem_singleton.mp hi]; simp [hg]
    · rename_i c0 es hg
      cases hb : reachIds.reachChildren d h (c0 :: es.map (·.2)) <;> rw [hb] at hr
      · cases hr
      · rename_i below
        cases hr
        rcases List.mem_cons.mp hi with rfl | hi
        · simp [hg]
        · -- walk the children
          have : ∀ (cs : List NodeId) (below : List NodeId),
              reachIds.reachChildren d h cs = some below → ∀ i ∈ below, (h.get i).isSome := by
            intro cs
            induction cs with
            | nil =>
              intro below hb i hi
              simp only [reachIds.reachChildren, Option.some.injEq] at hb
              subst hb; cases hi
            | cons c rest ihc =>
              intro below hb i hi
              simp only [reachIds.reachChildren] at hb
              cases hc : reachIds d h c <;> rw [hc] at hb
              · cases hb
              · cases hr : reachIds.reachChildren d h rest <;> rw [hr] at hb
                · cases hb
                · cases hb
                  rcases List.mem_append.mp hi with hi | hi
                  · exact ih h c _ hc i hi
                  · exact ihc _ hr i hi
          exact this _ _ hb i hi

/-! ### Frame lemmas: the walks read only the subtree's records -/

theorem absEntries_congr {d : Nat} {h h' : Heap K V} {es : List (K × NodeId)}
    (hes : ∀ e ∈ es, absNode d h' e.2 = absNode d h e.2) :
    absNode.absEntries d h' es = absNode.absEntries d h es := by
  induction es with
  | nil => simp [absNode.absEntries]
  | cons e rest ihe =>
    obtain ⟨s, c⟩ := e
    simp only [absNode.absEntries]
    rw [hes (s, c) List.mem_cons_self, ihe (fun e he => hes e (List.mem_cons_of_mem _ he))]

/-- Records agreeing (up to links) on every id a walk visits give the same
walk, the same abstraction, and the same leaf list. -/
theorem walks_congr (d : Nat) :
    ∀ (h h' : Heap K V) (id : NodeId) (ids : List NodeId),
      reachIds d h id = some ids → (∀ i ∈ ids, SameContent (h.get i) (h'.get i)) →
      reachIds d h' id = some ids ∧ absNode d h' id = absNode d h id ∧
        leafIds d h' id = leafIds d h id := by
  induction d with
  | zero => intro h h' id ids hr; simp [reachIds] at hr
  | succ d ih =>
    intro h h' id ids hr hsame
    have hself := hsame id (mem_reachIds_self hr)
    rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
    · simp [reachIds, hg] at hr
    · rw [hg] at hself
      obtain ⟨p', n', hg'⟩ := sameContent_leaf_inv hself
      rw [reachIds_leaf hg] at hr
      cases hr
      rw [reachIds_leaf hg', absNode_leaf hg', absNode_leaf hg, leafIds_leaf hg', leafIds_leaf hg]
      exact ⟨rfl, rfl, rfl⟩
    · rw [hg] at hself
      have hg' := sameContent_branch_inv hself
      rw [reachIds_branch hg] at hr
      cases hb : reachIds.reachChildren d h (c0 :: es.map (·.2)) <;> rw [hb] at hr
      · cases hr
      · rename_i below
        simp only [Option.map_some, Option.some.injEq] at hr
        subst hr
        have hsame' : ∀ i ∈ below, SameContent (h.get i) (h'.get i) :=
          fun i hi => hsame i (List.mem_cons_of_mem _ hi)
        -- the children one by one
        have hch : ∀ (cs : List NodeId) (below : List NodeId),
            reachIds.reachChildren d h cs = some below →
            (∀ i ∈ below, SameContent (h.get i) (h'.get i)) →
            reachIds.reachChildren d h' cs = some below ∧
              (∀ c ∈ cs, absNode d h' c = absNode d h c) ∧
              leafIds.leafChildren d h' cs = leafIds.leafChildren d h cs := by
          intro cs
          induction cs with
          | nil =>
            intro below hb _
            simp only [reachIds.reachChildren, Option.some.injEq] at hb
            subst hb
            exact ⟨by simp [reachIds.reachChildren], (fun c hc => by cases hc),
              by simp [leafIds.leafChildren]⟩
          | cons c rest ihc =>
            intro below hb hs
            simp only [reachIds.reachChildren] at hb
            cases hc : reachIds d h c <;> rw [hc] at hb
            · cases hb
            · rename_i lc
              cases hr : reachIds.reachChildren d h rest <;> rw [hr] at hb
              · cases hb
              · rename_i lr
                cases hb
                obtain ⟨hc', ha', hl'⟩ := ih h h' c lc hc
                  (fun i hi => hs i (List.mem_append_left _ hi))
                obtain ⟨hr', har', hlr'⟩ := ihc lr hr (fun i hi => hs i (List.mem_append_right _ hi))
                refine ⟨?_, ?_, ?_⟩
                · simp [reachIds.reachChildren, hc', hr']
                · intro x hx
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact ha'
                  · exact har' x hx
                · simp only [leafIds.leafChildren, hl', hlr']
        obtain ⟨hb', habs, hlv⟩ := hch _ _ hb hsame'
        refine ⟨?_, ?_, ?_⟩
        · rw [reachIds_branch hg', hb']; rfl
        · rw [absNode_branch hg', absNode_branch hg, habs c0 List.mem_cons_self]
          rw [absEntries_congr (fun e he =>
            habs e.2 (List.mem_cons_of_mem _ (List.mem_map_of_mem he)))]
        · rw [leafIds_branch hg', leafIds_branch hg, hlv]

theorem children_congr (d : Nat) {h h' : Heap K V} (cs L : List NodeId)
    (hb : reachIds.reachChildren d h cs = some L)
    (hsame : ∀ i ∈ L, SameContent (h.get i) (h'.get i)) :
    reachIds.reachChildren d h' cs = some L ∧
      (∀ c ∈ cs, absNode d h' c = absNode d h c) ∧
      leafIds.leafChildren d h' cs = leafIds.leafChildren d h cs := by
  induction cs generalizing L with
  | nil =>
    simp only [reachIds.reachChildren, Option.some.injEq] at hb
    subst hb
    exact ⟨by simp [reachIds.reachChildren], (fun c hc => by cases hc),
      by simp [leafIds.leafChildren]⟩
  | cons c rest ihc =>
    simp only [reachIds.reachChildren] at hb
    cases hc : reachIds d h c <;> rw [hc] at hb
    · cases hb
    · rename_i lc
      cases hr : reachIds.reachChildren d h rest <;> rw [hr] at hb
      · cases hb
      · rename_i lr
        cases hb
        obtain ⟨hc', ha', hl'⟩ := walks_congr d h h' c lc hc
          (fun i hi => hsame i (List.mem_append_left _ hi))
        obtain ⟨hr', har', hlr'⟩ := ihc lr hr (fun i hi => hsame i (List.mem_append_right _ hi))
        refine ⟨by simp [reachIds.reachChildren, hc', hr'], ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha'
          · exact har' x hx
        · simp only [leafIds.leafChildren, hl', hlr']

/-! ### Leaf ids sit among the reachable ids, and there is always one -/

theorem leaf_facts (d : Nat) :
    (∀ (h : Heap K V) (id : NodeId) (ids lv : List NodeId),
      reachIds d h id = some ids → leafIds d h id = some lv → lv ≠ [] ∧ lv.Sublist ids) ∧
    (∀ (h : Heap K V) (cs L lv : List NodeId),
      reachIds.reachChildren d h cs = some L → leafIds.leafChildren d h cs = some lv →
        (cs ≠ [] → lv ≠ []) ∧ lv.Sublist L) := by
  induction d with
  | zero =>
    refine ⟨fun h id ids lv hr => by simp [reachIds] at hr, ?_⟩
    intro h cs L lv hr hl
    cases cs with
    | nil =>
      simp only [reachIds.reachChildren, leafIds.leafChildren, Option.some.injEq] at hr hl
      subst hr; subst hl
      exact ⟨fun h => absurd rfl h, List.Sublist.refl _⟩
    | cons c rest => simp [reachIds.reachChildren, reachIds] at hr
  | succ d ih =>
    have hch : ∀ (h : Heap K V) (cs L lv : List NodeId),
        reachIds.reachChildren (d + 1) h cs = some L →
        leafIds.leafChildren (d + 1) h cs = some lv →
        (cs ≠ [] → lv ≠ []) ∧ lv.Sublist L := by
      intro h cs
      induction cs with
      | nil =>
        intro L lv hr hl
        simp only [reachIds.reachChildren, leafIds.leafChildren, Option.some.injEq] at hr hl
        subst hr; subst hl
        exact ⟨fun h => absurd rfl h, List.Sublist.refl _⟩
      | cons c rest ihc =>
        intro L lv hr hl
        simp only [reachIds.reachChildren, leafIds.leafChildren] at hr hl
        cases hc : reachIds (d + 1) h c <;> rw [hc] at hr
        · cases hr
        · rename_i lc
          cases hcl : leafIds (d + 1) h c <;> rw [hcl] at hl
          · cases hl
          · rename_i lvc
            cases hrr : reachIds.reachChildren (d + 1) h rest <;> rw [hrr] at hr
            · cases hr
            · rename_i lr
              cases hlr : leafIds.leafChildren (d + 1) h rest <;> rw [hlr] at hl
              · cases hl
              · rename_i lvr
                cases hr; cases hl
                -- the node statement at d + 1, unfolded by hand
                have hnode : lvc ≠ [] ∧ lvc.Sublist lc := by
                  rcases hg : h.get c with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
                  · simp [reachIds, hg] at hc
                  · rw [reachIds_leaf hg] at hc; rw [leafIds_leaf hg] at hcl
                    cases hc; cases hcl
                    exact ⟨by simp, List.Sublist.refl _⟩
                  · rw [reachIds_branch hg] at hc; rw [leafIds_branch hg] at hcl
                    cases hb : reachIds.reachChildren d h (c0 :: es.map (·.2)) <;> rw [hb] at hc
                    · cases hc
                    · rename_i below
                      simp only [Option.map_some, Option.some.injEq] at hc
                      subst hc
                      obtain ⟨hne, hsub⟩ := ih.2 h _ _ _ hb hcl
                      exact ⟨hne (by simp), List.Sublist.cons _ hsub⟩
                obtain ⟨_, hsubr⟩ := ihc lr lvr hrr hlr
                refine ⟨fun _ => ?_, hnode.2.append hsubr⟩
                intro hnil
                exact hnode.1 (List.eq_nil_of_append_eq_nil hnil).1
    refine ⟨?_, hch⟩
    intro h id ids lv hr hl
    rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
    · simp [reachIds, hg] at hr
    · rw [reachIds_leaf hg] at hr; rw [leafIds_leaf hg] at hl
      cases hr; cases hl
      exact ⟨by simp, List.Sublist.refl _⟩
    · rw [reachIds_branch hg] at hr; rw [leafIds_branch hg] at hl
      cases hb : reachIds.reachChildren d h (c0 :: es.map (·.2)) <;> rw [hb] at hr
      · cases hr
      · rename_i below
        simp only [Option.map_some, Option.some.injEq] at hr
        subst hr
        obtain ⟨hne, hsub⟩ := ih.2 h _ _ _ hb hl
        exact ⟨hne (by simp), List.Sublist.cons _ hsub⟩

/-! ### The children list around the child `child_for_key` picks -/

/-- The children before the one `lastChild` picks. -/
def frontIds (c : NodeId) : List (K × NodeId) → List NodeId
  | [] => []
  | (_, ch) :: rest => c :: frontIds ch rest

theorem cons_map_eq_front_last (c0 : NodeId) (A : List (K × NodeId)) :
    c0 :: A.map (·.2) = frontIds c0 A ++ [lastChild c0 A] := by
  induction A generalizing c0 with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    simp only [List.map_cons, frontIds, lastChild, List.cons_append]
    rw [ih c]

theorem takeWhile_append_dropWhile_entries (k : K) (es : List (K × NodeId)) :
    es = es.takeWhile (sepLE k) ++ es.dropWhile (sepLE k) :=
  List.takeWhile_append_dropWhile.symm

/-! ### Abstraction commutes with the tree model's list operations -/

theorem absEntries_length {d : Nat} {h : Heap K V} {es : List (K × NodeId)}
    {ts : List (K × Node K V)} (he : absNode.absEntries d h es = some ts) :
    ts.length = es.length := by
  induction es generalizing ts with
  | nil => simp only [absNode.absEntries, Option.some.injEq] at he; subst he; rfl
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    simp only [absNode.absEntries] at he
    cases hc : absNode d h c <;> rw [hc] at he
    · cases he
    · cases hr : absNode.absEntries d h rest <;> rw [hr] at he
      · cases he
      · cases he; simp [ih hr]

theorem absEntries_keys {d : Nat} {h : Heap K V} {es : List (K × NodeId)}
    {ts : List (K × Node K V)} (he : absNode.absEntries d h es = some ts) :
    ts.map Prod.fst = es.map Prod.fst := by
  induction es generalizing ts with
  | nil => simp only [absNode.absEntries, Option.some.injEq] at he; subst he; rfl
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    simp only [absNode.absEntries] at he
    cases hc : absNode d h c <;> rw [hc] at he
    · cases he
    · cases hr : absNode.absEntries d h rest <;> rw [hr] at he
      · cases he
      · cases he; simp [ih hr]

theorem absEntries_cons_inv {d : Nat} {h : Heap K V} {s : K} {c : NodeId}
    {rest : List (K × NodeId)} {ts : List (K × Node K V)}
    (he : absNode.absEntries d h ((s, c) :: rest) = some ts) :
    ∃ tc tr, absNode d h c = some tc ∧ absNode.absEntries d h rest = some tr ∧
      ts = (s, tc) :: tr := by
  simp only [absNode.absEntries] at he
  cases hc : absNode d h c <;> rw [hc] at he
  · cases he
  · cases hr : absNode.absEntries d h rest <;> rw [hr] at he
    · cases he
    · cases he; exact ⟨_, _, rfl, rfl, rfl⟩

theorem absEntries_cons {d : Nat} {h : Heap K V} {s : K} {c : NodeId} {rest : List (K × NodeId)}
    {tc : Node K V} {tr : List (K × Node K V)} (hc : absNode d h c = some tc)
    (hr : absNode.absEntries d h rest = some tr) :
    absNode.absEntries d h ((s, c) :: rest) = some ((s, tc) :: tr) := by
  simp [absNode.absEntries, hc, hr]

theorem absEntries_takeWhile {d : Nat} {h : Heap K V} (k : K) {es : List (K × NodeId)}
    {ts : List (K × Node K V)} (he : absNode.absEntries d h es = some ts) :
    absNode.absEntries d h (es.takeWhile (sepLE k)) = some (ts.takeWhile (sepLE k)) ∧
      absNode.absEntries d h (es.dropWhile (sepLE k)) = some (ts.dropWhile (sepLE k)) := by
  induction es generalizing ts with
  | nil =>
    simp only [absNode.absEntries, Option.some.injEq] at he
    subst he; simp [absNode.absEntries]
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨tc, tr, hc, hr, rfl⟩ := absEntries_cons_inv he
    obtain ⟨ih1, ih2⟩ := ih hr
    by_cases hs : sepLE k (s, c) = true
    · have hs' : sepLE k (s, tc) = true := hs
      rw [List.takeWhile_cons_of_pos hs, List.takeWhile_cons_of_pos hs',
        List.dropWhile_cons_of_pos hs, List.dropWhile_cons_of_pos hs']
      exact ⟨absEntries_cons hc ih1, ih2⟩
    · have hs' : ¬ sepLE k (s, tc) = true := hs
      rw [List.takeWhile_cons_of_neg hs, List.takeWhile_cons_of_neg hs',
        List.dropWhile_cons_of_neg hs, List.dropWhile_cons_of_neg hs']
      exact ⟨by simp [absNode.absEntries], absEntries_cons hc hr⟩

theorem absNode_lastChild {d : Nat} {h : Heap K V} {c0 : NodeId} {t0 : Node K V}
    {A : List (K × NodeId)} {tsA : List (K × Node K V)} (h0 : absNode d h c0 = some t0)
    (hA : absNode.absEntries d h A = some tsA) :
    absNode d h (lastChild c0 A) = some (lastChild t0 tsA) := by
  induction A generalizing c0 t0 tsA with
  | nil =>
    simp only [absNode.absEntries, Option.some.injEq] at hA
    subst hA; simpa [lastChild] using h0
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨tc, tr, hc, hr, rfl⟩ := absEntries_cons_inv hA
    simp only [lastChild]
    exact ih hc hr

/-- After the picked child changes its abstraction to `tc'` and the
children before it keep theirs, the branch abstracts to `replaceLast`. -/
theorem abs_replaceLast {d : Nat} {h h' : Heap K V} {c0 : NodeId} {t0 : Node K V}
    {A : List (K × NodeId)} {tsA : List (K × Node K V)} {tc' : Node K V}
    (h0 : absNode d h c0 = some t0) (hA : absNode.absEntries d h A = some tsA)
    (hfront : ∀ c ∈ frontIds c0 A, absNode d h' c = absNode d h c)
    (hlast : absNode d h' (lastChild c0 A) = some tc') :
    absNode d h' c0 = some (replaceLast t0 tsA tc').1 ∧
      absNode.absEntries d h' A = some (replaceLast t0 tsA tc').2 := by
  induction A generalizing c0 t0 tsA with
  | nil =>
    simp only [absNode.absEntries, Option.some.injEq] at hA
    subst hA
    simp only [lastChild] at hlast
    exact ⟨hlast, by simp [replaceLast, absNode.absEntries]⟩
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨tc, tr, hc, hr, rfl⟩ := absEntries_cons_inv hA
    simp only [frontIds, List.mem_cons, forall_eq_or_imp] at hfront
    simp only [lastChild] at hlast
    obtain ⟨ih1, ih2⟩ := ih hc hr hfront.2 hlast
    simp only [replaceLast]
    refine ⟨by rw [hfront.1]; exact h0, ?_⟩
    exact absEntries_cons ih1 ih2

theorem absEntries_take {d : Nat} {h : Heap K V} {es : List (K × NodeId)}
    {ts : List (K × Node K V)} (he : absNode.absEntries d h es = some ts) (i : Nat) :
    absNode.absEntries d h (es.take i) = some (ts.take i) ∧
      absNode.absEntries d h (es.drop i) = some (ts.drop i) := by
  induction es generalizing ts i with
  | nil =>
    simp only [absNode.absEntries, Option.some.injEq] at he
    subst he; simp [absNode.absEntries]
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨tc, tr, hc, hr, rfl⟩ := absEntries_cons_inv he
    cases i with
    | zero => exact ⟨by simp [absNode.absEntries], absEntries_cons hc hr⟩
    | succ i =>
      obtain ⟨ih1, ih2⟩ := ih hr i
      simp only [List.take_succ_cons, List.drop_succ_cons]
      exact ⟨absEntries_cons hc ih1, ih2⟩

theorem absEntries_insertAt {d : Nat} {h : Heap K V} {es : List (K × NodeId)}
    {ts : List (K × Node K V)} (he : absNode.absEntries d h es = some ts) (i : Nat) (s : K)
    {c : NodeId} {tc : Node K V} (hc : absNode d h c = some tc) :
    absNode.absEntries d h (insertAt es i (s, c)) = some (insertAt ts i (s, tc)) := by
  obtain ⟨h1, h2⟩ := absEntries_take he i
  simp only [insertAt]
  rw [absEntries_append, h1]
  simp only [Option.bind_some]
  rw [absEntries_cons hc h2]
  simp

theorem absEntries_child_some {d : Nat} {h : Heap K V} {es : List (K × NodeId)}
    {ts : List (K × Node K V)} (he : absNode.absEntries d h es = some ts) :
    ∀ e ∈ es, ∃ t, absNode d h e.2 = some t := by
  induction es generalizing ts with
  | nil => intro e he'; cases he'
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨tc, tr, hc, hr, rfl⟩ := absEntries_cons_inv he
    intro e' he'
    rcases List.mem_cons.mp he' with rfl | he'
    · exact ⟨tc, hc⟩
    · exact ih hr e' he'

/-- The abstraction of entries as a map: every child abstracts, and the
entries are the map of that function. -/
def absF (d : Nat) (h : Heap K V) (c : NodeId) : Node K V := (absNode d h c).getD (.leaf [])

theorem absEntries_eq_map {d : Nat} {h : Heap K V} {es : List (K × NodeId)}
    {ts : List (K × Node K V)} (he : absNode.absEntries d h es = some ts) :
    ts = es.map fun e => (e.1, absF d h e.2) := by
  induction es generalizing ts with
  | nil => simp only [absNode.absEntries, Option.some.injEq] at he; subst he; rfl
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨tc, tr, hc, hr, rfl⟩ := absEntries_cons_inv he
    simp [ih hr, absF, hc]

theorem absF_of_some {d : Nat} {h : Heap K V} {c : NodeId} {t : Node K V}
    (hc : absNode d h c = some t) : absF d h c = t := by simp [absF, hc]

theorem absEntries_of_all_some {d : Nat} {h : Heap K V} {es : List (K × NodeId)}
    (hall : ∀ e ∈ es, ∃ t, absNode d h e.2 = some t) :
    absNode.absEntries d h es = some (es.map fun e => (e.1, absF d h e.2)) := by
  induction es with
  | nil => simp [absNode.absEntries]
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    obtain ⟨t, ht⟩ := hall (s, c) List.mem_cons_self
    rw [List.map_cons]
    exact absEntries_cons (by rw [ht, absF_of_some ht]) (ih fun e he => hall e (List.mem_cons_of_mem _ he))

/-! ### `branchApplySplit` under a map on children -/

/-- Map the children of a branch. -/
def Branch.mapC {C C' : Type} (f : C → C') (b : Branch K C) : Branch K C' :=
  ⟨f b.c0, b.entries.map fun e => (e.1, f e.2)⟩

def BranchInsert.mapC {C C' : Type} (f : C → C') : BranchInsert K C → BranchInsert K C'
  | .noSplit b => .noSplit (b.mapC f)
  | .split l pk r => .split (l.mapC f) pk (r.mapC f)

theorem insertAt_map {α β : Type} (g : α → β) (l : List α) (i : Nat) (x : α) :
    (insertAt l i x).map g = insertAt (l.map g) i (g x) := by
  simp [insertAt, List.map_take, List.map_drop]

theorem cutInsert_map {α β : Type} (g : α → β) (l : List α) (i : Nat) (x : α) :
    cutInsert (l.map g) i (g x) = ((cutInsert l i x).1.map g, (cutInsert l i x).2.map g) := by
  simp only [cutInsert, List.length_map]
  split <;> simp [List.map_take, List.map_drop, insertAt_map]

theorem branchApplySplit_mapC {C C' : Type} (f : C → C') (cap : Nat) (b : Branch K C)
    (idx : Nat) (sep : K) (right : C) :
    branchApplySplit cap (b.mapC f) idx sep (f right) =
      (branchApplySplit cap b idx sep right).mapC f := by
  simp only [branchApplySplit, Branch.mapC, List.length_map]
  split
  · simp only [BranchInsert.mapC, Branch.mapC]
    congr 1
    have := insertAt_map (fun e : K × C => (e.1, f e.2)) b.entries idx (sep, right)
    simpa using this.symm
  · simp only [branchInsertAndSplit]
    have hc := cutInsert_map (fun e : K × C => (e.1, f e.2)) b.entries idx (sep, right)
    simp only at hc
    rw [hc]
    rcases (cutInsert b.entries idx (sep, right)) with ⟨l, r⟩
    cases r with
    | nil => simp [BranchInsert.mapC, Branch.mapC]
    | cons e rest => obtain ⟨pk, pc⟩ := e; simp [BranchInsert.mapC, Branch.mapC]

/-- A full branch splits into two halves whose entries, with the promoted
entry between them, are the inserted entries. -/
theorem branchInsertAndSplit_concat {C : Type} (b : Branch K C) (idx : Nat) (sep : K) (right : C)
    (hidx : idx ≤ b.entries.length) (hlen : 1 ≤ b.entries.length) :
    (branchInsertAndSplit b idx sep right).1.c0 = b.c0 ∧
      (branchInsertAndSplit b idx sep right).1.entries ++
        ((branchInsertAndSplit b idx sep right).2.1,
          (branchInsertAndSplit b idx sep right).2.2.c0) ::
          (branchInsertAndSplit b idx sep right).2.2.entries =
        insertAt b.entries idx (sep, right) := by
  simp only [branchInsertAndSplit]
  rw [cutInsert_eq _ _ _ hidx]
  have hlt : (b.entries.length + 1) / 2 < (insertAt b.entries idx (sep, right)).length := by
    simp [insertAt]; omega
  rcases hd : (insertAt b.entries idx (sep, right)).drop ((b.entries.length + 1) / 2) with _ | ⟨e, rest⟩
  · have := congrArg List.length hd
    simp at this; omega
  · obtain ⟨pk, pc⟩ := e
    simp only
    refine ⟨by first | trivial | rfl, ?_⟩
    rw [← hd, List.take_append_drop]

/-! ### Reassembling the chain around a replaced run of leaves -/

/-- If a run `lvC` in the middle of a chain is replaced by `lvC'` (same first
leaf, chained between the same neighbours), the leaves before it keep their
records, and the leaf after it only has its `prev` moved to the new last
leaf, the whole is chained again. -/
theorem linked_reassemble {h h' : Heap K V} {prev0 next0 : Option NodeId}
    {lvF lvC lvC' lvB : List NodeId}
    (hl : Linked h prev0 (lvF ++ lvC ++ lvB) next0)
    (hC' : Linked h' (lvF.getLast?.or prev0) lvC' (lvB.head?.or next0))
    (hhead : lvC'.head? = lvC.head?)
    (hF : ∀ i ∈ lvF, h'.get i = h.get i)
    (hBhead : ∀ a rest, lvB = a :: rest → ∀ O p n, h.get a = some (.leaf O p n) →
      h'.get a = some (.leaf O (lvC'.getLast?.or (lvF.getLast?.or prev0)) n))
    (hBrest : ∀ a rest, lvB = a :: rest → ∀ i ∈ rest, h'.get i = h.get i) :
    Linked h' prev0 (lvF ++ lvC' ++ lvB) next0 := by
  rw [linked_append, linked_append] at hl
  obtain ⟨⟨hlF, hlC⟩, hlB⟩ := hl
  rw [linked_append, linked_append]
  have hlastC : (lvF ++ lvC').getLast?.or prev0 = lvC'.getLast?.or (lvF.getLast?.or prev0) := by
    rw [List.getLast?_append, Option.or_assoc]
  refine ⟨⟨?_, hC'⟩, ?_⟩
  · rw [hhead]; exact linked_congr hF hlF
  · rw [hlastC]
    cases lvB with
    | nil => trivial
    | cons a rest =>
      obtain ⟨⟨O, hga⟩, hrest⟩ := hlB
      refine ⟨⟨O, hBhead a rest rfl O _ _ hga⟩, ?_⟩
      exact linked_congr (fun i hi => hBrest a rest rfl i hi) hrest

/-! ## The insert simulation -/

/-- The bookkeeping for the subtree at `id`: what it denotes, its ids in
preorder, its leaves left to right. -/
structure Sub (h : Heap K V) (d : Nat) (id : NodeId) (t : Node K V) (ids lv : List NodeId) :
    Prop where
  abs : absNode d h id = some t
  reach : reachIds d h id = some ids
  leaves : leafIds d h id = some lv

/-- Old ids are kept, and the new ids are exactly those allocated meanwhile. -/
def IdsGrow (h h' : Heap K V) (ids ids' : List NodeId) : Prop :=
  (∀ i ∈ ids, i ∈ ids') ∧ (∀ i ∈ ids', i ∈ ids ∨ (h.fresh ≤ i ∧ i < h'.fresh)) ∧
    (∀ i, h.fresh ≤ i → i < h'.fresh → i ∈ ids')

/-- The subtree's successor leaf, if any: outside the subtree, an
allocated leaf whose `prev` is the subtree's last leaf. -/
def NextOK (h : Heap K V) (ids lv : List NodeId) (prev0 next0 : Option NodeId) : Prop :=
  ∀ o, next0 = some o → o ∉ ids ∧ ∃ O n, h.get o = some (.leaf O (lv.getLast?.or prev0) n)

/-- The frame of an insert below a subtree: every pre-existing node outside
it keeps its record, except the successor leaf, whose `prev` now follows
the subtree's new last leaf. -/
def Frame (h h' : Heap K V) (ids : List NodeId) (next0 lastNew : Option NodeId) : Prop :=
  (∀ i, i ∉ ids → next0 ≠ some i → i < h.fresh → h'.get i = h.get i) ∧
  (∀ o O p n, next0 = some o → h.get o = some (.leaf O p n) →
    h'.get o = some (.leaf O lastNew n))

/-- What the simulation concludes for one subtree, by outcome. -/
def InsertPost (lc bc : Nat) (k : K) (v : V) (d : Nat) (h h' : Heap K V) (id : NodeId)
    (t : Node K V) (ids lv : List NodeId) (prev0 next0 : Option NodeId) :
    InsertResH K V → Prop
  | .noSplit old =>
    match insertRec lc bc k v t with
    | .noSplit t' old' => old = old' ∧ ∃ ids' lv',
        Sub h' (d + 1) id t' ids' lv' ∧ ids'.Nodup ∧ IdsGrow h h' ids ids' ∧
        lv'.head? = lv.head? ∧ Linked h' prev0 lv' next0 ∧
        Frame h h' ids next0 (lv'.getLast?.or prev0)
    | .split _ _ _ => False
  | .split sep rid old =>
    match insertRec lc bc k v t with
    | .noSplit _ _ => False
    | .split l sep' r => sep = sep' ∧ old = none ∧ ∃ idsL lvL idsR lvR,
        Sub h' (d + 1) id l idsL lvL ∧ Sub h' (d + 1) rid r idsR lvR ∧
        (idsL ++ idsR).Nodup ∧ IdsGrow h h' ids (idsL ++ idsR) ∧ lvL.head? = lv.head? ∧
        Linked h' prev0 (lvL ++ lvR) next0 ∧
        Frame h h' ids next0 ((lvL ++ lvR).getLast?.or prev0)

/-! ### Inverting `Sub` -/

theorem sub_leaf_inv {h : Heap K V} {d : Nat} {id : NodeId} {kvs : Leaf K V}
    {p n : Option NodeId} {t : Node K V} {ids lv : List NodeId}
    (hg : h.get id = some (.leaf kvs p n)) (hs : Sub h (d + 1) id t ids lv) :
    t = .leaf kvs ∧ ids = [id] ∧ lv = [id] := by
  obtain ⟨ha, hr, hl⟩ := hs
  rw [absNode_leaf hg] at ha; rw [reachIds_leaf hg] at hr; rw [leafIds_leaf hg] at hl
  cases ha; cases hr; cases hl
  exact ⟨rfl, rfl, rfl⟩

theorem sub_branch_inv {h : Heap K V} {d : Nat} {id : NodeId} {c0 : NodeId}
    {es : List (K × NodeId)} {t : Node K V} {ids lv : List NodeId}
    (hg : h.get id = some (.branch c0 es)) (hs : Sub h (d + 1) id t ids lv) :
    ∃ t0 ts below, absNode d h c0 = some t0 ∧ absNode.absEntries d h es = some ts ∧
      t = .branch t0 ts ∧ reachIds.reachChildren d h (c0 :: es.map (·.2)) = some below ∧
      ids = id :: below ∧ leafIds.leafChildren d h (c0 :: es.map (·.2)) = some lv := by
  obtain ⟨ha, hr, hl⟩ := hs
  rw [absNode_branch hg] at ha; rw [reachIds_branch hg] at hr; rw [leafIds_branch hg] at hl
  cases h0 : absNode d h c0 <;> rw [h0] at ha
  · cases ha
  · rename_i t0
    cases he : absNode.absEntries d h es <;> rw [he] at ha
    · cases ha
    · rename_i ts
      simp only [Option.bind_some, Option.some.injEq] at ha
      cases hb : reachIds.reachChildren d h (c0 :: es.map (·.2)) <;> rw [hb] at hr
      · cases hr
      · rename_i below
        simp only [Option.map_some, Option.some.injEq] at hr
        exact ⟨t0, ts, below, rfl, rfl, ha.symm, rfl, hr.symm, hl⟩

theorem sub_branch_zero {h : Heap K V} {id c0 : NodeId} {es : List (K × NodeId)} {t : Node K V}
    {ids lv : List NodeId} (hg : h.get id = some (.branch c0 es)) (hs : Sub h 1 id t ids lv) :
    False := by
  have := hs.abs
  rw [absNode_branch hg] at this
  simp [absNode] at this

/-! ### List helpers -/

theorem nodup_append_iff {α : Type} (l1 l2 : List α) :
    (l1 ++ l2).Nodup ↔ l1.Nodup ∧ l2.Nodup ∧ ∀ a ∈ l1, ∀ b ∈ l2, a ≠ b := by
  simp [List.Nodup, List.pairwise_append]

theorem reachChildren_cons (d : Nat) (h : Heap K V) (c : NodeId) (rest : List NodeId) :
    reachIds.reachChildren d h (c :: rest) =
      (reachIds d h c).bind fun l => (reachIds.reachChildren d h rest).bind fun r => some (l ++ r) := by
  simp only [reachIds.reachChildren]
  cases reachIds d h c <;> simp [Option.bind_eq_bind]

theorem leafChildren_cons (d : Nat) (h : Heap K V) (c : NodeId) (rest : List NodeId) :
    leafIds.leafChildren d h (c :: rest) =
      (leafIds d h c).bind fun l => (leafIds.leafChildren d h rest).bind fun r => some (l ++ r) := by
  simp only [leafIds.leafChildren]
  cases leafIds d h c <;> simp [Option.bind_eq_bind]

theorem head?_append_of_ne_nil {α : Type} {l1 : List α} (l2 : List α) (h : l1 ≠ []) :
    (l1 ++ l2).head? = l1.head? := by
  cases l1 with
  | nil => exact absurd rfl h
  | cons a t => rfl

theorem getLast?_append_of_ne_nil {α : Type} (l1 : List α) {l2 : List α} (h : l2 ≠ []) :
    (l1 ++ l2).getLast? = l2.getLast? := by
  rw [List.getLast?_append]
  cases hl : l2.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hl; exact absurd hl h
  | some a => rfl

theorem getLast?_append_cons {α : Type} (l1 l2 : List α) (a : α) (rest : List α) :
    (l1 ++ (l2 ++ a :: rest)).getLast? = (a :: rest).getLast? := by
  rw [getLast?_append_of_ne_nil _ (by simp), getLast?_append_of_ne_nil _ (by simp)]

/-! ### The leaf case -/

theorem insertLeaf_sim (lc bc : Nat) (k : K) (v : V) (d fuel : Nat) (h : Heap K V) (id : NodeId)
    (kvs : Leaf K V) (prev0 next0 : Option NodeId)
    (hg : h.get id = some (.leaf kvs prev0 next0)) (hb : Heap.Bounded h)
    (hnext : NextOK h [id] [id] prev0 next0) :
    ∃ res h', insertRecH lc bc k v (fuel + 1) h id = some (res, h') ∧ Heap.Bounded h' ∧
      h.fresh ≤ h'.fresh ∧ InsertPost lc bc k v d h h' id (.leaf kvs) [id] [id] prev0 next0 res := by
  have hid : id < h.fresh := hb id (by simp [hg])
  rcases hli : leafInsertOrSplit lc kvs k v with ⟨l, old⟩ | ⟨l, r, sep⟩
  · -- The leaf absorbs the entry: one write.
    have htree : insertRec lc bc k v (.leaf kvs) = .noSplit (.leaf l) old := by
      rw [insertRec, hli]
    obtain ⟨h', hw⟩ := Heap.write_some (h := h) (id := id) (r := .leaf l prev0 next0) (by simp [hg])
    have hg' := Heap.get_write_self hw
    refine ⟨.noSplit old, h', ?_, Heap.bounded_write hw hb,
      le_of_eq (Heap.fresh_write hw).symm, ?_⟩
    · simp [insertRecH, hg, hli, hw]
    · simp only [InsertPost, htree]
      refine ⟨by trivial, [id], [id], ⟨absNode_leaf hg' d, reachIds_leaf hg' d, leafIds_leaf hg' d⟩,
        by simp, ?_, rfl, linked_singleton.mpr ⟨l, hg'⟩, ?_⟩
      · refine ⟨fun i hi => hi, fun i hi => Or.inl hi, fun i h1 h2 => ?_⟩
        rw [Heap.fresh_write hw] at h2; omega_id
      · refine ⟨fun i hi _ _ => Heap.get_write_other hw (fun heq => hi (by simp [heq])), ?_⟩
        intro o O p n ho hgo
        obtain ⟨hno, O', n', hgo'⟩ := hnext o ho
        have hne : o ≠ id := fun heq => hno (by simp [heq])
        rw [Heap.get_write_other hw hne, hgo]
        rw [hgo] at hgo'
        cases hgo'
        rfl
  · -- The leaf splits: allocate the right sibling, write the left, link.
    have htree : insertRec lc bc k v (.leaf kvs) = .split (.leaf l) sep (.leaf r) := by
      rw [insertRec, hli]
    have hne : id ≠ h.fresh := by omega_id
    have hg1 : (h.alloc (.leaf r none none)).2.get id = some (.leaf kvs prev0 next0) := by
      rw [Heap.get_alloc_other h _ hne]; exact hg
    have hr1 : (h.alloc (.leaf r none none)).2.get h.fresh = some (.leaf r none none) :=
      Heap.get_alloc_self h _
    obtain ⟨h2, hw⟩ := Heap.write_some (h := (h.alloc (.leaf r none none)).2) (id := id)
      (r := .leaf l prev0 next0) (by simp [hg1])
    have hg2 := Heap.get_write_self hw
    have hr2 : h2.get h.fresh = some (.leaf r none none) := by
      rw [Heap.get_write_other hw (Ne.symm hne)]; exact hr1
    have hf2 : h2.fresh = h.fresh + 1 := by rw [Heap.fresh_write hw, Heap.fresh_alloc]
    have hold : ∀ o, next0 = some o → o ≠ id ∧ o ≠ h.fresh ∧
        ∃ O po no, h2.get o = some (.leaf O po no) := by
      intro o ho
      obtain ⟨hno, O, n, hgo⟩ := hnext o ho
      have hoid : o ≠ id := fun heq => hno (by simp [heq])
      have hofresh : o < h.fresh := hb o (by simp [hgo])
      refine ⟨hoid, by omega_id, O, [id].getLast?.or prev0, n, ?_⟩
      rw [Heap.get_write_other hw hoid, Heap.get_alloc_other h _ (by omega_id)]
      exact hgo
    obtain ⟨h3, hlink, hg3, hr3, ho3, hother3, hf3⟩ :=
      linkLeafAfter_spec hg2 hr2 (Ne.symm hne) hold
    have hb3 : Heap.Bounded h3 := by
      intro i hi
      rw [hf3, hf2]
      by_cases hiid : i = id
      · subst hiid; omega_id
      by_cases hir : i = h.fresh
      · subst hir; exact Nat.lt_succ_self _
      by_cases hio : next0 = some i
      · obtain ⟨hno, O, n, hgo⟩ := hnext i hio
        exact Nat.lt_succ_of_lt (hb i (by simp [hgo]))
      · rw [hother3 i hiid hir hio, Heap.get_write_other hw hiid,
          Heap.get_alloc_other h _ hir] at hi
        exact Nat.lt_succ_of_lt (hb i hi)
    refine ⟨.split sep h.fresh none, h3, ?_, hb3, by rw [hf3, hf2]; exact Nat.le_succ _, ?_⟩
    · simp only [insertRecH, hg, hli]
      rw [show h.alloc (.leaf r none none) = (h.fresh, (h.alloc (.leaf r none none)).2) from rfl]
      simp only [hw, Option.bind_eq_bind, Option.bind_some, hlink]
    · simp only [InsertPost, htree]
      refine ⟨by trivial, by trivial, [id], [id], [h.fresh], [h.fresh],
        ⟨absNode_leaf hg3 d, reachIds_leaf hg3 d, leafIds_leaf hg3 d⟩,
        ⟨absNode_leaf hr3 d, reachIds_leaf hr3 d, leafIds_leaf hr3 d⟩, ?_, ?_, rfl, ?_, ?_⟩
      · simp [hne]
      · refine ⟨fun i hi => by simp at hi; simp [hi], fun i hi => ?_, fun i h1 h2 => ?_⟩
        · simp at hi
          rcases hi with rfl | rfl
          · exact Or.inl (by simp)
          · right; rw [hf3, hf2]; omega_id
        · rw [hf3, hf2] at h2
          have : i = h.fresh := by omega_id
          simp [this]
      · exact ⟨⟨l, by simpa using hg3⟩, ⟨r, by simpa using hr3⟩, trivial⟩
      · refine ⟨fun i hi hio hlt => ?_, fun o O p n ho hgo => ?_⟩
        · have hiid : i ≠ id := fun heq => hi (by simp [heq])
          have hir : i ≠ h.fresh := by omega_id
          rw [hother3 i hiid hir hio, Heap.get_write_other hw hiid, Heap.get_alloc_other h _ hir]
        · obtain ⟨hno, O', n', hgo'⟩ := hnext o ho
          have hoid : o ≠ id := fun heq => hno (by simp [heq])
          have hofresh : o < h.fresh := hb o (by simp [hgo])
          have hgo2 : h2.get o = some (.leaf O p n) := by
            rw [Heap.get_write_other hw hoid, Heap.get_alloc_other h _ (by omega_id)]
            exact hgo
          rw [ho3 o O p n ho hgo2]
          rfl

/-! ### The branch case -/

/-- What the child's simulation leaves for the parent to reassemble: the
records of the front children, of the back children, and of the branch
itself, up to the successor leaf's `prev`. -/
theorem frame_consequences {h h' : Heap K V} {Lc lvB Lother : List NodeId}
    {nextC next0 prevB : Option NodeId} {lastNew : Option NodeId}
    (hfr : Frame h h' Lc nextC lastNew) (hnextC : nextC = lvB.head?.or next0)
    (hbounded : Heap.Bounded h) (hlB : Linked h prevB lvB next0)
    (hdisj : ∀ i ∈ Lother, i ∉ Lc) (halloc : ∀ i ∈ Lother, (h.get i).isSome)
    (hnext0 : ∀ o, next0 = some o → o ∉ Lother) :
    (∀ i ∈ Lother, SameContent (h.get i) (h'.get i)) ∧
    (∀ i ∈ Lother, lvB.head? ≠ some i → h'.get i = h.get i) := by
  have hlt : ∀ i ∈ Lother, i < h.fresh := fun i hi => hbounded i (halloc i hi)
  rcases lvB with _ | ⟨a, rest⟩
  · simp only [List.head?_nil, Option.none_or] at hnextC
    subst hnextC
    refine ⟨fun i hi => ?_, fun i hi _ => ?_⟩
    · exact sameContent_of_eq (hfr.1 i (hdisj i hi) (fun ho => hnext0 i ho hi) (hlt i hi))
    · exact hfr.1 i (hdisj i hi) (fun ho => hnext0 i ho hi) (hlt i hi)
  · simp only [List.head?_cons, Option.some_or] at hnextC
    subst hnextC
    obtain ⟨⟨O, hga⟩, _⟩ := hlB
    refine ⟨fun i hi => ?_, fun i hi hne => ?_⟩
    · by_cases hia : i = a
      · subst hia
        rw [hga, hfr.2 i O _ _ rfl hga]
        exact sameContent_leaf
      · exact sameContent_of_eq (hfr.1 i (hdisj i hi) (fun heq => hia (by simpa using heq.symm))
          (hlt i hi))
    · exact hfr.1 i (hdisj i hi) (fun heq => hne (by simpa using heq)) (hlt i hi)

theorem insertAt_children (c0 : NodeId) (A B : List (K × NodeId)) (s : K) (c : NodeId) :
    c0 :: (insertAt (A ++ B) A.length (s, c)).map (·.2) =
      frontIds c0 A ++ lastChild c0 A :: c :: B.map (·.2) := by
  rw [insertAt_map, List.map_append, ← List.length_map (f := fun e : K × NodeId => e.2),
    insertAt_append, ← List.cons_append, cons_map_eq_front_last, List.append_assoc,
    List.singleton_append]

theorem cons_map_split (c0 : NodeId) (A B : List (K × NodeId)) :
    c0 :: (A ++ B).map (·.2) = frontIds c0 A ++ lastChild c0 A :: B.map (·.2) := by
  rw [List.map_append, ← List.cons_append, cons_map_eq_front_last, List.append_assoc,
    List.singleton_append]

theorem insertRecH_sim (lc bc : Nat) (hbc : 1 ≤ bc) (k : K) (v : V) :
    ∀ (d fuel : Nat) (h : Heap K V) (id : NodeId) (t : Node K V) (ids lv : List NodeId)
      (prev0 next0 : Option NodeId),
      d < fuel → Sub h (d + 1) id t ids lv → ids.Nodup → Heap.Bounded h →
      Linked h prev0 lv next0 → NextOK h ids lv prev0 next0 →
      ∃ res h', insertRecH lc bc k v fuel h id = some (res, h') ∧ Heap.Bounded h' ∧
        h.fresh ≤ h'.fresh ∧ InsertPost lc bc k v d h h' id t ids lv prev0 next0 res := by
  have leafCase : ∀ (d f : Nat) (h : Heap K V) (id : NodeId) (t : Node K V) (ids lv : List NodeId)
      (prev0 next0 : Option NodeId) (kvs : Leaf K V) (p n : Option NodeId),
      h.get id = some (.leaf kvs p n) → Sub h (d + 1) id t ids lv → Heap.Bounded h →
      Linked h prev0 lv next0 → NextOK h ids lv prev0 next0 →
      ∃ res h', insertRecH lc bc k v (f + 1) h id = some (res, h') ∧ Heap.Bounded h' ∧
        h.fresh ≤ h'.fresh ∧ InsertPost lc bc k v d h h' id t ids lv prev0 next0 res := by
    intro d f h id t ids lv prev0 next0 kvs p n hg hsub hb hl hnext
    obtain ⟨rfl, rfl, rfl⟩ := sub_leaf_inv hg hsub
    obtain ⟨kvs', hg'⟩ := linked_singleton.mp hl
    rw [hg] at hg'
    simp only [Option.some.injEq, NodeRec.leaf.injEq] at hg'
    obtain ⟨rfl, rfl, rfl⟩ := hg'
    exact insertLeaf_sim lc bc k v d f h id kvs p n hg hb hnext
  intro d
  induction d with
  | zero =>
    intro fuel h id t ids lv prev0 next0 hfuel hsub hnd hb hl hnext
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
    · exfalso; have := hsub.reach; simp [reachIds, hg] at this
    · exact leafCase 0 f h id t ids lv prev0 next0 kvs p n hg hsub hb hl hnext
    · exact (sub_branch_zero hg hsub).elim
  | succ d ih =>
    intro fuel h id t ids lv prev0 next0 hfuel hsub hnd hb hl hnext
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rcases hg : h.get id with _ | (⟨kvs, p, n⟩ | ⟨c0, es⟩)
    · exfalso; have := hsub.reach; simp [reachIds, hg] at this
    · exact leafCase (d + 1) f h id t ids lv prev0 next0 kvs p n hg hsub hb hl hnext
    -- The branch case.
    obtain ⟨t0, ts, below, h0, hes, rfl, hbelow, rfl, hlvb⟩ := sub_branch_inv hg hsub
    have hid : id < h.fresh := hb id (by simp [hg])
    have hesAB := takeWhile_append_dropWhile_entries k es
    obtain ⟨htsA, htsB⟩ := absEntries_takeWhile k hes
    have htsAB : ts = ts.takeWhile (sepLE k) ++ ts.dropWhile (sepLE k) :=
      List.takeWhile_append_dropWhile.symm
    have hcs : c0 :: es.map (·.2) =
        frontIds c0 (es.takeWhile (sepLE k)) ++
          lastChild c0 (es.takeWhile (sepLE k)) :: (es.dropWhile (sepLE k)).map (·.2) := by
      have := cons_map_split c0 (es.takeWhile (sepLE k)) (es.dropWhile (sepLE k))
      rwa [← hesAB] at this
    -- Decompose the reach and leaf lists around the picked child.
    rw [hcs, reachChildren_append, reachChildren_cons] at hbelow
    rw [hcs, leafChildren_append, leafChildren_cons] at hlvb
    rcases hLf : reachIds.reachChildren (d + 1) h (frontIds c0 (es.takeWhile (sepLE k)))
      with _ | Lf
    · rw [hLf] at hbelow; cases hbelow
    rcases hLc : reachIds (d + 1) h (lastChild c0 (es.takeWhile (sepLE k))) with _ | Lc
    · rw [hLf, hLc] at hbelow; cases hbelow
    rcases hLb : reachIds.reachChildren (d + 1) h ((es.dropWhile (sepLE k)).map (·.2)) with _ | Lb
    · rw [hLf, hLc, hLb] at hbelow; cases hbelow
    rw [hLf, hLc, hLb] at hbelow
    simp only [Option.bind_some, Option.some.injEq] at hbelow
    subst hbelow
    rcases hlvF : leafIds.leafChildren (d + 1) h (frontIds c0 (es.takeWhile (sepLE k)))
      with _ | lvF
    · rw [hlvF] at hlvb; cases hlvb
    rcases hlvC : leafIds (d + 1) h (lastChild c0 (es.takeWhile (sepLE k))) with _ | lvC
    · rw [hlvF, hlvC] at hlvb; cases hlvb
    rcases hlvB : leafIds.leafChildren (d + 1) h ((es.dropWhile (sepLE k)).map (·.2)) with _ | lvB
    · rw [hlvF, hlvC, hlvB] at hlvb; cases hlvb
    rw [hlvF, hlvC, hlvB] at hlvb
    simp only [Option.bind_some, Option.some.injEq] at hlvb
    subst hlvb
    -- Bookkeeping facts about the pieces.
    have hnd' := List.nodup_cons.mp hnd
    obtain ⟨hidnb, hndb⟩ := hnd'
    obtain ⟨hLfNd, hrest⟩ := (nodup_append_iff _ _).mp hndb
    obtain ⟨hLcLbNd, hFdisj⟩ := hrest
    obtain ⟨hLcNd, hLbNd, hCBdisj⟩ := (nodup_append_iff _ _).mp hLcLbNd
    have halloc : ∀ i ∈ id :: (Lf ++ (Lc ++ Lb)), (h.get i).isSome :=
      mem_reachIds_allocated (d + 2) h id _ hsub.reach
    obtain ⟨_, hlvFsub⟩ := (leaf_facts (d + 1)).2 h _ Lf lvF hLf hlvF
    obtain ⟨hlvCne, hlvCsub⟩ := (leaf_facts (d + 1)).1 h _ Lc lvC hLc hlvC
    obtain ⟨_, hlvBsub⟩ := (leaf_facts (d + 1)).2 h _ Lb lvB hLb hlvB
    have hlvFmem : ∀ i ∈ lvF, i ∈ Lf := fun i hi => hlvFsub.subset hi
    have hlvCmem : ∀ i ∈ lvC, i ∈ Lc := fun i hi => hlvCsub.subset hi
    have hlvBmem : ∀ i ∈ lvB, i ∈ Lb := fun i hi => hlvBsub.subset hi
    have hlvBNd : lvB.Nodup := hLbNd.sublist hlvBsub
    -- The child's own bookkeeping.
    have hsubC : Sub h (d + 1) (lastChild c0 (es.takeWhile (sepLE k)))
        (lastChild t0 (ts.takeWhile (sepLE k))) Lc lvC :=
      ⟨absNode_lastChild h0 htsA, hLc, hlvC⟩
    have hl' := hl
    rw [linked_append] at hl'
    obtain ⟨hlF, hlCB⟩ := hl'
    rw [linked_append] at hlCB
    obtain ⟨hlC, hlB⟩ := hlCB
    have hnextC : NextOK h Lc lvC (lvF.getLast?.or prev0) (lvB.head?.or next0) := by
      intro o ho
      cases lvB with
      | nil =>
        simp only [List.head?_nil, Option.none_or] at ho
        obtain ⟨hno, O, n, hgo⟩ := hnext o ho
        refine ⟨fun hin => hno (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_append_left _ hin))), O, n, ?_⟩
        rw [hgo]
        congr 2
        first
          | rfl
          | rw [List.append_nil, List.getLast?_append, Option.or_assoc]
          | simp [List.getLast?_append, Option.or_assoc]
      | cons a rest =>
        simp only [List.head?_cons, Option.some_or, Option.some.injEq] at ho
        subst ho
        obtain ⟨⟨O, hga⟩, _⟩ := hlB
        refine ⟨fun hin => hCBdisj a hin a (hlvBmem a List.mem_cons_self) rfl, O, _, hga⟩
    obtain ⟨resC, h', hrec, hb', hfr', hpostC⟩ :=
      ih f h _ _ Lc lvC (lvF.getLast?.or prev0) (lvB.head?.or next0) (by omega) hsubC hLcNd hb hlC
        hnextC
    -- Facts shared by both outcomes of the child.
    have hidLc : id ∉ Lc := fun hin => hidnb (List.mem_append_right _ (List.mem_append_left _ hin))
    have hidLb : id ∉ Lb := fun hin => hidnb (List.mem_append_right _ (List.mem_append_right _ hin))
    have hidLf : id ∉ Lf := fun hin => hidnb (List.mem_append_left _ hin)
    have hFalloc : ∀ i ∈ Lf, (h.get i).isSome := fun i hi =>
      halloc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
    have hBalloc : ∀ i ∈ Lb, (h.get i).isSome := fun i hi =>
      halloc i (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ hi)))
    have hnext0F : ∀ o, next0 = some o → o ∉ Lf := fun o ho hin =>
      (hnext o ho).1 (List.mem_cons_of_mem _ (List.mem_append_left _ hin))
    have hnext0B : ∀ o, next0 = some o → o ∉ Lb := fun o ho hin =>
      (hnext o ho).1 (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ hin)))
    have hnext0id : ∀ o, next0 = some o → o ≠ id := fun o ho heq =>
      (hnext o ho).1 (by rw [heq]; exact List.mem_cons_self)
    have hnextCid : lvB.head?.or next0 ≠ some id := by
      cases hh : lvB.head? with
      | none => simp; intro ho; exact hnext0id id ho rfl
      | some a =>
        simp; intro heq; subst heq
        exact hidLb (hlvBmem _ (List.mem_of_mem_head? hh))
    have hlenA : (ts.takeWhile (sepLE k)).length = (es.takeWhile (sepLE k)).length :=
      absEntries_length htsA
    -- Name the four pieces of the entry lists.
    generalize hA : es.takeWhile (sepLE k) = A at *
    generalize hB : es.dropWhile (sepLE k) = B at *
    generalize hAt : ts.takeWhile (sepLE k) = tsA at *
    generalize hBt : ts.dropWhile (sepLE k) = tsB at *
    have hnotLc : ∀ i, i ∈ Lf ∨ i ∈ Lb → i ∉ Lc := by
      rintro i (hi | hi) hin
      · exact hFdisj i hi i (List.mem_append_left _ hin) rfl
      · exact hCBdisj i hin i hi rfl
    rcases resC with old | ⟨sep, rid, old⟩
    · -- The child absorbed the entry: this branch is untouched.
      simp only [InsertPost] at hpostC
      split at hpostC
      · rename_i tc' old' htc
        obtain ⟨hold, Lc', lvC', hsubC', hLc'Nd, hgrow, hheadC, hlC', hfrC⟩ := hpostC
        subst hold
        obtain ⟨hsameF, hunchF⟩ := frame_consequences hfrC rfl hb hlB
          (fun i hi => hnotLc i (Or.inl hi)) hFalloc hnext0F
        obtain ⟨hsameB, hunchB⟩ := frame_consequences hfrC rfl hb hlB
          (fun i hi => hnotLc i (Or.inr hi)) hBalloc hnext0B
        have hid' : h'.get id = some (.branch c0 es) := by
          rw [hfrC.1 id hidLc hnextCid hid]; exact hg
        obtain ⟨hLf', habsF, hlvF'⟩ := children_congr (d + 1) _ Lf hLf hsameF
        obtain ⟨hLb', habsB, hlvB'⟩ := children_congr (d + 1) _ Lb hLb hsameB
        rcases hrl : replaceLast t0 tsA tc' with ⟨t0', A'⟩
        obtain ⟨habs0, habsA⟩ := abs_replaceLast h0 htsA habsF hsubC'.abs
        rw [hrl] at habs0 habsA
        have habsB' : absNode.absEntries (d + 1) h' B = some tsB := by
          rw [absEntries_congr (fun e he => habsB e.2 (List.mem_map_of_mem he))]; exact htsB
        have hlvC'ne : lvC' ≠ [] := ((leaf_facts (d + 1)).1 h' _ Lc' lvC' hsubC'.reach hsubC'.leaves).1
        have hLc'sub : ∀ i ∈ Lc', i ∈ Lc ∨ (h.fresh ≤ i ∧ i < h'.fresh) := hgrow.2.1
        have hFlt : ∀ i ∈ Lf, i < h.fresh := fun i hi => hb i (hFalloc i hi)
        have hBlt : ∀ i ∈ Lb, i < h.fresh := fun i hi => hb i (hBalloc i hi)
        refine ⟨.noSplit old, h', ?_, hb', hfr', ?_⟩
        · rw [insertRecH]; simp only [hg, hA, hrec]
        simp only [InsertPost]
        rw [insertRec]
        simp only [hAt, hBt, htc, hrl]
        refine ⟨by trivial, id :: (Lf ++ (Lc' ++ Lb)), lvF ++ (lvC' ++ lvB), ⟨?_, ?_, ?_⟩, ?_, ?_, ?_,
          ?_, ?_⟩
        · -- abstraction
          rw [absNode_branch hid', habs0]
          simp only [Option.bind_some]
          rw [hesAB, absEntries_append, habsA]
          simp only [Option.bind_some]
          rw [habsB']
          rfl
        · -- reachable ids
          rw [reachIds_branch hid', hcs, reachChildren_append, reachChildren_cons, hLf',
            hsubC'.reach, hLb']
          rfl
        · -- leaves
          rw [leafIds_branch hid', hcs, leafChildren_append, leafChildren_cons, hlvF', hlvF,
            hsubC'.leaves, hlvB', hlvB]
          rfl
        · -- no id twice
          rw [List.nodup_cons, nodup_append_iff, nodup_append_iff]
          refine ⟨?_, hLfNd, ⟨hLc'Nd, hLbNd, ?_⟩, ?_⟩
          · intro hin
            rcases List.mem_append.mp hin with hin | hin
            · exact hidLf hin
            rcases List.mem_append.mp hin with hin | hin
            · rcases hLc'sub id hin with hin | ⟨hge, _⟩
              · exact hidLc hin
              · omega_id
            · exact hidLb hin
          · intro a ha b hb'
            rcases hLc'sub a ha with ha' | ⟨hge, _⟩
            · exact hCBdisj a ha' b hb'
            · have := hBlt b hb'; omega_id
          · intro a ha b hb'
            rcases List.mem_append.mp hb' with hb' | hb'
            · rcases hLc'sub b hb' with hb'' | ⟨hge, _⟩
              · exact hFdisj a ha b (List.mem_append_left _ hb'')
              · have := hFlt a ha; omega_id
            · exact hFdisj a ha b (List.mem_append_right _ hb')
        · -- ids grow
          refine ⟨fun i hi => ?_, fun i hi => ?_, fun i h1 h2 => ?_⟩
          · rcases List.mem_cons.mp hi with rfl | hi
            · exact List.mem_cons_self
            rcases List.mem_append.mp hi with hi | hi
            · exact List.mem_cons_of_mem _ (List.mem_append_left _ hi)
            rcases List.mem_append.mp hi with hi | hi
            · exact List.mem_cons_of_mem _ (List.mem_append_right _
                (List.mem_append_left _ (hgrow.1 i hi)))
            · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _ hi))
          · rcases List.mem_cons.mp hi with rfl | hi
            · exact Or.inl List.mem_cons_self
            rcases List.mem_append.mp hi with hi | hi
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
            rcases List.mem_append.mp hi with hi | hi
            · rcases hLc'sub i hi with hi' | hnew
              · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append_right _
                  (List.mem_append_left _ hi')))
              · exact Or.inr hnew
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append_right _
                (List.mem_append_right _ hi)))
          · exact List.mem_cons_of_mem _ (List.mem_append_right _
              (List.mem_append_left _ (hgrow.2.2 i h1 h2)))
        · -- the first leaf is unchanged
          cases lvF with
          | nil =>
            simp only [List.nil_append]
            rw [head?_append_of_ne_nil _ hlvC'ne, head?_append_of_ne_nil _ hlvCne, hheadC]
          | cons a t => rfl
        · -- the chain
          have := linked_reassemble (lvC' := lvC') (by rw [List.append_assoc]; exact hl) hlC'
            hheadC (fun i hi => hunchF i (hlvFmem i hi) ?_) ?_ ?_
          · rwa [List.append_assoc] at this
          · intro heq
            have ha := List.mem_of_mem_head? heq
            exact hFdisj i (hlvFmem i hi) i (List.mem_append_right _ (hlvBmem i ha)) rfl
          · intro a rest hlvBeq O p n hga
            exact hfrC.2 a O p n (by rw [hlvBeq]; rfl) hga
          · intro a rest hlvBeq i hi
            apply hunchB i (hlvBmem i (by rw [hlvBeq]; exact List.mem_cons_of_mem _ hi))
            rw [hlvBeq]
            intro heq
            simp at heq
            subst heq
            have := hlvBNd; rw [hlvBeq] at this
            exact (List.nodup_cons.mp this).1 hi
        · -- the frame
          refine ⟨fun i hi hio hlt => ?_, fun o O p n ho hgo => ?_⟩
          · apply hfrC.1 i (fun hin => hi (List.mem_cons_of_mem _ (List.mem_append_right _
              (List.mem_append_left _ hin)))) _ hlt
            cases hh : lvB.head? with
            | none => simpa using hio
            | some a =>
              simp
              intro heq; subst heq
              exact hi (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
                (hlvBmem _ (List.mem_of_mem_head? hh)))))
          · cases hlvBcase : lvB with
            | nil =>
              subst hlvBcase
              rw [hfrC.2 o O p n (by simpa using ho) hgo]
              try (congr 2)
              try simp only [List.append_nil, List.getLast?_append, Option.or_assoc]
            | cons a rest =>
              subst hlvBcase
              have hoa : o ≠ a := fun heq => hnext0B o ho (hlvBmem o (by rw [heq]; exact List.mem_cons_self))
              rw [hfrC.1 o (fun hin => (hnext o ho).1 (List.mem_cons_of_mem _
                (List.mem_append_right _ (List.mem_append_left _ hin))))
                (by simpa using (Ne.symm hoa)) (hb o (by simp [hgo])), hgo]
              obtain ⟨hno, O', n', hgo'⟩ := hnext o ho
              rw [hgo] at hgo'
              simp only [Option.some.injEq, NodeRec.leaf.injEq] at hgo'
              obtain ⟨_, hp, _⟩ := hgo'
              try rw [hp]
              try (congr 2)
              try rw [getLast?_append_cons, getLast?_append_cons]
      · exact hpostC.elim
    · -- The child split: this branch absorbs `(sep, rid)`, and may split too.
      simp only [InsertPost] at hpostC
      split at hpostC
      · exact hpostC.elim
      rename_i l sep' r htc
      obtain ⟨hsep, hold, LcL, lvL, LcR, lvR, hsubL, hsubR, hLRNd, hgrow, hheadL, hlLR, hfrC⟩ :=
        hpostC
      subst hsep; subst hold
      obtain ⟨hsameF, hunchF⟩ := frame_consequences hfrC rfl hb hlB
        (fun i hi => hnotLc i (Or.inl hi)) hFalloc hnext0F
      obtain ⟨hsameB, hunchB⟩ := frame_consequences hfrC rfl hb hlB
        (fun i hi => hnotLc i (Or.inr hi)) hBalloc hnext0B
      have hid' : h'.get id = some (.branch c0 es) := by
        rw [hfrC.1 id hidLc hnextCid hid]; exact hg
      obtain ⟨hLf', habsF, hlvF'⟩ := children_congr (d + 1) _ Lf hLf hsameF
      obtain ⟨hLb', habsB, hlvB'⟩ := children_congr (d + 1) _ Lb hLb hsameB
      rcases hrl : replaceLast t0 tsA l with ⟨t0', A'⟩
      obtain ⟨habs0, habsA⟩ := abs_replaceLast h0 htsA habsF hsubL.abs
      rw [hrl] at habs0 habsA
      have habsB' : absNode.absEntries (d + 1) h' B = some tsB := by
        rw [absEntries_congr (fun e he => habsB e.2 (List.mem_map_of_mem he))]; exact htsB
      have hLsub : ∀ i ∈ LcL ++ LcR, i ∈ Lc ∨ (h.fresh ≤ i ∧ i < h'.fresh) := hgrow.2.1
      have hFlt : ∀ i ∈ Lf, i < h.fresh := fun i hi => hb i (hFalloc i hi)
      have hBlt : ∀ i ∈ Lb, i < h.fresh := fun i hi => hb i (hBalloc i hi)
      -- The tree-level branch is the heap-level one with children abstracted.
      have hF0 : absF (d + 1) h' c0 = t0' := absF_of_some habs0
      have hFrid : absF (d + 1) h' rid = r := absF_of_some hsubR.abs
      have hAmap : A' = A.map fun e => (e.1, absF (d + 1) h' e.2) := absEntries_eq_map habsA
      have hBmap : tsB = B.map fun e => (e.1, absF (d + 1) h' e.2) := absEntries_eq_map habsB'
      have hbranch : (⟨t0', A' ++ tsB⟩ : Branch K (Node K V)) =
          Branch.mapC (absF (d + 1) h') ⟨c0, es⟩ := by
        simp only [Branch.mapC, hF0]
        rw [hAmap, hBmap, hesAB, List.map_append]
      have hes' : absNode.absEntries (d + 1) h' es = some (A' ++ tsB) := by
        rw [hesAB, absEntries_append, habsA]
        simp only [Option.bind_some]
        rw [habsB']
        rfl
      have hins' : absNode.absEntries (d + 1) h' (insertAt es A.length (sep, rid)) =
          some (insertAt (A' ++ tsB) A.length (sep, r)) :=
        absEntries_insertAt hes' A.length sep hsubR.abs
      have hinsmap : insertAt (A' ++ tsB) A.length (sep, r) =
          (insertAt es A.length (sep, rid)).map fun e => (e.1, absF (d + 1) h' e.2) :=
        absEntries_eq_map hins'
      have hchildsome : ∀ c ∈ c0 :: (insertAt es A.length (sep, rid)).map (·.2),
          ∃ t, absNode (d + 1) h' c = some t := by
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨t0', habs0⟩
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
          exact absEntries_child_some hins' e he
      have hlvLne : lvL ≠ [] := ((leaf_facts (d + 1)).1 h' _ LcL lvL hsubL.reach hsubL.leaves).1
      have hlvRne : lvR ≠ [] := ((leaf_facts (d + 1)).1 h' _ LcR lvR hsubR.reach hsubR.leaves).1
      -- The whole children list after the insert, and its walks under `h'`.
      have hcs' : c0 :: (insertAt es A.length (sep, rid)).map (·.2) =
          frontIds c0 A ++ lastChild c0 A :: rid :: B.map (·.2) := by
        rw [hesAB]; exact insertAt_children c0 A B sep rid
      have hLall : reachIds.reachChildren (d + 1) h'
          (frontIds c0 A ++ lastChild c0 A :: rid :: B.map (·.2)) =
          some (Lf ++ (LcL ++ (LcR ++ Lb))) := by
        rw [reachChildren_append, reachChildren_cons, reachChildren_cons, hLf', hsubL.reach,
          hsubR.reach, hLb']
        rfl
      have hlvall : leafIds.leafChildren (d + 1) h'
          (frontIds c0 A ++ lastChild c0 A :: rid :: B.map (·.2)) =
          some (lvF ++ (lvL ++ (lvR ++ lvB))) := by
        rw [leafChildren_append, leafChildren_cons, leafChildren_cons, hlvF', hlvF, hsubL.leaves,
          hsubR.leaves, hlvB', hlvB]
        rfl
      have hidall : id ∉ Lf ++ (LcL ++ (LcR ++ Lb)) := by
        intro hin
        rcases List.mem_append.mp hin with hin | hin
        · exact hidLf hin
        rcases List.mem_append.mp hin with hin | hin
        · rcases hLsub id (List.mem_append_left _ hin) with hin | ⟨hge, _⟩
          · exact hidLc hin
          · omega_id
        rcases List.mem_append.mp hin with hin | hin
        · rcases hLsub id (List.mem_append_right _ hin) with hin | ⟨hge, _⟩
          · exact hidLc hin
          · omega_id
        · exact hidLb hin
      have hallNd : (Lf ++ (LcL ++ (LcR ++ Lb))).Nodup := by
        rw [nodup_append_iff]
        refine ⟨hLfNd, ?_, ?_⟩
        · rw [← List.append_assoc, nodup_append_iff]
          refine ⟨hLRNd, hLbNd, fun a ha b hb' => ?_⟩
          rcases hLsub a ha with ha' | ⟨hge, _⟩
          · exact hCBdisj a ha' b hb'
          · have := hBlt b hb'; omega_id
        · intro a ha b hb'
          rw [← List.append_assoc] at hb'
          rcases List.mem_append.mp hb' with hb' | hb'
          · rcases hLsub b hb' with hb'' | ⟨hge, _⟩
            · exact hFdisj a ha b (List.mem_append_left _ hb'')
            · have := hFlt a ha; omega_id
          · exact hFdisj a ha b (List.mem_append_right _ hb')
      have hallalloc : ∀ i ∈ Lf ++ (LcL ++ (LcR ++ Lb)), i < h'.fresh := by
        intro i hi
        apply hb'
        rcases List.mem_append.mp hi with hi | hi
        · have := hsameF i hi
          rcases hg0 : h.get i with _ | (⟨kvs, p, n⟩ | ⟨c0', es'⟩)
          · have := hFalloc i hi; rw [hg0] at this; cases this
          · rw [hg0] at this; obtain ⟨p', n', heq⟩ := sameContent_leaf_inv this; simp [heq]
          · rw [hg0] at this; rw [sameContent_branch_inv this]; rfl
        rcases List.mem_append.mp hi with hi | hi
        · exact mem_reachIds_allocated (d + 1) h' _ _ hsubL.reach i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact mem_reachIds_allocated (d + 1) h' _ _ hsubR.reach i hi
        · have := hsameB i hi
          rcases hg0 : h.get i with _ | (⟨kvs, p, n⟩ | ⟨c0', es'⟩)
          · have := hBalloc i hi; rw [hg0] at this; cases this
          · rw [hg0] at this; obtain ⟨p', n', heq⟩ := sameContent_leaf_inv this; simp [heq]
          · rw [hg0] at this; rw [sameContent_branch_inv this]; rfl
      -- The chain, reassembled at `h'`.
      have hlink' : Linked h' prev0 (lvF ++ ((lvL ++ lvR) ++ lvB)) next0 := by
        have := linked_reassemble (lvC' := lvL ++ lvR) (by rw [List.append_assoc]; exact hl) hlLR
          (by rw [head?_append_of_ne_nil _ hlvLne]; exact hheadL)
          (fun i hi => hunchF i (hlvFmem i hi) ?_) ?_ ?_
        · rwa [List.append_assoc] at this
        · intro heq
          have ha := List.mem_of_mem_head? heq
          exact hFdisj i (hlvFmem i hi) i (List.mem_append_right _ (hlvBmem i ha)) rfl
        · intro a rest hlvBeq O p n hga
          exact hfrC.2 a O p n (by rw [hlvBeq]; rfl) hga
        · intro a rest hlvBeq i hi
          apply hunchB i (hlvBmem i (by rw [hlvBeq]; exact List.mem_cons_of_mem _ hi))
          rw [hlvBeq]
          intro heq
          simp at heq
          subst heq
          have := hlvBNd; rw [hlvBeq] at this
          exact (List.nodup_cons.mp this).1 hi
      have hhead' : (lvF ++ (lvL ++ (lvR ++ lvB))).head? = (lvF ++ (lvC ++ lvB)).head? := by
        cases lvF with
        | nil =>
          simp only [List.nil_append]
          rw [head?_append_of_ne_nil _ hlvLne, head?_append_of_ne_nil _ hlvCne, hheadL]
        | cons a t => rfl
      have hgrow' : ∀ ids', (∀ i, i ∈ ids' ↔ i ∈ id :: (Lf ++ (LcL ++ (LcR ++ Lb)))) →
          ∀ hf : Heap K V, hf.fresh = h'.fresh → IdsGrow h hf (id :: (Lf ++ (Lc ++ Lb))) ids' := by
        intro ids' hmem hf hfr
        refine ⟨fun i hi => (hmem i).mpr ?_, fun i hi => ?_, fun i h1 h2 => (hmem i).mpr ?_⟩
        · rcases List.mem_cons.mp hi with rfl | hi
          · exact List.mem_cons_self
          rcases List.mem_append.mp hi with hi | hi
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ hi)
          rcases List.mem_append.mp hi with hi | hi
          · rcases List.mem_append.mp (hgrow.1 i hi) with hi' | hi'
            · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ hi'))
            · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
                (List.mem_append_left _ hi')))
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
              (List.mem_append_right _ hi)))
        · rw [hfr]
          have hi := (hmem i).mp hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact Or.inl List.mem_cons_self
          rcases List.mem_append.mp hi with hi | hi
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append_left _ hi))
          rcases List.mem_append.mp hi with hi | hi
          · rcases hLsub i (List.mem_append_left _ hi) with hi' | hnew
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append_right _
                (List.mem_append_left _ hi')))
            · exact Or.inr hnew
          rcases List.mem_append.mp hi with hi | hi
          · rcases hLsub i (List.mem_append_right _ hi) with hi' | hnew
            · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append_right _
                (List.mem_append_left _ hi')))
            · exact Or.inr hnew
          · exact Or.inl (List.mem_cons_of_mem _ (List.mem_append_right _
              (List.mem_append_right _ hi)))
        · rw [hfr] at h2
          rcases List.mem_append.mp (hgrow.2.2 i h1 h2) with hi | hi
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _ hi))
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
              (List.mem_append_left _ hi)))
      have hframe1 : ∀ i, i ∉ id :: (Lf ++ (Lc ++ Lb)) → next0 ≠ some i → i < h.fresh →
          h'.get i = h.get i := by
        intro i hi hio hlt
        apply hfrC.1 i (fun hin => hi (List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_append_left _ hin)))) _ hlt
        cases hh : lvB.head? with
        | none => simpa using hio
        | some a =>
          simp
          intro heq; subst heq
          exact hi (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
            (hlvBmem _ (List.mem_of_mem_head? hh)))))
      have hframe2 : ∀ o O p n, next0 = some o → h.get o = some (.leaf O p n) →
          h'.get o = some (.leaf O ((lvF ++ (lvL ++ (lvR ++ lvB))).getLast?.or prev0) n) := by
        intro o O p n ho hgo
        cases hlvBcase : lvB with
        | nil =>
          subst hlvBcase
          rw [hfrC.2 o O p n (by simpa using ho) hgo]
          try (congr 2)
          try simp only [List.append_nil, List.getLast?_append, Option.or_assoc]
        | cons a rest =>
          subst hlvBcase
          have hoa : o ≠ a := fun heq => hnext0B o ho (hlvBmem o (by rw [heq]; exact List.mem_cons_self))
          rw [hfrC.1 o (fun hin => (hnext o ho).1 (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_append_left _ hin))))
            (by simpa using (Ne.symm hoa)) (hb o (by simp [hgo])), hgo]
          obtain ⟨hno, O', n', hgo'⟩ := hnext o ho
          rw [hgo] at hgo'
          simp only [Option.some.injEq, NodeRec.leaf.injEq] at hgo'
          obtain ⟨_, hp, _⟩ := hgo'
          try rw [hp]
          try (congr 2)
          try simp only [List.getLast?_append, List.getLast?_cons, Option.some_or]
      rcases hbas : branchApplySplit bc ⟨c0, es⟩ A.length sep rid with b | ⟨lb, pk, rb⟩
      · -- This branch absorbs the entry: one write.
        have hb_eq : b = ⟨c0, insertAt es A.length (sep, rid)⟩ := by
          unfold branchApplySplit at hbas
          split at hbas
          · cases hbas; rfl
          · split at hbas; cases hbas
        subst hb_eq
        have hbas_t : branchApplySplit bc ⟨t0', A' ++ tsB⟩ tsA.length sep r =
            .noSplit (Branch.mapC (absF (d + 1) h') ⟨c0, insertAt es A.length (sep, rid)⟩) := by
          rw [hbranch, hlenA, ← hFrid, branchApplySplit_mapC, hbas]; rfl
        obtain ⟨h'', hw⟩ := Heap.write_some (h := h') (id := id)
          (r := .branch c0 (insertAt es A.length (sep, rid))) (by simp [hid'])
        have hg'' := Heap.get_write_self hw
        have hsame'' : ∀ i ∈ Lf ++ (LcL ++ (LcR ++ Lb)), SameContent (h'.get i) (h''.get i) :=
          fun i hi => sameContent_of_eq (Heap.get_write_other hw (fun heq => hidall (heq ▸ hi)))
        obtain ⟨hLall'', habsAll, hlvall''⟩ := children_congr (d + 1) _ _ hLall hsame''
        have habsE : absNode.absEntries (d + 1) h'' (insertAt es A.length (sep, rid)) =
            some ((insertAt es A.length (sep, rid)).map fun e => (e.1, absF (d + 1) h' e.2)) := by
          rw [absEntries_congr (fun e he => habsAll e.2 (by
            rw [← hcs']; exact List.mem_cons_of_mem _ (List.mem_map_of_mem he))), hins', hinsmap]
        have habs0'' : absNode (d + 1) h'' c0 = some (absF (d + 1) h' c0) := by
          rw [habsAll c0 (by rw [← hcs']; exact List.mem_cons_self), habs0, hF0]
        refine ⟨.noSplit none, h'', ?_, Heap.bounded_write hw hb',
          le_trans hfr' (le_of_eq (Heap.fresh_write hw).symm), ?_⟩
        · rw [insertRecH]; simp only [hg, hA, hrec, hbas, hw]; rfl
        simp only [InsertPost]
        rw [insertRec]
        simp only [hAt, hBt, htc, hrl, hbas_t]
        refine ⟨by trivial, id :: (Lf ++ (LcL ++ (LcR ++ Lb))), lvF ++ (lvL ++ (lvR ++ lvB)),
          ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
        · rw [absNode_branch hg'', habs0'']
          simp only [Option.bind_some]
          rw [habsE]
          rfl
        · rw [reachIds_branch hg'', hcs', hLall'']; rfl
        · rw [leafIds_branch hg'', hcs', hlvall'', hlvall]
        · rw [List.nodup_cons]; exact ⟨hidall, hallNd⟩
        · exact hgrow' _ (fun i => Iff.rfl) h'' (Heap.fresh_write hw)
        · exact hhead'
        · have := linked_congr (h' := h'') (fun i hi => Heap.get_write_other hw (fun heq => ?_)) hlink'
          · rwa [List.append_assoc] at this
          · subst heq
            have hlvsub : ∀ j ∈ lvF ++ ((lvL ++ lvR) ++ lvB), j ∈ Lf ++ (LcL ++ (LcR ++ Lb)) := by
              intro j hj
              rw [List.append_assoc] at hj
              rcases List.mem_append.mp hj with hj | hj
              · exact List.mem_append_left _ (hlvFmem j hj)
              rcases List.mem_append.mp hj with hj | hj
              · exact List.mem_append_right _ (List.mem_append_left _
                  (((leaf_facts (d + 1)).1 h' _ LcL lvL hsubL.reach hsubL.leaves).2.subset hj))
              rcases List.mem_append.mp hj with hj | hj
              · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
                  (((leaf_facts (d + 1)).1 h' _ LcR lvR hsubR.reach hsubR.leaves).2.subset hj)))
              · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
                  (hlvBmem j hj)))
            exact hidall (hlvsub _ hi)
        · refine ⟨fun i hi hio hlt => ?_, fun o O p n ho hgo => ?_⟩
          · rw [Heap.get_write_other hw (fun heq => hi (heq ▸ List.mem_cons_self))]
            exact hframe1 i hi hio hlt
          · rw [Heap.get_write_other hw (hnext0id o ho)]
            exact hframe2 o O p n ho hgo
      · -- This branch splits too: allocate the right half, write the left.
        have hnlt : ¬ es.length < bc ∧
            branchInsertAndSplit ⟨c0, es⟩ A.length sep rid = (lb, pk, rb) := by
          unfold branchApplySplit at hbas
          split at hbas
          · cases hbas
          · rename_i hnlt
            split at hbas
            rename_i l' pk' r' heq
            cases hbas
            exact ⟨hnlt, heq⟩
        obtain ⟨hnlt, hbis⟩ := hnlt
        have hidx : A.length ≤ es.length := by rw [hesAB]; simp
        have hlen1 : 1 ≤ es.length := by omega
        have hcc := branchInsertAndSplit_concat ⟨c0, es⟩ A.length sep rid hidx hlen1
        rw [hbis] at hcc
        obtain ⟨hlbc0, hconcat⟩ := hcc
        simp only at hlbc0 hconcat
        have hbas_t : branchApplySplit bc ⟨t0', A' ++ tsB⟩ tsA.length sep r =
            .split (lb.mapC (absF (d + 1) h')) pk (rb.mapC (absF (d + 1) h')) := by
          rw [hbranch, hlenA, ← hFrid, branchApplySplit_mapC, hbas]; rfl
        -- The heap: allocate the right half, then write the left.
        have hidlt' : id < h'.fresh := lt_of_lt_of_le hid hfr'
        have hg1id : (h'.alloc (.branch rb.c0 rb.entries)).2.get id = some (.branch c0 es) := by
          rw [Heap.get_alloc_other h' _ (by omega_id)]; exact hid'
        have hg1r : (h'.alloc (.branch rb.c0 rb.entries)).2.get h'.fresh =
            some (.branch rb.c0 rb.entries) := Heap.get_alloc_self h' _
        obtain ⟨h'', hw⟩ := Heap.write_some (h := (h'.alloc (.branch rb.c0 rb.entries)).2)
          (id := id) (r := .branch lb.c0 lb.entries) (by simp [hg1id])
        have hg''id := Heap.get_write_self hw
        have hg''r : h''.get h'.fresh = some (.branch rb.c0 rb.entries) := by
          rw [Heap.get_write_other hw (by omega_id)]; exact hg1r
        have hfresh'' : h''.fresh = h'.fresh + 1 := by
          rw [Heap.fresh_write hw, Heap.fresh_alloc]
        have hother : ∀ i, i ≠ id → i ≠ h'.fresh → h''.get i = h'.get i := fun i h1 h2 => by
          rw [Heap.get_write_other hw h1, Heap.get_alloc_other h' _ h2]
        have hb'' : Heap.Bounded h'' := Heap.bounded_write hw (Heap.bounded_alloc _ hb')
        have hsame'' : ∀ i ∈ Lf ++ (LcL ++ (LcR ++ Lb)), SameContent (h'.get i) (h''.get i) :=
          fun i hi => sameContent_of_eq (hother i (fun heq => hidall (heq ▸ hi))
            (by have := hallalloc i hi; omega_id))
        obtain ⟨hLall'', habsAll, hlvall''⟩ := children_congr (d + 1) _ _ hLall hsame''
        -- The two halves' children lists together are the inserted list's.
        have hcsplit : (lb.c0 :: lb.entries.map (·.2)) ++ (rb.c0 :: rb.entries.map (·.2)) =
            frontIds c0 A ++ lastChild c0 A :: rid :: B.map (·.2) := by
          rw [← hcs', hlbc0, ← hconcat, List.map_append, List.map_cons]
          rfl
        have hLall2 : reachIds.reachChildren (d + 1) h''
            ((lb.c0 :: lb.entries.map (·.2)) ++ (rb.c0 :: rb.entries.map (·.2))) =
            some (Lf ++ (LcL ++ (LcR ++ Lb))) := by rw [hcsplit]; exact hLall''
        have hlvall2 : leafIds.leafChildren (d + 1) h''
            ((lb.c0 :: lb.entries.map (·.2)) ++ (rb.c0 :: rb.entries.map (·.2))) =
            some (lvF ++ (lvL ++ (lvR ++ lvB))) := by rw [hcsplit, hlvall'']; exact hlvall
        rw [reachChildren_append] at hLall2
        rw [leafChildren_append] at hlvall2
        rcases hLL : reachIds.reachChildren (d + 1) h'' (lb.c0 :: lb.entries.map (·.2))
          with _ | LL
        · rw [hLL] at hLall2; cases hLall2
        rcases hLR : reachIds.reachChildren (d + 1) h'' (rb.c0 :: rb.entries.map (·.2))
          with _ | LR
        · rw [hLL, hLR] at hLall2; cases hLall2
        rw [hLL, hLR] at hLall2
        simp only [Option.bind_some, Option.some.injEq] at hLall2
        rcases hlvL' : leafIds.leafChildren (d + 1) h'' (lb.c0 :: lb.entries.map (·.2))
          with _ | lvL'
        · rw [hlvL'] at hlvall2; cases hlvall2
        rcases hlvR' : leafIds.leafChildren (d + 1) h'' (rb.c0 :: rb.entries.map (·.2))
          with _ | lvR'
        · rw [hlvL', hlvR'] at hlvall2; cases hlvall2
        rw [hlvL', hlvR'] at hlvall2
        simp only [Option.bind_some, Option.some.injEq] at hlvall2
        -- The halves' children abstract under `h''` as under `h'`.
        have habsC : ∀ c ∈ (lb.c0 :: lb.entries.map (·.2)) ++ (rb.c0 :: rb.entries.map (·.2)),
            absNode (d + 1) h'' c = some (absF (d + 1) h' c) := by
          intro c hc
          rw [hcsplit, ← hcs'] at hc
          obtain ⟨t, ht⟩ := hchildsome c hc
          rw [habsAll c (by rw [← hcs']; exact hc), ht, absF_of_some ht]
        have habsHalf : ∀ (b : Branch K NodeId),
            (∀ c ∈ b.c0 :: b.entries.map (·.2), absNode (d + 1) h'' c = some (absF (d + 1) h' c)) →
            absNode (d + 1) h'' b.c0 = some (absF (d + 1) h' b.c0) ∧
            absNode.absEntries (d + 1) h'' b.entries =
              some (b.entries.map fun e => (e.1, absF (d + 1) h' e.2)) := by
          intro b hall
          refine ⟨hall b.c0 List.mem_cons_self, ?_⟩
          rw [absEntries_of_all_some (fun e he =>
            ⟨_, hall e.2 (List.mem_cons_of_mem _ (List.mem_map_of_mem he))⟩)]
          congr 1
          apply List.map_congr_left
          intro e he
          rw [absF_of_some (hall e.2 (List.mem_cons_of_mem _ (List.mem_map_of_mem he)))]
        obtain ⟨habsLc0, habsLb⟩ := habsHalf lb (fun c hc => habsC c (List.mem_append_left _ hc))
        obtain ⟨habsRc0, habsRb⟩ := habsHalf rb (fun c hc => habsC c (List.mem_append_right _ hc))
        -- Bookkeeping on the halves' ids.
        have hLLNd : (LL ++ LR).Nodup := by rw [hLall2]; exact hallNd
        have hLLlt : ∀ i ∈ LL ++ LR, i < h'.fresh := by rw [hLall2]; exact hallalloc
        have hidLL : id ∉ LL ++ LR := by rw [hLall2]; exact hidall
        have hleavesmem : ∀ j ∈ lvL' ++ lvR', j ∈ LL ++ LR := by
          have := (leaf_facts (d + 1)).2 h''
            ((lb.c0 :: lb.entries.map (·.2)) ++ (rb.c0 :: rb.entries.map (·.2))) (LL ++ LR)
            (lvL' ++ lvR') (by rw [reachChildren_append, hLL, hLR]; rfl)
            (by rw [leafChildren_append, hlvL', hlvR']; rfl)
          exact fun j hj => this.2.subset hj
        -- The first leaf: `lb.c0 = c0` is still the first child.
        have hheadL' : lvL'.head? = (lvF ++ (lvC ++ lvB)).head? := by
          rw [← hhead']
          have hLall0 := hLall
          rw [← hcs', reachChildren_cons] at hLall0
          have hlvall0 := hlvall
          rw [← hcs', leafChildren_cons] at hlvall0
          rcases hL0 : reachIds (d + 1) h' c0 with _ | L0
          · rw [hL0] at hLall0; cases hLall0
          rcases hl0 : leafIds (d + 1) h' c0 with _ | l0
          · rw [hl0] at hlvall0; cases hlvall0
          rw [hL0] at hLall0; rw [hl0] at hlvall0
          have hl0ne : l0 ≠ [] := ((leaf_facts (d + 1)).1 h' c0 L0 l0 hL0 hl0).1
          have hsub0 : ∀ i ∈ L0, i ∈ Lf ++ (LcL ++ (LcR ++ Lb)) := by
            intro i hi
            rcases hR0 : reachIds.reachChildren (d + 1) h'
                ((insertAt es A.length (sep, rid)).map (·.2)) with _ | R0
            · rw [hR0] at hLall0; cases hLall0
            rw [hR0] at hLall0
            simp only [Option.bind_some, Option.some.injEq] at hLall0
            rw [← hLall0]; exact List.mem_append_left _ hi
          obtain ⟨_, _, hleq⟩ :=
            walks_congr (d + 1) h' h'' c0 L0 hL0 (fun i hi => hsame'' i (hsub0 i hi))
          have h1 : leafIds.leafChildren (d + 1) h'' (c0 :: lb.entries.map (·.2)) = some lvL' := by
            rw [← hlbc0]; exact hlvL'
          rw [leafChildren_cons, hleq, hl0] at h1
          rcases hr0 : leafIds.leafChildren (d + 1) h'' (lb.entries.map (·.2)) with _ | r0
          · rw [hr0] at h1; cases h1
          rw [hr0] at h1
          simp only [Option.bind_some, Option.some.injEq] at h1
          rcases hR0' : leafIds.leafChildren (d + 1) h'
              ((insertAt es A.length (sep, rid)).map (·.2)) with _ | rest0
          · rw [hR0'] at hlvall0; cases hlvall0
          rw [hR0'] at hlvall0
          simp only [Option.bind_some, Option.some.injEq] at hlvall0
          rw [← h1, ← hlvall0, head?_append_of_ne_nil _ hl0ne, head?_append_of_ne_nil _ hl0ne]
        -- The result.
        refine ⟨.split pk h'.fresh none, h'', ?_, hb'', by rw [hfresh'']; omega_id, ?_⟩
        · rw [insertRecH]; simp only [hg, hA, hrec, hbas]
          rw [show h'.alloc (.branch rb.c0 rb.entries) =
            (h'.fresh, (h'.alloc (.branch rb.c0 rb.entries)).2) from rfl]
          simp only [hw, Option.bind_eq_bind, Option.bind_some]
        simp only [InsertPost]
        rw [insertRec]
        simp only [hAt, hBt, htc, hrl, hbas_t]
        refine ⟨by trivial, by trivial, id :: LL, lvL', h'.fresh :: LR, lvR',
          ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, hheadL', ?_, ?_⟩
        · rw [absNode_branch hg''id, habsLc0]
          simp only [Option.bind_some]
          rw [habsLb]
          rfl
        · rw [reachIds_branch hg''id, hLL]; rfl
        · rw [leafIds_branch hg''id, hlvL']
        · rw [absNode_branch hg''r, habsRc0]
          simp only [Option.bind_some]
          rw [habsRb]
          rfl
        · rw [reachIds_branch hg''r, hLR]; rfl
        · rw [leafIds_branch hg''r, hlvR']
        · -- no id twice
          have hLLNd' := (nodup_append_iff _ _).mp hLLNd
          rw [List.cons_append, List.nodup_cons, nodup_append_iff]
          refine ⟨?_, hLLNd'.1, ?_, ?_⟩
          · intro hin
            rcases List.mem_append.mp hin with hin | hin
            · exact hidLL (List.mem_append_left _ hin)
            · rcases List.mem_cons.mp hin with heq | hin
              · omega_id
              · exact hidLL (List.mem_append_right _ hin)
          · rw [List.nodup_cons]
            refine ⟨fun hin => ?_, hLLNd'.2.1⟩
            have := hLLlt _ (List.mem_append_right _ hin); omega_id
          · intro a ha b hb'
            rcases List.mem_cons.mp hb' with rfl | hb'
            · have := hLLlt a (List.mem_append_left _ ha); omega_id
            · exact hLLNd'.2.2 a ha b hb'
        · -- ids grow: the old ones, the child's new ones, and the new right half
          have hg1 := hgrow' (id :: (Lf ++ (LcL ++ (LcR ++ Lb)))) (fun i => Iff.rfl) h' rfl
          have hmemLL : ∀ i, i ∈ LL ++ LR ↔ i ∈ Lf ++ (LcL ++ (LcR ++ Lb)) := by
            rw [hLall2]; exact fun i => Iff.rfl
          have hto : ∀ i, i ∈ id :: (Lf ++ (LcL ++ (LcR ++ Lb))) →
              i ∈ (id :: LL) ++ (h'.fresh :: LR) := by
            intro i hi
            rw [List.cons_append]
            rcases List.mem_cons.mp hi with rfl | hi
            · exact List.mem_cons_self
            rcases List.mem_append.mp ((hmemLL i).mpr hi) with hi | hi
            · exact List.mem_cons_of_mem _ (List.mem_append_left _ hi)
            · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hi))
          refine ⟨fun i hi => hto i (hg1.1 i hi), fun i hi => ?_, fun i h1 h2 => ?_⟩
          · rw [List.cons_append] at hi
            rcases List.mem_cons.mp hi with rfl | hi
            · exact Or.inl List.mem_cons_self
            rcases List.mem_append.mp hi with hi | hi
            · rcases hg1.2.1 i (List.mem_cons_of_mem _ ((hmemLL i).mp (List.mem_append_left _ hi)))
                with hi' | ⟨hge, hlt⟩
              · exact Or.inl hi'
              · right; rw [hfresh'']; omega_id
            rcases List.mem_cons.mp hi with rfl | hi
            · right; rw [hfresh'']; omega_id
            · rcases hg1.2.1 i (List.mem_cons_of_mem _ ((hmemLL i).mp (List.mem_append_right _ hi)))
                with hi' | ⟨hge, hlt⟩
              · exact Or.inl hi'
              · right; rw [hfresh'']; omega_id
          · rw [hfresh''] at h2
            by_cases hlt : i < h'.fresh
            · exact hto i (hg1.2.2 i h1 hlt)
            · have : i = h'.fresh := by omega_id
              subst this
              rw [List.cons_append]
              exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
        · -- the chain: leaf records are untouched by the two branch writes
          rw [hlvall2]
          have := linked_congr (h' := h'') (fun i hi => hother i ?_ ?_) hlink'
          · rwa [List.append_assoc] at this
          · intro heq; subst heq
            rw [List.append_assoc, ← hlvall2] at hi
            exact hidLL (hleavesmem _ hi)
          · intro heq
            rw [List.append_assoc, ← hlvall2] at hi
            have := hLLlt i (hleavesmem i hi); omega_id
        · -- the frame
          refine ⟨fun i hi hio hlt => ?_, fun o O p n ho hgo => ?_⟩
          · rw [hother i (fun heq => hi (heq ▸ List.mem_cons_self)) (by omega_id)]
            exact hframe1 i hi hio hlt
          · rw [hother o (hnext0id o ho) (by have := hb o (by simp [hgo]); omega_id), hlvall2]
            exact hframe2 o O p n ho hgo

/-! ## The whole map -/

/-- The heap invariant of a map: the root's subtree bookkeeping, no id
twice, every allocated id below `fresh`, the store holding exactly the
reachable ids, the leaves chained end to end, and the stored count. -/
def HeapInv (m : HeapMap K V) (d : Nat) (t : Node K V) : Prop :=
  ∃ root ids lv, m.root = some root ∧ Sub m.heap (d + 1) root t ids lv ∧ ids.Nodup ∧
    Heap.Bounded m.heap ∧ (∀ i, (m.heap.get i).isSome ↔ i ∈ ids) ∧
    Linked m.heap none lv none ∧ m.count = t.toList.length

/-- After an operation that keeps old ids, allocates exactly the new ones
into the subtree and leaves everything else alone, the store still holds
exactly the reachable ids. -/
theorem domain_after {h h' : Heap K V} {ids ids' : List NodeId}
    (hdom : ∀ i, (h.get i).isSome ↔ i ∈ ids) (hb' : Heap.Bounded h')
    (hgrow : IdsGrow h h' ids ids')
    (hfr : ∀ i, i ∉ ids → i < h.fresh → h'.get i = h.get i)
    (halloc' : ∀ i ∈ ids', (h'.get i).isSome) : ∀ i, (h'.get i).isSome ↔ i ∈ ids' := by
  intro i
  refine ⟨fun hi => ?_, halloc' i⟩
  by_cases hlt : i < h.fresh
  · by_cases hin : i ∈ ids
    · exact hgrow.1 i hin
    · rw [hfr i hin hlt] at hi
      exact absurd ((hdom i).mp hi) hin
  · exact hgrow.2.2 i (by omega_id) (hb' i hi)

/-- `insert` on the heap model never faults, returns what the tree model
returns, and keeps the heap invariant for the tree model's new tree. -/
theorem insertH_sim (lc bc : Nat) (hlc : 2 ≤ lc) (hbc : 2 ≤ bc) (d fuel : Nat) (hfuel : d < fuel)
    (m : HeapMap K V) (t : Node K V) (hinv : HeapInv m d t) (k : K) (v : V) (ht : Nat)
    (hwf : WF lc bc ht true none none t) :
    ∃ old m', insertH lc bc fuel m k v = some (old, m') ∧ old = (insertTree lc bc t k v).2 ∧
      ∃ d', d' ≤ d + 1 ∧ HeapInv m' d' (insertTree lc bc t k v).1 := by
  obtain ⟨root, ids, lv, hroot, hsub, hnd, hb, hdom, hchain, hcount⟩ := hinv
  have hsorted := wf_toList_sorted lc bc ht t true none none hwf
  obtain ⟨htl, hsome, hnone⟩ := insertTree_toList lc bc hlc hbc ht t k v hwf
  have hnext : NextOK m.heap ids lv none none := fun o ho => by cases ho
  obtain ⟨res, h', hrec, hb', hfr', hpost⟩ :=
    insertRecH_sim lc bc (by omega) k v d fuel m.heap root t ids lv none none hfuel hsub hnd hb
      hchain hnext
  have hcount' : ∀ (old : Option V), old = (insertTree lc bc t k v).2 →
      (if old.isNone then m.count + 1 else m.count) = (insertTree lc bc t k v).1.toList.length := by
    intro old hold
    rw [htl, hcount]
    rcases old with _ | o
    · simp only [Option.isNone_none, if_true]
      rw [length_insertSorted_absent _ (hnone hold.symm)]
    · simp only [Option.isNone_some, Bool.false_eq_true, if_false]
      rw [length_insertSorted_present _ hsorted (hsome o hold.symm)]
  -- The tree model's result, by outcome.
  rcases res with old | ⟨sep, rid, old⟩
  · simp only [InsertPost] at hpost
    split at hpost
    · rename_i t' old' htc
      obtain ⟨rfl, ids', lv', hsub', hnd', hgrow, _, hchain', hfr⟩ := hpost
      have htree : insertTree lc bc t k v = (t', old) := by
        unfold insertTree; rw [htc]
      refine ⟨old, ⟨h', some root, if old.isNone then m.count + 1 else m.count⟩, ?_, ?_, d,
        Nat.le_succ d, ?_⟩
      · simp only [insertH, hroot, hrec]; rfl
      · rw [htree]
      · rw [htree]
        have hc := hcount' old (by rw [htree])
        rw [htree] at hc
        refine ⟨root, ids', lv', rfl, hsub', hnd', hb', ?_, hchain', hc⟩
        exact domain_after hdom hb' hgrow (fun i hi hlt => hfr.1 i hi (by simp) hlt)
          (mem_reachIds_allocated (d + 1) h' root ids' hsub'.reach)
    · exact hpost.elim
  · simp only [InsertPost] at hpost
    split at hpost
    · exact hpost.elim
    rename_i l sep' r htc
    obtain ⟨rfl, rfl, idsL, lvL, idsR, lvR, hsubL, hsubR, hLRnd, hgrow, _, hchainLR, hfr⟩ := hpost
    have htree : insertTree lc bc t k v = (.branch l [(sep, r)], none) := by
      unfold insertTree; rw [htc]; rfl
    -- `grow_root`: a fresh branch over the two halves.
    have hrootlt : root < h'.fresh := hb' root (mem_reachIds_allocated (d + 1) h' root idsL hsubL.reach root (mem_reachIds_self hsubL.reach))
    have hridlt : rid < h'.fresh := hb' rid (mem_reachIds_allocated (d + 1) h' rid idsR hsubR.reach rid (mem_reachIds_self hsubR.reach))
    have hLRlt : ∀ i ∈ idsL ++ idsR, i < h'.fresh := by
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hb' i (mem_reachIds_allocated (d + 1) h' root idsL hsubL.reach i hi)
      · exact hb' i (mem_reachIds_allocated (d + 1) h' rid idsR hsubR.reach i hi)
    have hgnr : (h'.alloc (.branch root [(sep, rid)])).2.get h'.fresh =
        some (.branch root [(sep, rid)]) := Heap.get_alloc_self h' _
    have hother : ∀ i, i ≠ h'.fresh → (h'.alloc (.branch root [(sep, rid)])).2.get i = h'.get i :=
      fun i hi => Heap.get_alloc_other h' _ hi
    have hsame : ∀ i ∈ idsL ++ idsR, SameContent (h'.get i) ((h'.alloc (.branch root [(sep, rid)])).2.get i) :=
      fun i hi => sameContent_of_eq (hother i (by have := hLRlt i hi; omega_id))
    obtain ⟨hLall, habs, hlvall⟩ := children_congr (d + 1) [root, rid] (idsL ++ idsR)
      (by rw [reachChildren_cons, reachChildren_cons, hsubL.reach, hsubR.reach]
          simp [reachIds.reachChildren]) hsame
    refine ⟨none, ⟨(h'.alloc (.branch root [(sep, rid)])).2, some h'.fresh, m.count + 1⟩, ?_, ?_,
      d + 1, Nat.le_refl _, ?_⟩
    · simp only [insertH, hroot, hrec, Option.bind_eq_bind, Option.bind_some]
      rw [show h'.alloc (.branch root [(sep, rid)]) = (h'.fresh, (h'.alloc (.branch root [(sep, rid)])).2) from rfl]
      first | rfl | simp
    · rw [htree]
    · rw [htree]
      refine ⟨h'.fresh, h'.fresh :: (idsL ++ idsR), lvL ++ lvR, rfl,
        ⟨?_, ?_, ?_⟩, ?_, Heap.bounded_alloc _ hb', ?_, ?_, ?_⟩
      · rw [absNode_branch hgnr, habs root List.mem_cons_self, hsubL.abs]
        simp only [Option.bind_some]
        rw [absEntries_cons (tr := [])
          (by rw [habs rid (List.mem_cons_of_mem _ List.mem_cons_self)]; exact hsubR.abs)
          (by simp [absNode.absEntries])]
        rfl
      · rw [reachIds_branch hgnr]
        simp only [List.map_cons, List.map_nil]
        rw [hLall]
        rfl
      · rw [leafIds_branch hgnr]
        simp only [List.map_cons, List.map_nil]
        rw [hlvall, leafChildren_cons, leafChildren_cons, hsubL.leaves, hsubR.leaves]
        simp [leafIds.leafChildren]
      · rw [List.nodup_cons]
        exact ⟨fun hin => by have := hLRlt _ hin; omega_id, hLRnd⟩
      · intro i
        by_cases hi : i = h'.fresh
        · subst hi; simp [hgnr]
        · rw [hother i hi]
          have hdom' := domain_after hdom hb' hgrow (fun i hi hlt => hfr.1 i hi (by simp) hlt)
            (fun i hi => by
              rcases List.mem_append.mp hi with hi | hi
              · exact mem_reachIds_allocated (d + 1) h' root idsL hsubL.reach i hi
              · exact mem_reachIds_allocated (d + 1) h' rid idsR hsubR.reach i hi)
          rw [hdom' i]
          simp [hi]
      · exact linked_congr (fun i hi => hother i (by
          have := hLRlt i (by
            rcases List.mem_append.mp hi with hi | hi
            · exact List.mem_append_left _
                (((leaf_facts (d + 1)).1 h' root idsL lvL hsubL.reach hsubL.leaves).2.subset hi)
            · exact List.mem_append_right _
                (((leaf_facts (d + 1)).1 h' rid idsR lvR hsubR.reach hsubR.leaves).2.subset hi))
          omega_id)) hchainLR
      · have := hcount' none (by rw [htree])
        simpa [htree] using this

end HeapProofs

end BPlusTree
