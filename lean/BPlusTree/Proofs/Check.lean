import BPlusTree.Model.Check
import BPlusTree.Proofs.Tree
import BPlusTree.Proofs.Delete
import BPlusTree.Proofs.Read

/-!
# The checker accepts exactly the well-formed trees

`checkInvariants_iff`: `check_invariants_detailed` succeeds on a tree
with stored length `count` iff the tree is `WF` at some height and
`count` is its number of entries. Soundness goes by strong induction on
the height the checker returns; completeness by induction on the `WF`
height. `Map.insert_wf` and `Map.remove_wf` then carry the stored length
along with the tree invariant.
-/

namespace BPlusTree

open Std

set_option linter.unusedSectionVars false

section CheckProofs

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-! ## Lengths of the spec operations -/

theorem length_insertSorted_absent {k : K} {v : V} (l : List (K × V))
    (h : ∀ e ∈ l, e.1 ≠ k) : (insertSorted k v l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    simp only [insertSorted]
    have hne := h e List.mem_cons_self
    by_cases h1 : e.1 < k
    · rw [if_pos h1]
      simp [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    · rw [if_neg h1]
      by_cases h2 : k < e.1
      · rw [if_pos h2]; simp
      · exact absurd (le_antisymm (not_lt.mp h2) (not_lt.mp h1)) hne

theorem length_insertSorted_present {k : K} {v v0 : V} (l : List (K × V))
    (hs : Sorted l) (h : (k, v0) ∈ l) : (insertSorted k v l).length = l.length := by
  induction l with
  | nil => cases h
  | cons e rest ih =>
    simp only [Sorted, List.pairwise_cons] at hs
    simp only [insertSorted]
    by_cases h1 : e.1 < k
    · rw [if_pos h1]
      rcases List.mem_cons.mp h with he | he
      · subst he; exact (lt_irrefl h1).elim
      · simp [ih hs.2 he]
    · rw [if_neg h1]
      by_cases h2 : k < e.1
      · rw [if_pos h2]
        rcases List.mem_cons.mp h with he | he
        · subst he; exact (lt_irrefl h2).elim
        · exact (lt_irrefl (lt_trans h2 (hs.1 _ he))).elim
      · rw [if_neg h2]; simp

theorem length_eraseSorted_absent {k : K} (l : List (K × V))
    (h : ∀ e ∈ l, e.1 ≠ k) : (eraseSorted k l).length = l.length := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    simp only [eraseSorted]
    have hne := h e List.mem_cons_self
    by_cases h1 : e.1 < k
    · rw [if_pos h1]
      simp [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    · rw [if_neg h1]
      by_cases h2 : k < e.1
      · rw [if_pos h2]
      · exact absurd (le_antisymm (not_lt.mp h2) (not_lt.mp h1)) hne

theorem length_eraseSorted_present {k : K} {v0 : V} (l : List (K × V))
    (hs : Sorted l) (h : (k, v0) ∈ l) : (eraseSorted k l).length + 1 = l.length := by
  induction l with
  | nil => cases h
  | cons e rest ih =>
    simp only [Sorted, List.pairwise_cons] at hs
    simp only [eraseSorted]
    by_cases h1 : e.1 < k
    · rw [if_pos h1]
      rcases List.mem_cons.mp h with he | he
      · subst he; exact (lt_irrefl h1).elim
      · simp [← ih hs.2 he]
    · rw [if_neg h1]
      by_cases h2 : k < e.1
      · rw [if_pos h2]
        rcases List.mem_cons.mp h with he | he
        · subst he; exact (lt_irrefl h2).elim
        · exact (lt_irrefl (lt_trans h2 (hs.1 _ he))).elim
      · rw [if_neg h2]; simp

/-! ## The stored length -/

/-- The tree invariant together with the stored length: what the checker
accepts. -/
def Map.WF (lc bc : Nat) (m : Map K V) : Prop :=
  (∃ h, BPlusTree.WF lc bc h true none none m.root) ∧ m.count = m.root.toList.length

theorem Map.insert_wf (lc bc : Nat) (hlc : 2 ≤ lc) (hbc : 2 ≤ bc) (m : Map K V)
    (hm : Map.WF lc bc m) (k : K) (v : V) : Map.WF lc bc (Map.insert lc bc m k v).1 := by
  obtain ⟨⟨h, hwf⟩, hcount⟩ := hm
  have hsorted := wf_toList_sorted lc bc h m.root true none none hwf
  have hwf' := insertTree_wf lc bc hlc hbc h m.root k v hwf
  obtain ⟨htl, hsome, hnone⟩ := insertTree_toList lc bc hlc hbc h m.root k v hwf
  simp only [Map.insert]
  refine ⟨?_, ?_⟩
  · rcases hwf' with hw | hw
    · exact ⟨h, hw⟩
    · exact ⟨h + 1, hw⟩
  · simp only [htl]
    rcases hold : (insertTree lc bc m.root k v).2 with _ | o
    · simp only [Option.isNone_none, if_true]
      rw [length_insertSorted_absent _ (hnone hold), hcount]
    · simp only [Option.isNone_some, Bool.false_eq_true, if_false]
      rw [length_insertSorted_present _ hsorted (hsome o hold), hcount]

theorem Map.remove_wf (lc bc : Nat) (hlc : 4 ≤ lc) (hbc : 4 ≤ bc) (m : Map K V)
    (hm : Map.WF lc bc m) (k : K) (v : V) (m' : Map K V)
    (hrem : Map.remove lc bc m k = some (v, m')) : Map.WF lc bc m' := by
  obtain ⟨⟨h, hwf⟩, hcount⟩ := hm
  have hsorted := wf_toList_sorted lc bc h m.root true none none hwf
  have hspec := removeTree_spec lc bc hlc hbc h m.root k hwf
  simp only [Map.remove] at hrem
  rcases hres : removeTree lc bc m.root k with _ | ⟨v', root'⟩
  · rw [hres] at hrem; cases hrem
  · rw [hres] at hrem hspec
    simp only [Option.some.injEq, Prod.mk.injEq] at hrem
    obtain ⟨rfl, rfl⟩ := hrem
    obtain ⟨hmem, htl, h', _, hwf'⟩ := hspec
    refine ⟨⟨h', hwf'⟩, ?_⟩
    simp only [htl]
    have := length_eraseSorted_present _ hsorted hmem
    omega

/-! ## Keys -/

theorem keysIncreasing_iff (l : List K) : keysIncreasing l = true ↔ l.Pairwise (· < ·) := by
  induction l with
  | nil => simp [keysIncreasing]
  | cons a rest ih =>
    cases rest with
    | nil => simp [keysIncreasing]
    | cons b rest' =>
      simp only [keysIncreasing, Bool.and_eq_true, decide_eq_true_eq, ih, List.pairwise_cons]
      constructor
      · rintro ⟨hab, hb, hrest⟩
        refine ⟨?_, hb, hrest⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hab
        · exact lt_trans hab (hb x hx)
      · rintro ⟨ha, hb, hrest⟩
        exact ⟨ha b List.mem_cons_self, hb, hrest⟩

theorem head_le_of_sorted {l : List K} (hs : l.Pairwise (· < ·)) {a k : K}
    (hh : l.head? = some a) (hk : k ∈ l) : a ≤ k := by
  obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hh
  rcases List.mem_cons.mp hk with rfl | hk
  · exact le_refl _
  · exact le_of_lt ((List.pairwise_cons.mp hs).1 k hk)

theorem le_getLast_of_sorted {l : List K} (hs : l.Pairwise (· < ·)) {b k : K}
    (hl : l.getLast? = some b) (hk : k ∈ l) : k ≤ b := by
  obtain ⟨t, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  rcases List.mem_append.mp hk with hk | hk
  · exact le_of_lt ((List.pairwise_append.mp hs).2.2 k hk b (List.mem_singleton_self b))
  · rw [List.mem_singleton.mp hk]; exact le_refl _

theorem mem_of_getLast?_eq_some' {α : Type} {l : List α} {b : α} (hl : l.getLast? = some b) :
    b ∈ l := by
  obtain ⟨t, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  simp

theorem boundsOK_iff {l : List K} (hs : l.Pairwise (· < ·)) (lo hi : Option K) :
    boundsOK lo hi l = true ↔ ∀ k ∈ l, InBounds lo hi k := by
  simp only [boundsOK, Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩ k hk
    constructor
    · intro l0 hl0
      subst hl0
      rcases hh : l.head? with _ | a
      · rw [List.head?_eq_none_iff] at hh; subst hh; cases hk
      · rw [hh] at h1
        simp only [decide_eq_true_eq] at h1
        exact le_trans (not_lt.mp h1) (head_le_of_sorted hs hh hk)
    · intro h0 hh0
      subst hh0
      rcases hl : l.getLast? with _ | b
      · rw [List.getLast?_eq_none_iff] at hl; subst hl; cases hk
      · rw [hl] at h2
        simp only [decide_eq_true_eq] at h2
        exact lt_of_le_of_lt (le_getLast_of_sorted hs hl hk) h2
  · intro h
    constructor
    · rcases lo with _ | l0 <;> rcases hh : l.head? with _ | a <;> simp
      have ha : a ∈ l := List.mem_of_mem_head? hh
      exact not_lt.mpr ((h a ha).1 l0 rfl)
    · rcases hi with _ | h0 <;> rcases hl : l.getLast? with _ | b <;> simp
      have hb : b ∈ l := mem_of_getLast?_eq_some' hl
      exact (h b hb).2 h0 rfl

/-! ## The threaded state -/

/-- What the last key seen must satisfy for a list to pass `observe_leaf`. -/
def Compat (p? : Option K) (l : List (K × V)) : Prop :=
  ∀ p, p? = some p → ∀ e ∈ l, p < e.1

/-- The state after the checker has walked the entries `l`. -/
def VState.after (st : VState K) (l : List (K × V)) : VState K :=
  ⟨st.totalItems + l.length, (l.getLast?.map (·.1)).or st.prevKey⟩

theorem after_nil (st : VState K) : st.after ([] : List (K × V)) = st := by
  cases st; rfl

theorem after_append (st : VState K) (l1 l2 : List (K × V)) :
    (st.after l1).after l2 = st.after (l1 ++ l2) := by
  simp only [VState.after, List.length_append, List.getLast?_append, Nat.add_assoc]
  cases l2.getLast? <;> simp [Option.or]

theorem compat_append {p? : Option K} {l1 l2 : List (K × V)} :
    Compat p? (l1 ++ l2) ↔ Compat p? l1 ∧ Compat p? l2 := by
  constructor
  · intro h
    exact ⟨fun p hp e he => h p hp e (List.mem_append_left _ he),
      fun p hp e he => h p hp e (List.mem_append_right _ he)⟩
  · rintro ⟨h1, h2⟩ p hp e he
    rcases List.mem_append.mp he with he | he
    · exact h1 p hp e he
    · exact h2 p hp e he

/-- After walking `l1`, the last key seen is below `l2` when `l1` is and
every entry of `l1` is below every entry of `l2`. -/
theorem compat_after_of_lt {st : VState K} {l1 l2 : List (K × V)}
    (hc : Compat st.prevKey l2) (hlt : ∀ a ∈ l1, ∀ b ∈ l2, a.1 < b.1) :
    Compat (st.after l1).prevKey l2 := by
  intro p hp e he
  simp only [VState.after] at hp
  rcases hl : l1.getLast? with _ | a
  · rw [hl] at hp; exact hc p hp e he
  · rw [hl] at hp
    simp only [Option.map_some, Option.some_or, Option.some.injEq] at hp
    subst hp
    exact hlt a (mem_of_getLast?_eq_some' hl) e he

/-- Conversely, if `l2` passes after `l1` did, it passes from the start. -/
theorem compat_of_after {st : VState K} {l1 l2 : List (K × V)}
    (h1 : Compat st.prevKey l1) (h2 : Compat (st.after l1).prevKey l2) :
    Compat st.prevKey l2 := by
  intro p hp e he
  rcases hl : l1.getLast? with _ | a
  · apply h2 p _ e he
    simp [VState.after, hl, hp]
  · have ha := h2 a.1 (by simp [VState.after, hl]) e he
    exact lt_trans (h1 p hp a (mem_of_getLast?_eq_some' hl)) ha

/-! ## Leaves -/

theorem sorted_map_iff (kvs : Leaf K V) :
    (kvs.map (·.1)).Pairwise (· < ·) ↔ Sorted kvs := by
  simp [Sorted, List.pairwise_map]

theorem inBounds_map_iff (kvs : Leaf K V) (lo hi : Option K) :
    (∀ k ∈ kvs.map (·.1), InBounds lo hi k) ↔ ∀ e ∈ kvs, InBounds lo hi e.1 := by
  simp

theorem validateLeaf_sound (lc bc : Nat) {lo hi : Option K} {isRoot : Bool}
    {st st' : VState K} {kvs : Leaf K V} {d : Nat}
    (h : validateLeaf lc lo hi isRoot st kvs = some (st', d)) :
    d = 0 ∧ WF lc bc 0 isRoot lo hi (.leaf kvs) ∧ Compat st.prevKey kvs ∧
      st' = st.after kvs := by
  simp only [validateLeaf] at h
  by_cases hcap : lc < kvs.length
  · rw [if_pos hcap] at h; cases h
  rw [if_neg hcap] at h
  by_cases hempty : kvs.length = 0 ∧ isRoot = false
  · rw [if_pos hempty] at h; cases h
  rw [if_neg hempty] at h
  by_cases hmin : isRoot = false ∧ kvs.length < minLeafLen lc
  · rw [if_pos hmin] at h; cases h
  rw [if_neg hmin] at h
  have hfill : isRoot = true ∨ lc / 2 ≤ kvs.length := by
    cases isRoot
    · right; simp [minLeafLen] at hmin; omega
    · left; rfl
  by_cases hnil : kvs.length = 0
  · rw [if_pos hnil] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : kvs = [] := List.eq_nil_of_length_eq_zero hnil
    subst this
    refine ⟨rfl, ⟨by simp [Sorted], (fun e he => by cases he), by omega, hfill⟩,
      (fun p _ e he => by cases he), (after_nil st).symm⟩
  rw [if_neg hnil] at h
  by_cases hinc : keysIncreasing (kvs.map (·.1)) = false
  · rw [if_pos hinc] at h; cases h
  rw [if_neg hinc] at h
  have hsorted : Sorted kvs := by
    rw [← sorted_map_iff, ← keysIncreasing_iff]
    simpa using hinc
  by_cases hbnd : boundsOK lo hi (kvs.map (·.1)) = false
  · rw [if_pos hbnd] at h; cases h
  rw [if_neg hbnd] at h
  have hb : ∀ e ∈ kvs, InBounds lo hi e.1 := by
    rw [← inBounds_map_iff, ← boundsOK_iff ((sorted_map_iff kvs).mpr hsorted)]
    simpa using hbnd
  simp only [observeLeaf] at h
  by_cases hok : observeOK st kvs = true
  · rw [if_pos hok] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, ⟨hsorted, hb, by omega, hfill⟩, ?_, ?_⟩
    · intro p hp e he
      simp only [observeOK] at hok
      rw [hp] at hok
      rcases hh : kvs.head? with _ | k0
      · rw [List.head?_eq_none_iff] at hh; subst hh; cases he
      · rw [hh] at hok
        simp only [decide_eq_true_eq] at hok
        have hk0 : k0 ∈ kvs := List.mem_of_mem_head? hh
        have : k0.1 ≤ e.1 := by
          have hs' := (sorted_map_iff kvs).mpr hsorted
          exact head_le_of_sorted hs' (by simp [List.head?_map, hh]) (List.mem_map_of_mem he)
        exact lt_of_lt_of_le hok this
    · simp only [VState.after]
      rcases hl : kvs.getLast? with _ | a
      · rw [List.getLast?_eq_none_iff] at hl; subst hl; simp at hnil
      · rfl
  · rw [if_neg hok] at h; cases h

theorem validateLeaf_complete (lc bc : Nat) (hlc : 2 ≤ lc) {lo hi : Option K} {isRoot : Bool}
    (st : VState K) {kvs : Leaf K V} (hwf : WF lc bc 0 isRoot lo hi (.leaf kvs))
    (hc : Compat st.prevKey kvs) :
    validateLeaf lc lo hi isRoot st kvs = some (st.after kvs, 0) := by
  obtain ⟨hsorted, hb, hcap, hfill⟩ := hwf
  simp only [validateLeaf]
  rw [if_neg (by omega)]
  have hnonroot : isRoot = false → lc / 2 ≤ kvs.length := by
    intro hr; rcases hfill with h | h
    · rw [hr] at h; cases h
    · exact h
  rw [if_neg (by rintro ⟨h0, hr⟩; have := hnonroot hr; omega)]
  rw [if_neg (by rintro ⟨hr, hlt⟩; have := hnonroot hr; simp only [minLeafLen] at hlt; omega)]
  by_cases hnil : kvs.length = 0
  · rw [if_pos hnil]
    have : kvs = [] := List.eq_nil_of_length_eq_zero hnil
    subst this
    rw [after_nil]
  rw [if_neg hnil]
  have hinc : keysIncreasing (kvs.map (·.1)) = true :=
    (keysIncreasing_iff _).mpr ((sorted_map_iff kvs).mpr hsorted)
  rw [if_neg (by simp [hinc])]
  have hbnd : boundsOK lo hi (kvs.map (·.1)) = true :=
    (boundsOK_iff ((sorted_map_iff kvs).mpr hsorted) lo hi).mpr ((inBounds_map_iff kvs lo hi).mpr hb)
  rw [if_neg (by simp [hbnd])]
  simp only [observeLeaf]
  have hok : observeOK st kvs = true := by
    simp only [observeOK]
    rcases hp : st.prevKey with _ | p
    · rfl
    · rcases hh : kvs.head? with _ | k0
      · rfl
      · simp only [decide_eq_true_eq]
        exact hc p hp k0 (List.mem_of_mem_head? hh)
  rw [if_pos hok]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, VState.after]
  rcases hl : kvs.getLast? with _ | a
  · rw [List.getLast?_eq_none_iff] at hl; subst hl; simp at hnil
  · simp

/-! ## Soundness -/

theorem validate_sound (lc bc : Nat) (hbc : 3 ≤ bc) :
    ∀ d : Nat,
      (∀ (lo hi : Option K) (isRoot : Bool) (st st' : VState K) (n : Node K V),
        validateNode lc bc lo hi isRoot st n = some (st', d) →
          WF lc bc d isRoot lo hi n ∧ Compat st.prevKey n.toList ∧ st' = st.after n.toList) ∧
      (∀ (lo hi : Option K) (st st' : VState K) (c : Node K V) (es : List (K × Node K V)),
        validateChildren lc bc lo hi st c es = some (st', d) →
          ∃ d', d = d' + 1 ∧ Chain (WF lc bc d' false) lo hi c es ∧
            Compat st.prevKey (c.toList ++ entriesToList es) ∧
            st' = st.after (c.toList ++ entriesToList es)) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  have hchildren : ∀ (lo hi : Option K) (st st' : VState K) (c : Node K V)
      (es : List (K × Node K V)),
      validateChildren lc bc lo hi st c es = some (st', d) →
        ∃ d', d = d' + 1 ∧ Chain (WF lc bc d' false) lo hi c es ∧
          Compat st.prevKey (c.toList ++ entriesToList es) ∧
          st' = st.after (c.toList ++ entriesToList es) := by
    intro lo hi st st' c es
    induction es generalizing lo st st' c with
    | nil =>
      intro h
      rw [validateChildren] at h
      rcases hn : validateNode lc bc lo hi false st c with _ | ⟨st1, d1⟩
      · rw [hn] at h; cases h
      · rw [hn] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hwf, hc, hst⟩ := (ih d1 (by omega)).1 lo hi false st st1 c hn
        refine ⟨d1, rfl, hwf, ?_, ?_⟩
        · simpa [entriesToList] using hc
        · simpa [entriesToList] using hst
    | cons x rest ihes =>
      obtain ⟨s, c'⟩ := x
      intro h
      rw [validateChildren] at h
      rcases hn : validateNode lc bc lo (some s) false st c with _ | ⟨st1, d1⟩
      · rw [hn] at h; cases h
      rw [hn] at h
      dsimp only at h
      rcases hr : validateChildren lc bc (some s) hi st1 c' rest with _ | ⟨st2, d2⟩
      · rw [hr] at h; cases h
      rw [hr] at h
      dsimp only at h
      by_cases hd : d1 + 1 = d2
      · rw [if_pos hd] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hst', hdd⟩ := h
        rw [hdd] at hr
        obtain ⟨hwf, hc1, hst1⟩ := (ih d1 (by omega)).1 lo (some s) false st st1 c hn
        obtain ⟨d', hd', hchain, hc2, hst2⟩ := ihes (some s) st1 st2 c' hr
        have hdeq : d' = d1 := by omega
        refine ⟨d1, by omega, ⟨hwf, hdeq ▸ hchain⟩, ?_, ?_⟩
        · simp only [entriesToList]
          rw [compat_append]
          refine ⟨hc1, ?_⟩
          rw [hst1] at hc2
          exact compat_of_after hc1 hc2
        · rw [← hst', hst2, hst1, after_append]
          simp [entriesToList]
      · rw [if_neg hd] at h; cases h
  refine ⟨?_, hchildren⟩
  intro lo hi isRoot st st' n h
  cases n with
  | leaf kvs =>
    rw [validateNode] at h
    obtain ⟨rfl, hwf, hc, hst⟩ := validateLeaf_sound lc bc h
    exact ⟨hwf, hc, hst⟩
  | branch c0 es =>
    rw [validateNode] at h
    try dsimp only at h
    by_cases hcap : bc < es.length
    · rw [if_pos (by simpa using hcap)] at h; cases h
    rw [if_neg (by simpa using hcap)] at h
    by_cases hzero : es.length = 0
    · rw [if_pos (by simpa using hzero)] at h; cases h
    rw [if_neg (by simpa using hzero)] at h
    by_cases hmin : isRoot = false ∧ es.length < minBranchLen bc
    · rw [if_pos (by simpa using hmin)] at h; cases h
    rw [if_neg (by simpa using hmin)] at h
    by_cases hinc : keysIncreasing (es.map (·.1)) = false
    · rw [if_pos hinc] at h; cases h
    rw [if_neg hinc] at h
    have hsorted : Sorted es := by
      rw [← sorted_map_iff, ← keysIncreasing_iff]
      simpa using hinc
    by_cases hbnd : boundsOK lo hi (es.map (·.1)) = false
    · rw [if_pos hbnd] at h; cases h
    rw [if_neg hbnd] at h
    have hb : ∀ e ∈ es, InBounds lo hi e.1 := by
      rw [← inBounds_map_iff, ← boundsOK_iff ((sorted_map_iff es).mpr hsorted)]
      simpa using hbnd
    obtain ⟨d', rfl, hchain, hc, hst⟩ := hchildren lo hi st st' c0 es h
    refine ⟨⟨hsorted, hb, by omega, ?_, hchain⟩, hc, hst⟩
    rw [minBranchLen_eq hbc] at hmin
    cases isRoot
    · simp only [Bool.false_eq_true, if_false]
      simp only [true_and] at hmin
      omega
    · simp only [if_true]; omega

/-! ## Completeness -/

theorem children_of_node (lc bc : Nat) (h : Nat)
    (hnode : ∀ (lo hi : Option K) (st : VState K) (n : Node K V),
      WF lc bc h false lo hi n → Compat st.prevKey n.toList →
        validateNode lc bc lo hi false st n = some (st.after n.toList, h)) :
    ∀ (lo hi : Option K) (st : VState K) (c : Node K V) (es : List (K × Node K V)),
      Sorted es → (∀ e ∈ es, InBounds lo hi e.1) → Chain (WF lc bc h false) lo hi c es →
      Compat st.prevKey (c.toList ++ entriesToList es) →
      validateChildren lc bc lo hi st c es = some (st.after (c.toList ++ entriesToList es), h + 1) := by
  intro lo hi st c es
  induction es generalizing lo st c with
  | nil =>
    intro _ _ hchain hc
    simp only [entriesToList, List.append_nil] at hc ⊢
    rw [validateChildren, hnode lo hi st c hchain hc]
  | cons x rest ihes =>
    obtain ⟨s, c'⟩ := x
    intro hsort hb hchain hc
    simp only [Sorted, List.pairwise_cons] at hsort
    have hb' : ∀ e ∈ rest, InBounds (some s) hi e.1 := fun e he =>
      ⟨fun l hl => by cases hl; exact le_of_lt (hsort.1 e he),
        (hb e (List.mem_cons_of_mem _ he)).2⟩
    simp only [entriesToList] at hc ⊢
    rw [compat_append] at hc
    have hlt : ∀ a ∈ c.toList, ∀ b ∈ c'.toList ++ entriesToList rest, a.1 < b.1 := by
      intro a ha b hb
      have h1 := wf_toList_bounds lc bc h c false lo (some s) hchain.1 a ha
      have h2 := chain_toList_bounds (WF lc bc h false)
        (fun lo hi c hw => wf_toList_bounds lc bc h c false lo hi hw)
        rest (some s) hi c' hsort.2 hb' hchain.2 b hb
      exact lt_of_lt_of_le (h1.2 s rfl) (h2.1 s rfl)
    have hrest := ihes (some s) (st.after c.toList) c' hsort.2 hb' hchain.2
      (compat_after_of_lt hc.2 hlt)
    rw [validateChildren, hnode lo (some s) st c hchain.1 hc.1]
    dsimp only
    rw [hrest]
    dsimp only
    rw [if_pos rfl, after_append]

theorem validate_complete (lc bc : Nat) (hlc : 2 ≤ lc) (hbc : 3 ≤ bc) :
    ∀ (h : Nat) (lo hi : Option K) (isRoot : Bool) (st : VState K) (n : Node K V),
      WF lc bc h isRoot lo hi n → Compat st.prevKey n.toList →
        validateNode lc bc lo hi isRoot st n = some (st.after n.toList, h) := by
  intro h
  induction h with
  | zero =>
    intro lo hi isRoot st n hwf hc
    cases n with
    | branch _ _ => exact absurd hwf id
    | leaf kvs =>
      rw [validateNode]
      exact validateLeaf_complete lc bc hlc st hwf hc
  | succ h ih =>
    intro lo hi isRoot st n hwf hc
    cases n with
    | leaf _ => exact absurd hwf id
    | branch c0 es =>
      obtain ⟨hsorted, hb, hcap, hfill, hchain⟩ := hwf
      have hpos : 1 ≤ es.length := by
        split at hfill
        · exact hfill
        · omega
      rw [validateNode]
      try dsimp only
      rw [if_neg (by simp only [List.length_map]; omega),
        if_neg (by simp only [List.length_map]; omega)]
      rw [if_neg (by
        rintro ⟨hr, hlt⟩
        rw [hr] at hfill
        simp only [Bool.false_eq_true, if_false] at hfill
        rw [minBranchLen_eq hbc] at hlt
        simp at hlt
        omega)]
      have hinc : keysIncreasing (es.map (·.1)) = true :=
        (keysIncreasing_iff _).mpr ((sorted_map_iff es).mpr hsorted)
      rw [if_neg (by simp [hinc])]
      have hbnd : boundsOK lo hi (es.map (·.1)) = true :=
        (boundsOK_iff ((sorted_map_iff es).mpr hsorted) lo hi).mpr
          ((inBounds_map_iff es lo hi).mpr hb)
      rw [if_neg (by simp [hbnd])]
      have hnode : ∀ (lo hi : Option K) (st : VState K) (n : Node K V),
          WF lc bc h false lo hi n → Compat st.prevKey n.toList →
            validateNode lc bc lo hi false st n = some (st.after n.toList, h) :=
        fun lo hi st n hw hc => ih lo hi false st n hw hc
      exact children_of_node lc bc h hnode lo hi st c0 es hsorted hb hchain hc

/-! ## The equivalence -/

/-- `check_invariants_detailed` accepts a tree with stored length `count`
exactly when the tree is well-formed and `count` is its number of
entries. -/
theorem checkInvariants_iff (lc bc : Nat) (hlc : 2 ≤ lc) (hbc : 3 ≤ bc) (m : Map K V) :
    checkInvariants lc bc m.root m.count = true ↔ Map.WF lc bc m := by
  constructor
  · intro h
    simp only [checkInvariants] at h
    rcases hv : validateNode lc bc none none true ⟨0, none⟩ m.root with _ | ⟨st, d⟩
    · rw [hv] at h; cases h
    · rw [hv] at h
      simp only [decide_eq_true_eq] at h
      obtain ⟨hwf, _, hst⟩ := (validate_sound lc bc hbc d).1 none none true _ st m.root hv
      refine ⟨⟨d, hwf⟩, ?_⟩
      rw [← h, hst]
      simp [VState.after]
  · rintro ⟨⟨h, hwf⟩, hcount⟩
    have := validate_complete lc bc hlc hbc h none none true ⟨0, none⟩ m.root hwf
      (fun p hp => by cases hp)
    simp only [checkInvariants]
    rw [this]
    simp [VState.after, hcount]

end CheckProofs

end BPlusTree
