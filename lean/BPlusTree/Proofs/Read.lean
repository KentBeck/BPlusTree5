import BPlusTree.Model.Read
import BPlusTree.Proofs.Leaf
import BPlusTree.Proofs.Tree

/-!
# Correctness of the read paths

`get` answers membership in `toList`; `first` and `last` are its head and
last entry; `range` is `rangeSorted` on it. The range proof turns the
model's positions (indices into `toList`) into counts: on a sorted list
the entries below the start bound form a prefix, and so do those within
the end bound, so `resolve_front` lands on the first count and
`resolve_back` on the second, and the slice between them is the spec.
-/

namespace BPlusTree

open Std

set_option linter.unusedSectionVars false

/-! ## Prefix predicates on lists -/

section Prefix

variable {α : Type} {P : α → Bool}

/-- If `P` fails at the head of a list on which `P` is a prefix property,
it fails everywhere. -/
theorem countP_eq_zero_of_head_false {a : α} {l : List α}
    (hmono : (a :: l).Pairwise fun x y => P y = true → P x = true) (ha : P a = false) :
    l.countP P = 0 := by
  rw [List.countP_eq_zero]
  intro b hb hPb
  have := (List.pairwise_cons.mp hmono).1 b hb hPb
  simp [ha] at this

theorem length_takeWhile_eq_countP {l : List α}
    (hmono : l.Pairwise fun x y => P y = true → P x = true) :
    (l.takeWhile P).length = l.countP P := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hm := List.pairwise_cons.mp hmono
    by_cases ha : P a = true
    · rw [List.takeWhile_cons_of_pos ha]
      simp [ha, ih hm.2]
    · have ha' : P a = false := by simpa using ha
      rw [List.takeWhile_cons_of_neg ha]
      simp [ha', countP_eq_zero_of_head_false hmono ha']

theorem takeWhile_eq_take_countP {l : List α}
    (hmono : l.Pairwise fun x y => P y = true → P x = true) :
    l.takeWhile P = l.take (l.countP P) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hm := List.pairwise_cons.mp hmono
    by_cases ha : P a = true
    · rw [List.takeWhile_cons_of_pos ha]
      simp [ha, ih hm.2]
    · have ha' : P a = false := by simpa using ha
      rw [List.takeWhile_cons_of_neg ha]
      simp [ha', countP_eq_zero_of_head_false hmono ha']

theorem dropWhile_eq_drop_countP {l : List α}
    (hmono : l.Pairwise fun x y => P y = true → P x = true) :
    l.dropWhile P = l.drop (l.countP P) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hm := List.pairwise_cons.mp hmono
    by_cases ha : P a = true
    · rw [List.dropWhile_cons_of_pos ha]
      simp [ha, ih hm.2]
    · have ha' : P a = false := by simpa using ha
      rw [List.dropWhile_cons_of_neg ha]
      simp [ha', countP_eq_zero_of_head_false hmono ha']

/-- Slot `i` satisfies a prefix property iff `i` is below its count. -/
theorem getElem?_sat_iff {l : List α} {i : Nat} {x : α}
    (hmono : l.Pairwise fun x y => P y = true → P x = true) (hx : l[i]? = some x) :
    P x = true ↔ i < l.countP P := by
  induction l generalizing i with
  | nil => simp at hx
  | cons a l ih =>
    have hm := List.pairwise_cons.mp hmono
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      by_cases ha : P a = true
      · simp [ha]
      · have ha' : P a = false := by simpa using ha
        simp [ha', countP_eq_zero_of_head_false hmono ha']
    | succ j =>
      simp only [List.getElem?_cons_succ] at hx
      by_cases ha : P a = true
      · simp only [List.countP_cons, ha, if_true]
        rw [ih hm.2 hx]; omega
      · have ha' : P a = false := by simpa using ha
        have hx0 : ¬ P x = true := fun hPx => by
          have := hm.1 x (List.mem_of_getElem? hx) hPx
          simp [ha'] at this
        simp [ha', countP_eq_zero_of_head_false hmono ha', hx0]

theorem countP_drop {l : List α} (n : Nat)
    (hmono : l.Pairwise fun x y => P y = true → P x = true) :
    (l.drop n).countP P = l.countP P - n := by
  induction l generalizing n with
  | nil => simp
  | cons a l ih =>
    cases n with
    | zero => simp
    | succ m =>
      have hm := List.pairwise_cons.mp hmono
      simp only [List.drop_succ_cons]
      rw [ih m hm.2]
      by_cases ha : P a = true
      · simp only [List.countP_cons, ha, if_true]; omega
      · have ha' : P a = false := by simpa using ha
        simp only [List.countP_cons, ha', countP_eq_zero_of_head_false hmono ha']
        simp

end Prefix

section ReadProofs

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-! ## Sorted lists -/

/-- A key-monotone predicate is a prefix property on a sorted leaf. -/
theorem mono_of_sorted {l : Leaf K V} {P : K × V → Bool} (hs : Sorted l)
    (hdc : ∀ a b : K × V, a.1 < b.1 → P b = true → P a = true) :
    l.Pairwise fun x y => P y = true → P x = true :=
  List.Pairwise.imp (fun {a b} hab => hdc a b hab) hs

/-- A sorted list carries at most one value per key. -/
theorem sorted_val_unique {l : Leaf K V} (hs : Sorted l) {k : K} {v v' : V}
    (h1 : (k, v) ∈ l) (h2 : (k, v') ∈ l) : v = v' := by
  induction l with
  | nil => cases h1
  | cons a l ih =>
    simp only [Sorted, List.pairwise_cons] at hs
    rcases List.mem_cons.mp h1 with h1a | h1b
    · rcases List.mem_cons.mp h2 with h2a | h2b
      · rw [← h1a] at h2a; exact (Prod.mk.inj h2a).2.symm
      · subst h1a
        have hlt := hs.1 (k, v') h2b
        exact (lt_irrefl hlt).elim
    · rcases List.mem_cons.mp h2 with h2a | h2b
      · subst h2a
        have hlt := hs.1 (k, v) h1b
        exact (lt_irrefl hlt).elim
      · exact ih hs.2 h1b h2b

/-- The entries of a chain of bounded, sorted children are sorted. -/
theorem chain_toList_sorted (P : Option K → Option K → Node K V → Prop)
    (hPb : ∀ lo hi c, P lo hi c → ∀ e ∈ c.toList, InBounds lo hi e.1)
    (hPs : ∀ lo hi c, P lo hi c → Sorted c.toList)
    (L : List (K × Node K V)) (lo hi : Option K) (c : Node K V) (hsort : Sorted L)
    (hb : ∀ e ∈ L, InBounds lo hi e.1) (hch : Chain P lo hi c L) :
    Sorted (c.toList ++ entriesToList L) := by
  induction L generalizing lo c with
  | nil => simp only [entriesToList, List.append_nil]; exact hPs lo hi c hch
  | cons x rest ih =>
    obtain ⟨s, ch⟩ := x
    simp only [Sorted, List.pairwise_cons] at hsort
    have hb' : ∀ x ∈ rest, InBounds (some s) hi x.1 := fun x hx =>
      ⟨fun l hl => by cases hl; exact le_of_lt (hsort.1 x hx),
        (hb x (List.mem_cons_of_mem _ hx)).2⟩
    have hrest := ih (some s) ch hsort.2 hb' hch.2
    have hleft := hPs lo (some s) c hch.1
    have hleftb := hPb lo (some s) c hch.1
    have hrightb := chain_toList_bounds P hPb rest (some s) hi ch hsort.2 hb' hch.2
    simp only [entriesToList]
    simp only [Sorted, List.pairwise_append] at hleft hrest ⊢
    exact ⟨hleft, hrest, fun a ha b hb =>
      lt_of_lt_of_le ((hleftb a ha).2 s rfl) ((hrightb b hb).1 s rfl)⟩

/-- The entries of a well-formed tree are sorted. -/
theorem wf_toList_sorted (lc bc : Nat) :
    ∀ (h : Nat) (n : Node K V) (isRoot : Bool) (lo hi : Option K),
      WF lc bc h isRoot lo hi n → Sorted n.toList := by
  intro h
  induction h with
  | zero =>
    intro n isRoot lo hi hwf
    cases n with
    | branch _ _ => exact absurd hwf id
    | leaf kvs => exact hwf.1
  | succ h ih =>
    intro n isRoot lo hi hwf
    cases n with
    | leaf _ => exact absurd hwf id
    | branch c0 entries =>
      obtain ⟨hs, hb, _, _, hchain⟩ := hwf
      exact chain_toList_sorted (WF lc bc h false)
        (fun lo hi c hw => wf_toList_bounds lc bc h c false lo hi hw)
        (fun lo hi c hw => ih c false lo hi hw) entries lo hi c0 hs hb hchain

/-! ## `leaf_for_key` -/

/-- Descending to the leaf for `k` splits `toList` into the entries before
that leaf (all below `k`), the leaf, and the entries after it (all above). -/
theorem leafForKey_spec (lc bc : Nat) (k : K) :
    ∀ (h : Nat) (n : Node K V) (isRoot : Bool) (lo hi : Option K),
      WF lc bc h isRoot lo hi n → InBounds lo hi k →
      ∀ (pre : List (K × V)) (leaf : Leaf K V) (post : List (K × V)),
        leafForKey k n = (pre, leaf, post) →
        n.toList = pre ++ leaf ++ post ∧ Sorted leaf ∧
          (∀ e ∈ pre, e.1 < k) ∧ (∀ e ∈ post, k < e.1) := by
  intro h
  induction h with
  | zero =>
    intro n isRoot lo hi hwf hk pre leaf post hres
    cases n with
    | branch _ _ => exact absurd hwf id
    | leaf kvs =>
      rw [leafForKey] at hres
      simp only [Prod.mk.injEq] at hres
      obtain ⟨rfl, rfl, rfl⟩ := hres
      exact ⟨by simp [Node.toList], hwf.1, (fun e he => by cases he), (fun e he => by cases he)⟩
  | succ h ih =>
    intro n isRoot lo hi hwf hk pre leaf post hres
    cases n with
    | leaf _ => exact absurd hwf id
    | branch c0 entries =>
      obtain ⟨hs, hb, _, _, hchain⟩ := hwf
      rw [leafForKey] at hres
      simp only [] at hres
      have hAmem : ∀ e ∈ entries.takeWhile (sepLE k), ¬ k < e.1 := by
        intro e he
        have := mem_takeWhile_imp he
        simpa [sepLE] using this
      have hBhead : ∀ e, (entries.dropWhile (sepLE k)).head? = some e → k < e.1 := by
        intro e he
        have := head_dropWhile_false he
        simpa [sepLE] using this
      have hAB : entries = entries.takeWhile (sepLE k) ++ entries.dropWhile (sepLE k) :=
        List.takeWhile_append_dropWhile.symm
      generalize hA : entries.takeWhile (sepLE k) = A at *
      generalize hB : entries.dropWhile (sepLE k) = B at *
      subst hAB
      have hchild := chain_split _ A B lo hi c0 hchain
      have hkC : InBounds (lastBound lo A) (headBound hi B) k := by
        constructor
        · intro l0 hl0
          rcases lastBound_mem lo A l0 hl0 with ⟨_, hl⟩ | ⟨c, hc⟩
          · exact hk.1 l0 hl
          · exact not_lt.mp (hAmem (l0, c) hc)
        · intro h0 hh0
          cases B with
          | nil => exact hk.2 h0 hh0
          | cons e rest =>
            simp only [headBound, Option.some.injEq] at hh0
            subst hh0
            exact hBhead e rfl
      obtain ⟨hfront, hsuffix⟩ := front_lt_of_route hs hb hchain hkC
      have htl := toList_branch_split c0 A B
      rcases hrec : leafForKey k (lastChild c0 A) with ⟨pre', leaf', post'⟩
      rw [hrec] at hres
      simp only [Prod.mk.injEq] at hres
      obtain ⟨rfl, rfl, rfl⟩ := hres
      obtain ⟨htl', hsl, hpre, hpost⟩ := ih (lastChild c0 A) false _ _ hchild hkC _ _ _ hrec
      refine ⟨?_, hsl, ?_, ?_⟩
      · rw [htl, htl']; simp [List.append_assoc]
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hfront e he
        · exact hpre e he
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hpost e he
        · exact hsuffix e he

/-! ## `get` -/

theorem leafSearch_some {kvs : Leaf K V} (hs : Sorted kvs) {k : K} {e : K × V}
    (h : leafSearch kvs k = some e) : e.1 = k ∧ e ∈ kvs := by
  obtain ⟨A, B, hAB, hlb, hA, hB⟩ := lowerBound_spec kvs k hs
  simp only [leafSearch] at h
  rw [hlb, hAB, getElem?_append_length] at h
  cases B with
  | nil => simp at h
  | cons b B' =>
    simp only [List.head?_cons] at h
    by_cases hkb : k < b.1
    · rw [if_pos hkb] at h; cases h
    · rw [if_neg hkb, Option.some.injEq] at h
      subst h
      have hb1 : ¬ b.1 < k := hB b List.mem_cons_self
      exact ⟨le_antisymm (not_lt.mp hkb) (not_lt.mp hb1), by rw [hAB]; simp⟩

theorem leafSearch_none {kvs : Leaf K V} (hs : Sorted kvs) {k : K}
    (h : leafSearch kvs k = none) : ∀ e ∈ kvs, e.1 ≠ k := by
  obtain ⟨A, B, hAB, hlb, hA, hB⟩ := lowerBound_spec kvs k hs
  simp only [leafSearch] at h
  rw [hlb, hAB, getElem?_append_length] at h
  have hsB : Sorted B := by
    rw [hAB] at hs
    exact (List.pairwise_append.mp hs).2.1
  cases B with
  | nil =>
    intro e he
    rw [hAB, List.append_nil] at he
    exact ne_of_lt (hA e he)
  | cons b B' =>
    simp only [List.head?_cons] at h
    by_cases hkb : k < b.1
    · have hgt := forall_gt_of_head_gt hsB hkb
      intro e he
      rw [hAB] at he
      rcases List.mem_append.mp he with he | he
      · exact ne_of_lt (hA e he)
      · exact (ne_of_lt (hgt e he)).symm
    · rw [if_neg hkb] at h; cases h

/-- `get` answers exactly membership in the tree's entries. -/
theorem getTree_spec (lc bc h : Nat) (root : Node K V)
    (hwf : WF lc bc h true none none root) (k : K) (v : V) :
    getTree root k = some v ↔ (k, v) ∈ root.toList := by
  have hk : InBounds (K := K) none none k :=
    ⟨(fun _ hl => by cases hl), (fun _ hh => by cases hh)⟩
  rcases hres : leafForKey k root with ⟨pre, leaf, post⟩
  obtain ⟨htl, hsl, hpre, hpost⟩ :=
    leafForKey_spec lc bc k h root true none none hwf hk pre leaf post hres
  simp only [getTree, hres]
  rw [htl]
  constructor
  · intro hget
    rcases hsearch : leafSearch leaf k with _ | e
    · rw [hsearch] at hget; cases hget
    · rw [hsearch, Option.map_some, Option.some.injEq] at hget
      obtain ⟨hek, hmem⟩ := leafSearch_some hsl hsearch
      obtain ⟨ek, ev⟩ := e
      simp only at hek hget
      subst hek hget
      simp [hmem]
  · intro hmem
    have hmem' : (k, v) ∈ leaf := by
      simp only [List.mem_append] at hmem
      rcases hmem with (h | h) | h
      · exact (lt_irrefl (hpre _ h)).elim
      · exact h
      · exact (lt_irrefl (hpost _ h)).elim
    rcases hsearch : leafSearch leaf k with _ | e
    · exact absurd rfl (leafSearch_none hsl hsearch (k, v) hmem')
    · obtain ⟨hek, hmem2⟩ := leafSearch_some hsl hsearch
      obtain ⟨ek, ev⟩ := e
      simp only at hek
      subst hek
      simp only [Option.map_some, Option.some.injEq]
      exact sorted_val_unique hsl hmem2 hmem'

/-! ## `first` and `last` -/

/-- The leftmost leaf starts `toList`, and is nonempty unless it is the
root itself. -/
theorem leftmostLeaf_spec (lc bc : Nat) (hlc : 2 ≤ lc) :
    ∀ (h : Nat) (n : Node K V) (isRoot : Bool) (lo hi : Option K),
      WF lc bc h isRoot lo hi n →
      (∃ rest, n.toList = leftmostLeaf n ++ rest) ∧
        ((isRoot = false ∨ 0 < h) → leftmostLeaf n ≠ []) := by
  intro h
  induction h with
  | zero =>
    intro n isRoot lo hi hwf
    cases n with
    | branch _ _ => exact absurd hwf id
    | leaf kvs =>
      refine ⟨⟨[], by simp [Node.toList, leftmostLeaf]⟩, fun hr hnil => ?_⟩
      obtain ⟨_, _, _, hmin⟩ := hwf
      simp only [leftmostLeaf] at hnil
      subst hnil
      rcases hr with hr | hr
      · rcases hmin with hm | hm
        · rw [hr] at hm; cases hm
        · simp at hm; omega
      · exact absurd hr (Nat.lt_irrefl 0)
  | succ h ih =>
    intro n isRoot lo hi hwf
    cases n with
    | leaf _ => exact absurd hwf id
    | branch c0 es =>
      obtain ⟨_, _, _, _, hchain⟩ := hwf
      have hc0 : WF lc bc h false lo (headBound hi es) c0 :=
        chain_split (WF lc bc h false) [] es lo hi c0 hchain
      obtain ⟨⟨rest, hrest⟩, hne⟩ := ih c0 false lo _ hc0
      refine ⟨⟨rest ++ entriesToList es, ?_⟩, fun _ => hne (Or.inl rfl)⟩
      simp only [Node.toList, leftmostLeaf, hrest, List.append_assoc]

/-- The rightmost leaf ends `toList`, and is nonempty unless it is the
root itself. -/
theorem rightmostLeaf_spec (lc bc : Nat) (hlc : 2 ≤ lc) :
    ∀ (h : Nat) (n : Node K V) (isRoot : Bool) (lo hi : Option K),
      WF lc bc h isRoot lo hi n →
      (∃ front, n.toList = front ++ rightmostLeaf n) ∧
        ((isRoot = false ∨ 0 < h) → rightmostLeaf n ≠ []) := by
  intro h
  induction h with
  | zero =>
    intro n isRoot lo hi hwf
    cases n with
    | branch _ _ => exact absurd hwf id
    | leaf kvs =>
      refine ⟨⟨[], by simp [Node.toList, rightmostLeaf]⟩, fun hr hnil => ?_⟩
      obtain ⟨_, _, _, hmin⟩ := hwf
      simp only [rightmostLeaf] at hnil
      subst hnil
      rcases hr with hr | hr
      · rcases hmin with hm | hm
        · rw [hr] at hm; cases hm
        · simp at hm; omega
      · exact absurd hr (Nat.lt_irrefl 0)
  | succ h ih =>
    intro n isRoot lo hi hwf
    cases n with
    | leaf _ => exact absurd hwf id
    | branch c0 es =>
      obtain ⟨_, _, _, _, hchain⟩ := hwf
      have hlast : WF lc bc h false (lastBound lo es) hi (lastChild c0 es) :=
        chain_split (WF lc bc h false) es [] lo hi c0 (by rwa [List.append_nil])
      obtain ⟨⟨front, hfront⟩, hne⟩ := ih (lastChild c0 es) false _ _ hlast
      have htl := toList_branch_split c0 es []
      rw [List.append_nil] at htl
      simp only [entriesToList, List.append_nil] at htl
      refine ⟨⟨frontList c0 es ++ front, ?_⟩, fun _ => ?_⟩
      · rw [htl, rightmostLeaf, hfront, List.append_assoc]
      · rw [rightmostLeaf]; exact hne (Or.inl rfl)

/-- `first` is the head of the tree's entries. -/
theorem firstTree_spec (lc bc h : Nat) (hlc : 2 ≤ lc) (root : Node K V)
    (hwf : WF lc bc h true none none root) :
    firstTree root = root.toList.head? := by
  obtain ⟨⟨rest, hrest⟩, hne⟩ := leftmostLeaf_spec lc bc hlc h root true none none hwf
  rw [firstTree, hrest, List.head?_append]
  cases h with
  | zero =>
    cases root with
    | branch _ _ => exact absurd hwf id
    | leaf kvs =>
      simp only [Node.toList, leftmostLeaf] at hrest
      have : rest = [] := by
        have := congrArg List.length hrest
        simp at this
        first | exact this.symm | exact this | exact List.eq_nil_of_length_eq_zero this
      subst this
      simp
  | succ h =>
    cases hl : leftmostLeaf root with
    | nil => exact absurd hl (hne (Or.inr (Nat.succ_pos h)))
    | cons a t => rfl

/-- `last` is the last of the tree's entries. -/
theorem lastTree_spec (lc bc h : Nat) (hlc : 2 ≤ lc) (root : Node K V)
    (hwf : WF lc bc h true none none root) :
    lastTree root = root.toList.getLast? := by
  obtain ⟨⟨front, hfront⟩, hne⟩ := rightmostLeaf_spec lc bc hlc h root true none none hwf
  rw [lastTree, hfront, List.getLast?_append]
  cases h with
  | zero =>
    cases root with
    | branch _ _ => exact absurd hwf id
    | leaf kvs =>
      simp only [Node.toList, rightmostLeaf] at hfront
      have : front = [] := by
        have := congrArg List.length hfront
        simp at this
        first | exact this.symm | exact this | exact List.eq_nil_of_length_eq_zero this
      subst this
      simp
  | succ h =>
    cases hl : (rightmostLeaf root).getLast? with
    | none =>
      exact absurd (List.getLast?_eq_none_iff.mp hl) (hne (Or.inr (Nat.succ_pos h)))
    | some a => rfl

/-! ## `range` -/

/-- The two cuts `cut_in_leaf` makes: keys `≤ k` (after an equal key) or
keys `< k` (before it). -/
def cutPred (k : K) : Bool → K × V → Bool
  | true, e => decide (¬ k < e.1)
  | false, e => decide (e.1 < k)

theorem cutPred_mono {l : Leaf K V} (hs : Sorted l) (k : K) (ae : Bool) :
    l.Pairwise fun x y => cutPred k ae y = true → cutPred k ae x = true := by
  apply mono_of_sorted hs
  intro a b hab hb
  cases ae <;> simp only [cutPred, decide_eq_true_eq] at hb ⊢
  · exact lt_trans hab hb
  · exact fun hk => hb (lt_trans hk hab)

theorem below_included (k : K) :
    (fun e : K × V => !(Bound.included k).admitsFrom e) = cutPred k false := by
  funext e; simp [Bound.admitsFrom, cutPred]

theorem below_excluded (k : K) :
    (fun e : K × V => !(Bound.excluded k).admitsFrom e) = cutPred k true := by
  funext e; simp [Bound.admitsFrom, cutPred]

theorem within_included (k : K) :
    (Bound.included k).admitsTo (V := V) = cutPred k true := by
  funext e; rfl

theorem within_excluded (k : K) :
    (Bound.excluded k).admitsTo (V := V) = cutPred k false := by
  funext e; rfl

/-- "Below the start bound" is a prefix property on a sorted list. -/
theorem below_mono {l : Leaf K V} (hs : Sorted l) (start : Bound K) :
    l.Pairwise fun x y => (!start.admitsFrom y) = true → (!start.admitsFrom x) = true := by
  apply mono_of_sorted hs
  intro a b hab hb
  cases start with
  | unbounded => simp [Bound.admitsFrom] at hb
  | included k => simp [Bound.admitsFrom] at hb ⊢; exact lt_trans hab hb
  | excluded k => simp [Bound.admitsFrom] at hb ⊢; exact fun hk => hb (lt_trans hk hab)

/-- "Within the end bound" is a prefix property on a sorted list. -/
theorem within_mono {l : Leaf K V} (hs : Sorted l) (stop : Bound K) :
    l.Pairwise fun x y => stop.admitsTo y = true → stop.admitsTo x = true := by
  apply mono_of_sorted hs
  intro a b hab hb
  cases stop with
  | unbounded => simp [Bound.admitsTo]
  | included k => simp [Bound.admitsTo] at hb ⊢; exact fun hk => hb (lt_trans hk hab)
  | excluded k => simp [Bound.admitsTo] at hb ⊢; exact lt_trans hab hb

/-- What `cut_in_leaf` returns: the leaf's neighbourhood from
`leaf_for_key`, and the cut as a count of the leaf's keys. -/
theorem cutInLeaf_spec (lc bc h : Nat) (root : Node K V)
    (hwf : WF lc bc h true none none root) (k : K) (ae : Bool)
    (pre : List (K × V)) (leaf : Leaf K V) (cut : Nat) (post : List (K × V))
    (hres : cutInLeaf root k ae = (pre, leaf, cut, post)) :
    root.toList = pre ++ leaf ++ post ∧ Sorted leaf ∧
      (∀ e ∈ pre, e.1 < k) ∧ (∀ e ∈ post, k < e.1) ∧
      cut = leaf.countP (cutPred k ae) ∧ cut ≤ leaf.length := by
  have hk : InBounds (K := K) none none k :=
    ⟨(fun _ hl => by cases hl), (fun _ hh => by cases hh)⟩
  simp only [cutInLeaf] at hres
  rcases hlf : leafForKey k root with ⟨pre', leaf', post'⟩
  rw [hlf] at hres
  simp only [Prod.mk.injEq] at hres
  obtain ⟨rfl, rfl, hcut, rfl⟩ := hres
  obtain ⟨htl, hsl, hpre, hpost⟩ :=
    leafForKey_spec lc bc k h root true none none hwf hk _ _ _ hlf
  refine ⟨htl, hsl, hpre, hpost, ?_, ?_⟩
  · rw [← hcut]
    cases ae
    · simp only [Bool.false_eq_true, if_false]
      exact length_takeWhile_eq_countP (cutPred_mono hsl k false)
    · simp only [if_true]
      exact length_takeWhile_eq_countP (cutPred_mono hsl k true)
  · rw [← hcut]
    cases ae
    · simp only [Bool.false_eq_true, if_false]
      exact le_trans (le_of_eq (length_takeWhile_eq_countP (cutPred_mono hsl k false)))
        List.countP_le_length
    · simp only [if_true]
      exact le_trans (le_of_eq (length_takeWhile_eq_countP (cutPred_mono hsl k true)))
        List.countP_le_length

/-- `resolve_front` lands on the number of entries below the start bound,
strictly inside the list, or reports none when every entry is below it. -/
theorem resolveFront_spec (lc bc h : Nat) (hlc : 2 ≤ lc) (root : Node K V)
    (hwf : WF lc bc h true none none root) (start : Bound K) :
    (∀ f, resolveFront root start = some f →
      f = root.toList.countP (fun e => !start.admitsFrom e) ∧ f < root.toList.length) ∧
    (resolveFront root start = none →
      root.toList.countP (fun e => !start.admitsFrom e) = root.toList.length) := by
  obtain ⟨⟨rest, hrest⟩, hne⟩ := leftmostLeaf_spec lc bc hlc h root true none none hwf
  cases start with
  | unbounded =>
    have hF : root.toList.countP (fun e => !(Bound.unbounded).admitsFrom e) = 0 := by
      simp [Bound.admitsFrom]
    rw [hF]
    simp only [resolveFront, Bound.key]
    by_cases hpos : (leftmostLeaf root).length > 0
    · rw [if_pos hpos]
      refine ⟨(fun f hf => ?_), (fun hn => by cases hn)⟩
      cases hf
      refine ⟨rfl, ?_⟩
      rw [hrest]; simp; omega
    · rw [if_neg hpos]
      refine ⟨(fun f hf => by cases hf), (fun _ => ?_)⟩
      rcases Nat.eq_zero_or_pos h with hz | hpos'
      · subst hz
        cases root with
        | branch _ _ => exact absurd hwf id
        | leaf kvs =>
          simp only [leftmostLeaf, Node.toList] at hpos ⊢
          omega
      · exact absurd (List.eq_nil_of_length_eq_zero (by omega)) (hne (Or.inr hpos'))
  | included k =>
    rw [below_included]
    simp only [resolveFront, Bound.key]
    rcases hcut : cutInLeaf root k false with ⟨pre, leaf, cut, post⟩
    obtain ⟨htl, hsl, hpre, hpost, hcuteq, hcutle⟩ :=
      cutInLeaf_spec lc bc h root hwf k false pre leaf cut post hcut
    have hF : root.toList.countP (cutPred k false) = pre.length + cut := by
      rw [htl, List.countP_append, List.countP_append, ← hcuteq]
      have h1 : pre.countP (cutPred k false) = pre.length :=
        List.countP_eq_length.mpr fun e he => by simp [cutPred, hpre e he]
      have h3 : post.countP (cutPred k false) = 0 :=
        List.countP_eq_zero.mpr fun e he => by simp [cutPred]; exact not_lt.mpr (le_of_lt (hpost e he))
      omega
    have hlen : root.toList.length = pre.length + leaf.length + post.length := by
      rw [htl]; simp; omega
    rw [hF]
    simp only []
    by_cases hlt : cut < leaf.length
    · rw [if_pos hlt]
      exact ⟨(fun f hf => by cases hf; omega), (fun hn => by cases hn)⟩
    · rw [if_neg hlt]
      cases post with
      | nil => exact ⟨(fun f hf => by cases hf), (fun _ => by simp at hlen; omega)⟩
      | cons p ps => exact ⟨(fun f hf => by cases hf; simp at hlen; omega), (fun hn => by cases hn)⟩
  | excluded k =>
    rw [below_excluded]
    simp only [resolveFront, Bound.key]
    rcases hcut : cutInLeaf root k true with ⟨pre, leaf, cut, post⟩
    obtain ⟨htl, hsl, hpre, hpost, hcuteq, hcutle⟩ :=
      cutInLeaf_spec lc bc h root hwf k true pre leaf cut post hcut
    have hF : root.toList.countP (cutPred k true) = pre.length + cut := by
      rw [htl, List.countP_append, List.countP_append, ← hcuteq]
      have h1 : pre.countP (cutPred k true) = pre.length :=
        List.countP_eq_length.mpr fun e he => by
          simp [cutPred]; exact not_lt.mpr (le_of_lt (hpre e he))
      have h3 : post.countP (cutPred k true) = 0 :=
        List.countP_eq_zero.mpr fun e he => by simp [cutPred, hpost e he]
      omega
    have hlen : root.toList.length = pre.length + leaf.length + post.length := by
      rw [htl]; simp; omega
    rw [hF]
    simp only []
    by_cases hlt : cut < leaf.length
    · rw [if_pos hlt]
      exact ⟨(fun f hf => by cases hf; omega), (fun hn => by cases hn)⟩
    · rw [if_neg hlt]
      cases post with
      | nil => exact ⟨(fun f hf => by cases hf), (fun _ => by simp at hlen; omega)⟩
      | cons p ps => exact ⟨(fun f hf => by cases hf; simp at hlen; omega), (fun hn => by cases hn)⟩

/-- `resolve_back` lands on the number of entries within the end bound,
or reports none when no entry is. -/
theorem resolveBack_spec (lc bc h : Nat) (hlc : 2 ≤ lc) (root : Node K V)
    (hwf : WF lc bc h true none none root) (stop : Bound K) :
    (∀ b, resolveBack root stop = some b → b = root.toList.countP stop.admitsTo) ∧
    (resolveBack root stop = none → root.toList.countP stop.admitsTo = 0) := by
  obtain ⟨⟨front, hfront⟩, hne⟩ := rightmostLeaf_spec lc bc hlc h root true none none hwf
  cases stop with
  | unbounded =>
    have hB : root.toList.countP (Bound.unbounded).admitsTo = root.toList.length := by
      simp [Bound.admitsTo]
    rw [hB]
    simp only [resolveBack, Bound.key]
    by_cases hpos : (rightmostLeaf root).length > 0
    · rw [if_pos hpos]
      exact ⟨(fun b hb => by cases hb; rfl), (fun hn => by cases hn)⟩
    · rw [if_neg hpos]
      refine ⟨(fun b hb => by cases hb), (fun _ => ?_)⟩
      rcases Nat.eq_zero_or_pos h with hz | hpos'
      · subst hz
        cases root with
        | branch _ _ => exact absurd hwf id
        | leaf kvs =>
          simp only [rightmostLeaf, Node.toList] at hpos ⊢
          omega
      · exact absurd (List.eq_nil_of_length_eq_zero (by omega)) (hne (Or.inr hpos'))
  | included k =>
    rw [within_included]
    simp only [resolveBack, Bound.key]
    rcases hcut : cutInLeaf root k true with ⟨pre, leaf, cut, post⟩
    obtain ⟨htl, hsl, hpre, hpost, hcuteq, hcutle⟩ :=
      cutInLeaf_spec lc bc h root hwf k true pre leaf cut post hcut
    have hB : root.toList.countP (cutPred k true) = pre.length + cut := by
      rw [htl, List.countP_append, List.countP_append, ← hcuteq]
      have h1 : pre.countP (cutPred k true) = pre.length :=
        List.countP_eq_length.mpr fun e he => by
          simp [cutPred]; exact not_lt.mpr (le_of_lt (hpre e he))
      have h3 : post.countP (cutPred k true) = 0 :=
        List.countP_eq_zero.mpr fun e he => by simp [cutPred, hpost e he]
      omega
    rw [hB]
    simp only []
    by_cases hgt : cut > 0
    · rw [if_pos hgt]
      exact ⟨(fun b hb => by cases hb; rfl), (fun hn => by cases hn)⟩
    · rw [if_neg hgt]
      cases pre with
      | nil => exact ⟨(fun b hb => by cases hb), (fun _ => by simp only [List.length_nil, Nat.zero_add]; omega)⟩
      | cons p ps => exact ⟨(fun b hb => by cases hb; omega), (fun hn => by cases hn)⟩
  | excluded k =>
    rw [within_excluded]
    simp only [resolveBack, Bound.key]
    rcases hcut : cutInLeaf root k false with ⟨pre, leaf, cut, post⟩
    obtain ⟨htl, hsl, hpre, hpost, hcuteq, hcutle⟩ :=
      cutInLeaf_spec lc bc h root hwf k false pre leaf cut post hcut
    have hB : root.toList.countP (cutPred k false) = pre.length + cut := by
      rw [htl, List.countP_append, List.countP_append, ← hcuteq]
      have h1 : pre.countP (cutPred k false) = pre.length :=
        List.countP_eq_length.mpr fun e he => by simp [cutPred, hpre e he]
      have h3 : post.countP (cutPred k false) = 0 :=
        List.countP_eq_zero.mpr fun e he => by
          simp [cutPred]; exact not_lt.mpr (le_of_lt (hpost e he))
      omega
    rw [hB]
    simp only []
    by_cases hgt : cut > 0
    · rw [if_pos hgt]
      exact ⟨(fun b hb => by cases hb; rfl), (fun hn => by cases hn)⟩
    · rw [if_neg hgt]
      cases pre with
      | nil => exact ⟨(fun b hb => by cases hb), (fun _ => by simp only [List.length_nil, Nat.zero_add]; omega)⟩
      | cons p ps => exact ⟨(fun b hb => by cases hb; omega), (fun hn => by cases hn)⟩

theorem makeItems_eq_front_none {root : Node K V} {start stop : Bound K}
    (hf : resolveFront root start = none) : makeItems root start stop = [] := by
  unfold makeItems; rw [hf]

theorem makeItems_eq_back_none {root : Node K V} {start stop : Bound K} {f : Nat}
    (hf : resolveFront root start = some f) (hb : resolveBack root stop = none) :
    makeItems root start stop = [] := by
  unfold makeItems; rw [hf, hb]

theorem makeItems_eq {root : Node K V} {start stop : Bound K} {f b : Nat} {first : K × V}
    (hf : resolveFront root start = some f) (hb : resolveBack root stop = some b)
    (hfirst : root.toList[f]? = some first) :
    makeItems root start stop =
      if stop.admitsTo first then (root.toList.drop f).take (b - f) else [] := by
  unfold makeItems
  rw [hf, hb]
  dsimp only
  rw [hfirst]
  cases stop <;> rfl

theorem dropWhile_const_false {α : Type} (l : List α) : l.dropWhile (fun _ => false) = l := by
  cases l <;> simp

theorem takeWhile_const_true {α : Type} (l : List α) : l.takeWhile (fun _ => true) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- `range` yields exactly the entries of `toList` inside the bounds. -/
theorem rangeTree_spec (lc bc h : Nat) (hlc : 2 ≤ lc) (root : Node K V)
    (hwf : WF lc bc h true none none root) (start stop : Bound K) :
    rangeTree root start stop = rangeSorted start stop root.toList := by
  have hsorted := wf_toList_sorted lc bc h root true none none hwf
  have hmonoF := below_mono hsorted start
  have hmonoT := within_mono hsorted stop
  obtain ⟨hFs, hFn⟩ := resolveFront_spec lc bc h hlc root hwf start
  obtain ⟨hBs, hBn⟩ := resolveBack_spec lc bc h hlc root hwf stop
  have hmonoT' : (root.toList.drop (root.toList.countP fun e => !start.admitsFrom e)).Pairwise
      fun x y => stop.admitsTo y = true → stop.admitsTo x = true :=
    hmonoT.sublist (List.drop_sublist _ _)
  rw [rangeSorted, dropWhile_eq_drop_countP hmonoF, takeWhile_eq_take_countP hmonoT',
    countP_drop _ hmonoT]
  unfold rangeTree
  rcases hf : resolveFront root start with _ | f
  · rw [makeItems_eq_front_none hf, hFn hf]; simp
  · obtain ⟨hfF, hflt⟩ := hFs f hf
    rcases hb : resolveBack root stop with _ | b
    · rw [makeItems_eq_back_none hf hb, hBn hb]; simp
    · have hbB := hBs b hb
      have hfirst := List.getElem?_eq_getElem hflt
      rw [makeItems_eq hf hb hfirst, ← hfF, ← hbB]
      have hiff := getElem?_sat_iff hmonoT hfirst
      rw [← hbB] at hiff
      by_cases hr : stop.admitsTo root.toList[f] = true
      · rw [if_pos hr]
      · rw [if_neg hr]
        have : ¬ f < b := fun hlt => hr (hiff.mpr hlt)
        rw [Nat.sub_eq_zero_of_le (by omega)]; simp

/-- `items` yields all entries. -/
theorem itemsTree_spec (lc bc h : Nat) (hlc : 2 ≤ lc) (root : Node K V)
    (hwf : WF lc bc h true none none root) : itemsTree root = root.toList := by
  have := rangeTree_spec lc bc h hlc root hwf .unbounded .unbounded
  simp only [rangeTree] at this
  rw [itemsTree, this, rangeSorted]
  have h1 : (fun e : K × V => !(Bound.unbounded : Bound K).admitsFrom e) = fun _ => false := by
    funext e; rfl
  have h2 : (Bound.unbounded : Bound K).admitsTo (V := V) = fun _ => true := by
    funext e; rfl
  rw [h1, h2, dropWhile_const_false, takeWhile_const_true]

end ReadProofs

end BPlusTree
