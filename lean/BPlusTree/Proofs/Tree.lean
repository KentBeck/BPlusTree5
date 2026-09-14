import BPlusTree.Model.Tree
import BPlusTree.Proofs.Leaf
import BPlusTree.Proofs.Branch
import BPlusTree.Proofs.Spec

/-!
# The tree invariant, and insert preserves it

`WF` is what `check_invariants_detailed` checks plus uniform leaf depth:
keys strictly increasing in every node, every key inside the bounds its
ancestors' separators impose, fill between `cap / 2` and `cap` except at
the root, and every leaf at the same height. `insertRec_wf` shows
`insert_rec` keeps it, and in doing so discharges the branch theorems'
`SepFits` hypothesis from the split child's bounds.
-/

set_option linter.unusedSectionVars false

namespace BPlusTree

open Std List

/-! ## Chains of bounded children -/

section Chain

variable {K V : Type}

/-- `P lo hi c` for every child, with consecutive separators as bounds:
`children[0]` is bounded by `lo` and the first separator, each later child
by the separators around it, the last by the last separator and `hi`. -/
def Chain (P : Option K → Option K → Node K V → Prop) :
    Option K → Option K → Node K V → List (K × Node K V) → Prop
  | lo, hi, c, [] => P lo hi c
  | lo, hi, c, (s, c') :: rest => P lo (some s) c ∧ Chain P (some s) hi c' rest

/-- Lower bound of the child `lastChild` picks. -/
def lastBound (lo : Option K) : List (K × Node K V) → Option K
  | [] => lo
  | (s, _) :: rest => lastBound (some s) rest

/-- Upper bound of the child `lastChild` picks, given the entries after it. -/
def headBound (hi : Option K) : List (K × Node K V) → Option K
  | [] => hi
  | (s, _) :: _ => some s

theorem chain_split (P : Option K → Option K → Node K V → Prop) (A B : List (K × Node K V))
    (lo hi : Option K) (c : Node K V) (h : Chain P lo hi c (A ++ B)) :
    P (lastBound lo A) (headBound hi B) (lastChild c A) := by
  induction A generalizing lo c with
  | nil =>
    cases B with
    | nil => exact h
    | cons e rest => obtain ⟨s, c'⟩ := e; exact h.1
  | cons e rest ih =>
    obtain ⟨s, ch⟩ := e
    exact ih (some s) ch h.2

theorem chain_replace (P : Option K → Option K → Node K V → Prop) (A B : List (K × Node K V))
    (lo hi : Option K) (c c' : Node K V) (h : Chain P lo hi c (A ++ B))
    (hc' : P (lastBound lo A) (headBound hi B) c') :
    Chain P lo hi (replaceLast c A c').1 ((replaceLast c A c').2 ++ B) := by
  induction A generalizing lo c with
  | nil =>
    cases B with
    | nil => exact hc'
    | cons e rest => obtain ⟨s, c''⟩ := e; exact ⟨hc', h.2⟩
  | cons e rest ih =>
    obtain ⟨s, ch⟩ := e
    exact ⟨h.1, ih (some s) ch h.2 hc'⟩

theorem chain_insert (P : Option K → Option K → Node K V → Prop) (A B : List (K × Node K V))
    (lo hi : Option K) (c cl cr : Node K V) (sep : K) (h : Chain P lo hi c (A ++ B))
    (hl : P (lastBound lo A) (some sep) cl) (hr : P (some sep) (headBound hi B) cr) :
    Chain P lo hi (replaceLast c A cl).1 ((replaceLast c A cl).2 ++ (sep, cr) :: B) := by
  induction A generalizing lo c with
  | nil =>
    refine ⟨hl, ?_⟩
    cases B with
    | nil => exact hr
    | cons e rest => obtain ⟨s, c''⟩ := e; exact ⟨hr, h.2⟩
  | cons e rest ih =>
    obtain ⟨s, ch⟩ := e
    exact ⟨h.1, ih (some s) ch h.2 hl⟩

theorem chain_cut (P : Option K → Option K → Node K V → Prop) (L R : List (K × Node K V))
    (lo hi : Option K) (c rc : Node K V) (pk : K) (h : Chain P lo hi c (L ++ (pk, rc) :: R)) :
    Chain P lo (some pk) c L ∧ Chain P (some pk) hi rc R := by
  induction L generalizing lo c with
  | nil => exact h
  | cons e rest ih =>
    obtain ⟨s, ch⟩ := e
    obtain ⟨h1, h2⟩ := ih (some s) ch h.2
    exact ⟨⟨h.1, h1⟩, h2⟩

theorem replaceLast_keys (c : Node K V) (A : List (K × Node K V)) (c' : Node K V) :
    ((replaceLast c A c').2).map Prod.fst = A.map Prod.fst := by
  induction A generalizing c with
  | nil => rfl
  | cons e rest ih => obtain ⟨s, ch⟩ := e; simp [replaceLast, ih ch]

theorem replaceLast_length (c : Node K V) (A : List (K × Node K V)) (c' : Node K V) :
    ((replaceLast c A c').2).length = A.length := by
  have := congrArg List.length (replaceLast_keys c A c')
  simpa using this

theorem lastBound_mem (lo : Option K) (A : List (K × Node K V)) (s : K)
    (h : lastBound lo A = some s) : (A = [] ∧ lo = some s) ∨ ∃ c, (s, c) ∈ A := by
  induction A generalizing lo with
  | nil => exact Or.inl ⟨rfl, h⟩
  | cons e rest ih =>
    obtain ⟨a, ch⟩ := e
    rcases ih (some a) h with ⟨_, ha⟩ | ⟨c, hc⟩
    · cases ha; exact Or.inr ⟨ch, List.mem_cons_self⟩
    · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc⟩

theorem lastBound_some_of_ne_nil (lo : Option K) (A : List (K × Node K V)) (h : A ≠ []) :
    ∃ s, lastBound lo A = some s := by
  induction A generalizing lo with
  | nil => exact absurd rfl h
  | cons e rest ih =>
    obtain ⟨a, ch⟩ := e
    cases rest with
    | nil => exact ⟨a, rfl⟩
    | cons e' rest' => exact ih (some a) (by simp)

theorem headBound_mem (hi : Option K) (B : List (K × Node K V)) (s : K)
    (h : headBound hi B = some s) : (B = [] ∧ hi = some s) ∨ ∃ c, (s, c) ∈ B := by
  cases B with
  | nil => exact Or.inl ⟨rfl, h⟩
  | cons e rest =>
    obtain ⟨a, ch⟩ := e
    simp only [headBound, Option.some.injEq] at h
    subst h
    exact Or.inr ⟨ch, List.mem_cons_self⟩

end Chain

section Order

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K] [DecidableLT K]

theorem le_lastBound_of_sorted (A : List (K × Node K V)) (lo : Option K) (s : K)
    (hs : Sorted A) (h : lastBound lo A = some s) : ∀ x ∈ A, x.1 ≤ s := by
  induction A generalizing lo with
  | nil => intro x hx; simp at hx
  | cons e rest ih =>
    obtain ⟨a, ch⟩ := e
    simp only [Sorted, List.pairwise_cons] at hs
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rcases lastBound_mem (some a) rest s h with ⟨_, ha⟩ | ⟨c, hc⟩
      · cases ha; exact le_refl _
      · exact le_of_lt (hs.1 (s, c) hc)
    · exact ih (some a) hs.2 h x hx

theorem le_of_headBound (B : List (K × Node K V)) (hi : Option K) (s : K)
    (hs : Sorted B) (hne : B ≠ []) (h : headBound hi B = some s) : ∀ x ∈ B, s ≤ x.1 := by
  cases B with
  | nil => exact absurd rfl hne
  | cons e rest =>
    obtain ⟨a, ch⟩ := e
    simp only [headBound, Option.some.injEq] at h
    subst h
    simp only [Sorted, List.pairwise_cons] at hs
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_refl _
    · exact le_of_lt (hs.1 x hx)

/-- Key order is a property of the keys alone. -/
theorem sorted_of_keys_eq {X Y : Type} {l : List (K × X)} {l' : List (K × Y)}
    (h : l.map Prod.fst = l'.map Prod.fst) (hs : Sorted l) : Sorted l' := by
  have : (l'.map Prod.fst).Pairwise (· < ·) := by
    rw [← h]; exact List.pairwise_map.mpr hs
  exact List.pairwise_map.mp this

theorem forall_key_of_keys_eq {X Y : Type} {l : List (K × X)} {l' : List (K × Y)}
    (h : l.map Prod.fst = l'.map Prod.fst) (P : K → Prop) (hp : ∀ e ∈ l, P e.1) :
    ∀ e ∈ l', P e.1 := by
  intro e he
  have : e.1 ∈ l'.map Prod.fst := List.mem_map_of_mem he
  rw [← h] at this
  obtain ⟨a, ha, hae⟩ := List.mem_map.mp this
  rw [← hae]; exact hp a ha

theorem head_dropWhile_false {α : Type} {p : α → Bool} {l : List α} {x : α}
    (h : (l.dropWhile p).head? = some x) : p x = false := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases ha : p a = true
    · rw [List.dropWhile_cons_of_pos ha] at h; exact ih h
    · rw [List.dropWhile_cons_of_neg ha] at h
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h; simpa using ha

end Order

/-! ## The invariant -/

section WF

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K] [DecidableLT K]

/-- `lo ≤ k < hi`, with `none` meaning unbounded: the bounds `validate_node`
passes down. -/
def InBounds (lo hi : Option K) (k : K) : Prop :=
  (∀ l, lo = some l → l ≤ k) ∧ (∀ h, hi = some h → k < h)

/-- `lo < s < hi`: what a split hands its parent about the new separator. -/
def StrictlyInside (lo hi : Option K) (s : K) : Prop :=
  (∀ l, lo = some l → l < s) ∧ (∀ h, hi = some h → s < h)

/-- The tree invariant at height `h`. Leaves sit at height 0, so every leaf
of a well-formed tree is at the same depth. `isRoot` lifts the minimum
fill (a root leaf may even be empty; a root branch needs one entry). -/
def WF (lc bc : Nat) : Nat → Bool → Option K → Option K → Node K V → Prop
  | 0, isRoot, lo, hi, .leaf kvs =>
    Sorted kvs ∧ (∀ e ∈ kvs, InBounds lo hi e.1) ∧ kvs.length ≤ lc ∧
      (isRoot = true ∨ lc / 2 ≤ kvs.length)
  | 0, _, _, _, .branch _ _ => False
  | _ + 1, _, _, _, .leaf _ => False
  | h + 1, isRoot, lo, hi, .branch c0 entries =>
    Sorted entries ∧ (∀ e ∈ entries, InBounds lo hi e.1) ∧ entries.length ≤ bc ∧
      (if isRoot then 1 ≤ entries.length else bc / 2 ≤ entries.length) ∧
      Chain (WF lc bc h false) lo hi c0 entries

theorem inBounds_of_strictlyInside {lo hi : Option K} {s : K} (h : StrictlyInside lo hi s) :
    InBounds lo hi s :=
  ⟨fun l hl => le_of_lt (h.1 l hl), h.2⟩

/-- A separator strictly inside the chosen child's bounds is inside the
branch's bounds, because the child's bounds are the branch's bounds or
separators of the branch. -/
theorem inBounds_of_childBounds {lo hi : Option K} {A B : List (K × Node K V)} {sep : K}
    (hb : ∀ e ∈ A ++ B, InBounds lo hi e.1)
    (hstrict : StrictlyInside (lastBound lo A) (headBound hi B) sep) : InBounds lo hi sep := by
  constructor
  · intro l hl
    obtain ⟨s, hs⟩ : ∃ s, lastBound lo A = some s := by
      cases A with
      | nil => exact ⟨l, hl⟩
      | cons e rest => exact lastBound_some_of_ne_nil lo _ (by simp)
    have hlt := hstrict.1 s hs
    rcases lastBound_mem lo A s hs with ⟨_, hls⟩ | ⟨c, hc⟩
    · rw [hl] at hls; cases hls; exact le_of_lt hlt
    · exact le_of_lt (lt_of_le_of_lt ((hb (s, c) (List.mem_append_left _ hc)).1 l hl) hlt)
  · intro h hh
    obtain ⟨t, ht⟩ : ∃ t, headBound hi B = some t := by
      cases B with
      | nil => exact ⟨h, hh⟩
      | cons e rest => exact ⟨e.1, rfl⟩
    have hlt := hstrict.2 t ht
    rcases headBound_mem hi B t ht with ⟨_, hht⟩ | ⟨c, hc⟩
    · rw [hh] at hht; cases hht; exact hlt
    · exact lt_trans hlt ((hb (t, c) (List.mem_append_right _ hc)).2 h hh)

/-- A separator strictly inside the picked child's slot fits strictly
between the neighbouring entries: this is the branch theorems' `SepFits`,
for any prefix `A'` with the same keys as `A`. -/
theorem sepFits_of_strict {A A' B : List (K × Node K V)} {lo hi : Option K} {sep : K}
    (hs : Sorted (A ++ B)) (hkeys : A'.map Prod.fst = A.map Prod.fst)
    (hstrict : StrictlyInside (lastBound lo A) (headBound hi B) sep) :
    SepFits (A' ++ B) A.length sep := by
  have hlen : A'.length = A.length := by
    have := congrArg List.length hkeys; simpa using this
  have hsA : Sorted A := hs.sublist (List.sublist_append_left A B)
  have hsB : Sorted B := hs.sublist (List.sublist_append_right A B)
  constructor
  · intro e he
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at he
    have : e.1 ∈ A.map Prod.fst := by rw [← hkeys]; exact List.mem_map_of_mem he
    obtain ⟨a, ha, hae⟩ := List.mem_map.mp this
    obtain ⟨s, hs0⟩ := lastBound_some_of_ne_nil lo A (List.ne_nil_of_mem ha)
    rw [← hae]
    exact lt_of_le_of_lt (le_lastBound_of_sorted A lo s hsA hs0 a ha) (hstrict.1 s hs0)
  · intro e he
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
      List.nil_append] at he
    cases B with
    | nil => simp at he
    | cons b rest =>
      exact lt_of_lt_of_le (hstrict.2 b.1 rfl)
        (le_of_headBound (b :: rest) hi b.1 hsB (by simp) rfl e he)

/-- `insert_rec` preserves the invariant. A `NoSplit` result is well-formed
at the same height and bounds; a `Split` result gives two well-formed
non-root halves around a separator strictly inside the bounds, which is
exactly the `SepFits` the parent needs. -/
theorem insertRec_wf (lc bc : Nat) (hlc : 2 ≤ lc) (hbc : 2 ≤ bc) (k : K) (v : V) :
    ∀ (h : Nat) (n : Node K V) (isRoot : Bool) (lo hi : Option K),
      WF lc bc h isRoot lo hi n → InBounds lo hi k →
      match insertRec lc bc k v n with
      | .noSplit n' _ => WF lc bc h isRoot lo hi n'
      | .split l sep r =>
        WF lc bc h false lo (some sep) l ∧ WF lc bc h false (some sep) hi r ∧
          StrictlyInside lo hi sep := by
  intro h
  induction h with
  | zero =>
    intro n isRoot lo hi hwf hk
    cases n with
    | branch c0 entries => exact absurd hwf id
    | leaf kvs =>
      obtain ⟨hs, hb, hlen, hmin⟩ := hwf
      rw [insertRec]
      rcases hres : leafInsertOrSplit lc kvs k v with ⟨l, old⟩ | ⟨l, r, sep⟩
      · obtain ⟨hs', hlen', hsome, hnone, hmem⟩ := leafInsertOrSplit_noSplit hs hlen hres
        have hgrow : kvs.length ≤ l.length := by
          cases old with
          | none => have := hnone rfl; omega
          | some o => have := hsome o rfl; omega
        refine ⟨hs', ?_, hlen', ?_⟩
        · intro e he
          rcases hmem e he with rfl | he
          · exact hk
          · exact hb e he
        · rcases hmin with hr | hr
          · exact Or.inl hr
          · exact Or.inr (Nat.le_trans hr hgrow)
      · obtain ⟨hsl, hsr, hlmin, hlmax, hrmin, hrmax, hlsep, hrsep, _, heq⟩ :=
          leafInsertOrSplit_split hlc hs hlen hres
        have hmem : ∀ e ∈ l ++ r, InBounds lo hi e.1 := by
          intro e he
          rw [heq] at he
          rcases mem_insertAt he with rfl | he
          · exact hk
          · exact hb e he
        have hl2 : 1 ≤ lc / 2 := by omega
        refine ⟨⟨hsl, ?_, hlmax, Or.inr hlmin⟩, ⟨hsr, ?_, hrmax, Or.inr hrmin⟩, ?_, ?_⟩
        · intro e he
          exact ⟨(hmem e (List.mem_append_left _ he)).1,
            fun h hh => by cases hh; exact hlsep e he⟩
        · intro e he
          exact ⟨fun l hl => by cases hl; exact hrsep e he,
            (hmem e (List.mem_append_right _ he)).2⟩
        · intro l0 hl0
          obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil l (List.ne_nil_of_length_pos (by omega))
          exact lt_of_le_of_lt ((hmem e (List.mem_append_left _ he)).1 l0 hl0) (hlsep e he)
        · intro h0 hh0
          obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil r (List.ne_nil_of_length_pos (by omega))
          exact lt_of_le_of_lt (hrsep e he) ((hmem e (List.mem_append_right _ he)).2 h0 hh0)
  | succ h ih =>
    intro n isRoot lo hi hwf hk
    cases n with
    | leaf kvs => exact absurd hwf id
    | branch c0 entries =>
      obtain ⟨hs, hb, hlen, hmin, hchain⟩ := hwf
      rw [insertRec]
      simp only []
      -- Route: `A` holds the entries whose separator is `≤ k`.
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
      -- The chosen child is well-formed within its slot's bounds, and `k`
      -- lies in those bounds.
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
      have hrec := ih (lastChild c0 A) false _ _ hchild hkC
      have hkeysA := replaceLast_keys c0 A
      have hlenA := replaceLast_length c0 A
      rcases hres : insertRec lc bc k v (lastChild c0 A) with ⟨c', old⟩ | ⟨cl, sep, cr⟩ <;>
        simp only [hres] at hrec ⊢
      · -- The child absorbed the insert: same keys, one child replaced.
        have hkeys : (A ++ B).map Prod.fst =
            ((replaceLast c0 A c').2 ++ B).map Prod.fst := by
          simp [hkeysA c']
        refine ⟨sorted_of_keys_eq hkeys hs, forall_key_of_keys_eq hkeys _ hb, ?_, ?_,
          chain_replace _ A B lo hi c0 c' hchain hrec⟩
        · simp only [List.length_append, hlenA c'] at hlen ⊢; exact hlen
        · simp only [List.length_append, hlenA c'] at hmin ⊢; exact hmin
      · -- The child split: `SepFits` holds for the new separator, so the
        -- branch theorems apply.
        obtain ⟨hwl, hwr, hstrict⟩ := hrec
        have hkeys : (A ++ B).map Prod.fst =
            ((replaceLast c0 A cl).2 ++ B).map Prod.fst := by
          simp [hkeysA cl]
        have hs' : Sorted ((replaceLast c0 A cl).2 ++ B) := sorted_of_keys_eq hkeys hs
        have hb' : ∀ e ∈ (replaceLast c0 A cl).2 ++ B, InBounds lo hi e.1 :=
          forall_key_of_keys_eq hkeys _ hb
        have hfit : SepFits ((replaceLast c0 A cl).2 ++ B) A.length sep :=
          sepFits_of_strict hs (hkeysA cl) hstrict
        have hidx : A.length ≤ ((replaceLast c0 A cl).2 ++ B).length := by
          simp [hlenA cl]
        have hlen' : ((replaceLast c0 A cl).2 ++ B).length ≤ bc := by
          simp only [List.length_append, hlenA cl] at hlen ⊢; exact hlen
        have hins : insertAt ((replaceLast c0 A cl).2 ++ B) A.length (sep, cr) =
            (replaceLast c0 A cl).2 ++ (sep, cr) :: B := by
          rw [← hlenA cl, insertAt_append]
        have hchain' := chain_insert _ A B lo hi c0 cl cr sep hchain hwl hwr
        have hsep : InBounds lo hi sep := inBounds_of_childBounds hb hstrict
        have hb'' : ∀ e ∈ (replaceLast c0 A cl).2 ++ (sep, cr) :: B, InBounds lo hi e.1 := by
          intro e he
          simp only [List.mem_append, List.mem_cons] at he
          rcases he with he | rfl | he
          · exact hb' e (List.mem_append_left _ he)
          · exact hsep
          · exact hb' e (List.mem_append_right _ he)
        rcases hbr : branchApplySplit bc ⟨(replaceLast c0 A cl).1, (replaceLast c0 A cl).2 ++ B⟩
            A.length sep cr with ⟨b⟩ | ⟨l, pk, r⟩ <;> simp only []
        · -- This branch absorbed the child's split.
          obtain ⟨hc0, hent, hsb, hlenb, hcap⟩ := branchApplySplit_noSplit hs' hfit hidx hbr
          simp only at hc0 hent hsb hlenb hcap
          rw [hins] at hent
          rw [hc0, hent]
          refine ⟨by rw [← hent]; exact hsb, hb'', by rw [← hent]; exact hcap, ?_,
            hchain'⟩
          simp only [List.length_append, List.length_cons, hlenA cl] at hmin ⊢
          cases isRoot <;> simp at hmin ⊢ <;> omega
        · -- This branch split too.
          obtain ⟨hsl, hsr, hlmin, hlmax, hrmin, hrmax, hlpk, hrpk, hlc0, heq⟩ :=
            branchApplySplit_split (by omega) hs' hfit hidx hlen' hbr
          simp only at hsl hsr hlmin hlmax hrmin hrmax hlpk hrpk hlc0 heq
          rw [hins] at heq
          have hbins : ∀ e ∈ l.entries ++ (pk, r.c0) :: r.entries, InBounds lo hi e.1 := by
            rw [heq]; exact hb''
          rw [← heq] at hchain'
          rw [← hlc0] at hchain'
          obtain ⟨hcl, hcr⟩ := chain_cut _ _ _ lo hi _ _ pk hchain'
          have hb2 : 1 ≤ bc / 2 := by omega
          refine ⟨⟨hsl, ?_, hlmax, by simp; exact hlmin, hcl⟩,
            ⟨hsr, ?_, hrmax, by simp; exact hrmin, hcr⟩, ?_, ?_⟩
          · intro e he
            exact ⟨(hbins e (List.mem_append_left _ he)).1,
              fun h hh => by cases hh; exact hlpk e he⟩
          · intro e he
            exact ⟨fun l0 hl0 => by cases hl0; exact le_of_lt (hrpk e he),
              (hbins e (List.mem_append_right _ (List.mem_cons_of_mem _ he))).2⟩
          · intro l0 hl0
            obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil l.entries
              (List.ne_nil_of_length_pos (by omega))
            exact lt_of_le_of_lt ((hbins e (List.mem_append_left _ he)).1 l0 hl0) (hlpk e he)
          · intro h0 hh0
            exact (hbins (pk, r.c0) (List.mem_append_right _ List.mem_cons_self)).2 h0 hh0

/-- `insert` on a well-formed root yields a well-formed root, at the same
height or one higher (root growth). -/
theorem insertTree_wf (lc bc : Nat) (hlc : 2 ≤ lc) (hbc : 2 ≤ bc) (h : Nat) (root : Node K V)
    (k : K) (v : V) (hwf : WF lc bc h true none none root) :
    WF lc bc h true none none (insertTree lc bc root k v).1 ∨
      WF lc bc (h + 1) true none none (insertTree lc bc root k v).1 := by
  have hk : InBounds (K := K) none none k :=
    ⟨(fun _ hl => by cases hl), (fun _ hh => by cases hh)⟩
  have := insertRec_wf lc bc hlc hbc k v h root true none none hwf hk
  unfold insertTree
  rcases hres : insertRec lc bc k v root with ⟨n, old⟩ | ⟨l, sep, r⟩ <;> simp only [hres] at this ⊢
  · exact Or.inl this
  · obtain ⟨hwl, hwr, _⟩ := this
    right
    simp only [growRoot]
    refine ⟨by simp [Sorted], ?_, by simp; omega, by simp, hwl, hwr⟩
    intro e _
    exact ⟨(fun _ hl => by cases hl), (fun _ hh => by cases hh)⟩

/-! ## `toList` -/

theorem entriesToList_append (L R : List (K × Node K V)) :
    entriesToList (L ++ R) = entriesToList L ++ entriesToList R := by
  induction L with
  | nil => rfl
  | cons e rest ih => obtain ⟨s, c⟩ := e; simp [entriesToList, ih]

/-- A branch's entries, cut around the picked child. -/
theorem toList_branch_split (c : Node K V) (A B : List (K × Node K V)) :
    (Node.branch c (A ++ B)).toList =
      frontList c A ++ (lastChild c A).toList ++ entriesToList B := by
  induction A generalizing c with
  | nil => simp [Node.toList, frontList, lastChild]
  | cons e rest ih =>
    obtain ⟨s, ch⟩ := e
    have := ih ch
    simp only [Node.toList] at this
    simp only [List.cons_append, Node.toList, entriesToList, frontList, lastChild, this,
      List.append_assoc]

theorem frontList_replaceLast (c : Node K V) (A : List (K × Node K V)) (c' : Node K V) :
    frontList (replaceLast c A c').1 (replaceLast c A c').2 = frontList c A := by
  induction A generalizing c with
  | nil => rfl
  | cons e rest ih => obtain ⟨s, ch⟩ := e; simp [replaceLast, frontList, ih ch]

theorem lastChild_replaceLast (c : Node K V) (A : List (K × Node K V)) (c' : Node K V) :
    lastChild (replaceLast c A c').1 (replaceLast c A c').2 = c' := by
  induction A generalizing c with
  | nil => rfl
  | cons e rest ih => obtain ⟨s, ch⟩ := e; simp [replaceLast, lastChild, ih ch]

theorem chain_append_right (P : Option K → Option K → Node K V → Prop)
    (A B : List (K × Node K V)) (lo hi : Option K) (c : Node K V)
    (h : Chain P lo hi c (A ++ B)) : Chain P (lastBound lo A) hi (lastChild c A) B := by
  induction A generalizing lo c with
  | nil => exact h
  | cons e rest ih => obtain ⟨s, ch⟩ := e; exact ih (some s) ch h.2

/-- Every entry under a chain lies within the chain's outer bounds. -/
theorem chain_toList_bounds (P : Option K → Option K → Node K V → Prop)
    (hP : ∀ lo hi c, P lo hi c → ∀ e ∈ c.toList, InBounds lo hi e.1)
    (L : List (K × Node K V)) (lo hi : Option K) (c : Node K V) (hsort : Sorted L)
    (hb : ∀ e ∈ L, InBounds lo hi e.1) (hch : Chain P lo hi c L) :
    ∀ e ∈ c.toList ++ entriesToList L, InBounds lo hi e.1 := by
  induction L generalizing lo c with
  | nil => intro e he; simp only [entriesToList, List.append_nil] at he; exact hP lo hi c hch e he
  | cons x rest ih =>
    obtain ⟨s, ch⟩ := x
    simp only [Sorted, List.pairwise_cons] at hsort
    have hs : InBounds lo hi s := hb (s, ch) List.mem_cons_self
    intro e he
    simp only [entriesToList] at he
    rcases List.mem_append.mp he with he | he
    · have := hP lo (some s) c hch.1 e he
      exact ⟨this.1, fun h hh => lt_trans (this.2 s rfl) (hs.2 h hh)⟩
    · have hb' : ∀ x ∈ rest, InBounds (some s) hi x.1 := fun x hx =>
        ⟨fun l hl => by cases hl; exact le_of_lt (hsort.1 x hx),
          (hb x (List.mem_cons_of_mem _ hx)).2⟩
      have := ih (some s) ch hsort.2 hb' hch.2 e he
      exact ⟨fun l hl => le_trans (hs.1 l hl) (this.1 s rfl), this.2⟩

/-- Entries of a well-formed subtree lie within its bounds. -/
theorem wf_toList_bounds (lc bc : Nat) :
    ∀ (h : Nat) (n : Node K V) (isRoot : Bool) (lo hi : Option K),
      WF lc bc h isRoot lo hi n → ∀ e ∈ n.toList, InBounds lo hi e.1 := by
  intro h
  induction h with
  | zero =>
    intro n isRoot lo hi hwf
    cases n with
    | branch _ _ => exact absurd hwf id
    | leaf kvs => exact hwf.2.1
  | succ h ih =>
    intro n isRoot lo hi hwf
    cases n with
    | leaf _ => exact absurd hwf id
    | branch c0 entries =>
      obtain ⟨hsort, hb, _, _, hchain⟩ := hwf
      simp only [Node.toList]
      exact chain_toList_bounds _ (fun lo hi c hw => ih c false lo hi hw) entries lo hi c0 hsort
        hb hchain

/-- Keys before the picked child sort below `k`; keys after it sort above. -/
theorem front_lt_of_route {lc bc h : Nat} {A B : List (K × Node K V)} {lo hi : Option K}
    {c0 : Node K V} {k : K} (hs : Sorted (A ++ B)) (hb : ∀ e ∈ A ++ B, InBounds lo hi e.1)
    (hchain : Chain (WF lc bc h false) lo hi c0 (A ++ B))
    (hkC : InBounds (lastBound lo A) (headBound hi B) k) :
    (∀ e ∈ frontList c0 A, e.1 < k) ∧ (∀ e ∈ entriesToList B, k < e.1) := by
  have hP : ∀ (lo hi : Option K) (c : Node K V), WF lc bc h false lo hi c →
      ∀ e ∈ c.toList, InBounds lo hi e.1 :=
    fun lo hi c hw => wf_toList_bounds lc bc h c false lo hi hw
  constructor
  · -- Induct along `A`: each front child is bounded above by the next
    -- separator, which is at most the picked child's lower bound.
    suffices ∀ (A : List (K × Node K V)) (lo : Option K) (c0 : Node K V),
        Sorted (A ++ B) → (∀ e ∈ A ++ B, InBounds lo hi e.1) →
        Chain (WF lc bc h false) lo hi c0 (A ++ B) →
        ∀ e ∈ frontList c0 A, ∀ s, lastBound lo A = some s → e.1 < s by
      intro e he
      cases A with
      | nil => simp [frontList] at he
      | cons x rest =>
        obtain ⟨s, hs0⟩ := lastBound_some_of_ne_nil lo (x :: rest) (by simp)
        exact lt_of_lt_of_le (this _ lo c0 hs hb hchain e he s hs0) (hkC.1 s hs0)
    intro A
    induction A with
    | nil => intro lo c0 _ _ _ e he; simp [frontList] at he
    | cons x rest ih =>
      intro lo c0 hs hb hchain e he s hs0
      obtain ⟨s0, ch⟩ := x
      simp only [List.cons_append, Sorted, List.pairwise_cons] at hs
      simp only [frontList] at he
      have hs0' : lastBound (some s0) rest = some s := hs0
      have hs0_le : s0 ≤ s := by
        rcases lastBound_mem (some s0) rest s hs0' with ⟨_, hh⟩ | ⟨c, hc⟩
        · cases hh; exact le_refl _
        · exact le_of_lt (hs.1 (s, c) (List.mem_append_left _ hc))
      rcases List.mem_append.mp he with he | he
      · exact lt_of_lt_of_le ((hP lo (some s0) c0 hchain.1 e he).2 s0 rfl) hs0_le
      · exact ih (some s0) ch hs.2
          (fun x hx => ⟨fun l hl => by cases hl; exact le_of_lt (hs.1 x hx),
            (hb x (List.mem_cons_of_mem _ hx)).2⟩) hchain.2 e he s hs0'
  · intro e he
    have hch := chain_append_right _ A B lo hi c0 hchain
    cases B with
    | nil => simp [entriesToList] at he
    | cons x rest =>
      obtain ⟨t, ch⟩ := x
      have hsB : Sorted ((t, ch) :: rest) := hs.sublist (List.sublist_append_right A _)
      have hbB : ∀ e ∈ (t, ch) :: rest, InBounds lo hi e.1 :=
        fun e he => hb e (List.mem_append_right _ he)
      simp only [Sorted, List.pairwise_cons] at hsB
      simp only [entriesToList] at he
      have hkt : k < t := hkC.2 t rfl
      have := chain_toList_bounds _ hP rest (some t) hi ch hsB.2
        (fun x hx => ⟨fun l hl => by cases hl; exact le_of_lt (hsB.1 x hx),
          (hbB x (List.mem_cons_of_mem _ hx)).2⟩) hch.2 e he
      exact lt_of_lt_of_le hkt (this.1 t rfl)

/-- `insert_rec` refines `insertSorted` through `toList`, and the value it
returns is the one previously stored under the key, if any. -/
theorem insertRec_toList (lc bc : Nat) (hlc : 2 ≤ lc) (hbc : 2 ≤ bc) (k : K) (v : V) :
    ∀ (h : Nat) (n : Node K V) (isRoot : Bool) (lo hi : Option K),
      WF lc bc h isRoot lo hi n → InBounds lo hi k →
      match insertRec lc bc k v n with
      | .noSplit n' old =>
        n'.toList = insertSorted k v n.toList ∧
          (∀ o, old = some o → (k, o) ∈ n.toList) ∧
          (old = none → ∀ e ∈ n.toList, e.1 ≠ k)
      | .split l _ r =>
        l.toList ++ r.toList = insertSorted k v n.toList ∧ ∀ e ∈ n.toList, e.1 ≠ k := by
  intro h
  induction h with
  | zero =>
    intro n isRoot lo hi hwf hk
    cases n with
    | branch c0 entries => exact absurd hwf id
    | leaf kvs =>
      obtain ⟨hs, hb, hlen, hmin⟩ := hwf
      rw [insertRec]
      rcases hres : leafInsertOrSplit lc kvs k v with ⟨l, old⟩ | ⟨l, r, sep⟩
      · obtain ⟨_, _, hsome, hnone, _⟩ := leafInsertOrSplit_noSplit hs hlen hres
        refine ⟨leafInsertOrSplit_noSplit_eq hs hres, fun o ho => (hsome o ho).1,
          fun hn => (hnone hn).1⟩
      · obtain ⟨_, _, _, _, _, _, _, _, habs, _⟩ := leafInsertOrSplit_split hlc hs hlen hres
        exact ⟨leafInsertOrSplit_split_eq hlc hs hlen hres, habs⟩
  | succ h ih =>
    intro n isRoot lo hi hwf hk
    cases n with
    | leaf kvs => exact absurd hwf id
    | branch c0 entries =>
      have hwf' := hwf
      obtain ⟨hs, hb, hlen, hmin, hchain⟩ := hwf
      rw [insertRec]
      simp only []
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
      have hrec := ih (lastChild c0 A) false _ _ hchild hkC
      have hwrec := insertRec_wf lc bc hlc hbc k v h (lastChild c0 A) false _ _ hchild hkC
      have htl := toList_branch_split c0 A B
      -- The inserted list, in the shape every outcome reduces to.
      have hspec : insertSorted k v (Node.branch c0 (A ++ B)).toList =
          frontList c0 A ++ insertSorted k v (lastChild c0 A).toList ++ entriesToList B := by
        rw [htl, List.append_assoc, insertSorted_append_left _ _ hfront,
          insertSorted_append_right _ _ hsuffix, List.append_assoc]
      have habs_all : (∀ e ∈ (lastChild c0 A).toList, e.1 ≠ k) →
          ∀ e ∈ (Node.branch c0 (A ++ B)).toList, e.1 ≠ k := by
        intro hc e he
        rw [htl] at he
        simp only [List.mem_append] at he
        rcases he with (he | he) | he
        · exact ne_of_lt (hfront e he)
        · exact hc e he
        · exact (ne_of_lt (hsuffix e he)).symm
      rcases hres : insertRec lc bc k v (lastChild c0 A) with ⟨c', old⟩ | ⟨cl, sep, cr⟩ <;>
        simp only [hres] at hrec hwrec ⊢
      · obtain ⟨heq, hsome, hnone⟩ := hrec
        refine ⟨?_, ?_, fun hn => habs_all (hnone hn)⟩
        · rw [toList_branch_split, frontList_replaceLast, lastChild_replaceLast, heq, hspec]
        · intro o ho
          rw [htl]
          exact List.mem_append_left _ (List.mem_append_right _ (hsome o ho))
      · obtain ⟨heq, habs⟩ := hrec
        obtain ⟨hwl, hwr, hstrict⟩ := hwrec
        have hkeysA := replaceLast_keys c0 A
        have hlenA := replaceLast_length c0 A
        have hkeys : (A ++ B).map Prod.fst =
            ((replaceLast c0 A cl).2 ++ B).map Prod.fst := by
          simp [hkeysA cl]
        have hs' : Sorted ((replaceLast c0 A cl).2 ++ B) := sorted_of_keys_eq hkeys hs
        have hfit : SepFits ((replaceLast c0 A cl).2 ++ B) A.length sep :=
          sepFits_of_strict hs (hkeysA cl) hstrict
        have hidx : A.length ≤ ((replaceLast c0 A cl).2 ++ B).length := by
          simp [hlenA cl]
        have hlen' : ((replaceLast c0 A cl).2 ++ B).length ≤ bc := by
          simp only [List.length_append, hlenA cl] at hlen ⊢; exact hlen
        have hins : insertAt ((replaceLast c0 A cl).2 ++ B) A.length (sep, cr) =
            (replaceLast c0 A cl).2 ++ (sep, cr) :: B := by
          rw [← hlenA cl, insertAt_append]
        -- The whole entry list after absorbing the split, as a flat list.
        have hflat : (Node.branch (replaceLast c0 A cl).1
              ((replaceLast c0 A cl).2 ++ (sep, cr) :: B)).toList =
            insertSorted k v (Node.branch c0 (A ++ B)).toList := by
          rw [toList_branch_split, frontList_replaceLast, lastChild_replaceLast, hspec, ← heq]
          simp only [entriesToList, List.append_assoc]
        rcases hbr : branchApplySplit bc ⟨(replaceLast c0 A cl).1, (replaceLast c0 A cl).2 ++ B⟩
            A.length sep cr with ⟨b⟩ | ⟨l, pk, r⟩ <;> simp only []
        · obtain ⟨hc0, hent, _, _, _⟩ := branchApplySplit_noSplit hs' hfit hidx hbr
          simp only at hc0 hent
          rw [hins] at hent
          refine ⟨?_, (fun o ho => by cases ho), fun _ => habs_all habs⟩
          rw [hc0, hent, hflat]
        · obtain ⟨_, _, _, _, _, _, _, _, hlc0, hent⟩ :=
            branchApplySplit_split (by omega) hs' hfit hidx hlen' hbr
          simp only at hlc0 hent
          rw [hins] at hent
          refine ⟨?_, habs_all habs⟩
          rw [← hflat, ← hent, ← hlc0]
          simp only [Node.toList, entriesToList_append, entriesToList, List.append_assoc]

/-- `insert` refines `insertSorted` through `toList`, and returns the value
previously stored under the key, if any. -/
theorem insertTree_toList (lc bc : Nat) (hlc : 2 ≤ lc) (hbc : 2 ≤ bc) (h : Nat)
    (root : Node K V) (k : K) (v : V) (hwf : WF lc bc h true none none root) :
    (insertTree lc bc root k v).1.toList = insertSorted k v root.toList ∧
      (∀ o, (insertTree lc bc root k v).2 = some o → (k, o) ∈ root.toList) ∧
      ((insertTree lc bc root k v).2 = none → ∀ e ∈ root.toList, e.1 ≠ k) := by
  have hk : InBounds (K := K) none none k :=
    ⟨(fun _ hl => by cases hl), (fun _ hh => by cases hh)⟩
  have := insertRec_toList lc bc hlc hbc k v h root true none none hwf hk
  unfold insertTree
  rcases hres : insertRec lc bc k v root with ⟨n, old⟩ | ⟨l, sep, r⟩ <;> simp only [hres] at this ⊢
  · exact this
  · obtain ⟨heq, habs⟩ := this
    refine ⟨?_, (fun o ho => by cases ho), fun _ => habs⟩
    simp only [growRoot, Node.toList, entriesToList, List.append_nil]
    exact heq

end WF

end BPlusTree
