import BPlusTree.Model.Delete
import BPlusTree.Proofs.Tree
import BPlusTree.Proofs.Spec

/-!
# Proofs about the delete model

`delete.rs` indexes a branch's `keys[]` and `children[]`, so these proofs
work in that array view: `ChainA` is `Chain` over arrays, and the window
lemmas let a repair replace two adjacent children (or merge them into one)
inside a chain without touching the rest. `Shape` is `WF` without the
minimum-fill clause, the state a node is in between losing an entry and
its parent repairing it.
-/

set_option linter.unusedSectionVars false

namespace BPlusTree

open Std List

/-! ## The array view -/

section ArrayView

variable {K V : Type}

/-- `Chain` in the array view: `children` is one longer than `keys`. -/
def ChainA (P : Option K → Option K → Node K V → Prop) :
    Option K → Option K → List K → List (Node K V) → Prop
  | lo, hi, [], [c] => P lo hi c
  | lo, hi, s :: ks, c :: cs => P lo (some s) c ∧ ChainA P (some s) hi ks cs
  | _, _, _, _ => False

/-- Lower bound of the child after the keys `ks`. -/
def lastB (lo : Option K) : List K → Option K
  | [] => lo
  | s :: ks => lastB (some s) ks

/-- Upper bound of the child before the keys `ks`. -/
def headB (hi : Option K) : List K → Option K
  | [] => hi
  | s :: _ => some s

theorem lastB_append_singleton (lo : Option K) (ks : List K) (s : K) :
    lastB lo (ks ++ [s]) = some s := by
  induction ks generalizing lo with
  | nil => rfl
  | cons t ks ih => exact ih (some t)

theorem lastB_map_fst (lo : Option K) (A : List (K × Node K V)) :
    lastB lo (A.map Prod.fst) = lastBound lo A := by
  induction A generalizing lo with
  | nil => rfl
  | cons e rest ih => obtain ⟨s, c⟩ := e; exact ih (some s)

theorem headB_map_fst (hi : Option K) (B : List (K × Node K V)) :
    headB hi (B.map Prod.fst) = headBound hi B := by
  cases B with
  | nil => rfl
  | cons e rest => obtain ⟨s, c⟩ := e; rfl

theorem chain_iff_chainA (P : Option K → Option K → Node K V → Prop) (lo hi : Option K)
    (c0 : Node K V) (es : List (K × Node K V)) :
    Chain P lo hi c0 es ↔ ChainA P lo hi (es.map Prod.fst) (c0 :: es.map Prod.snd) := by
  induction es generalizing lo c0 with
  | nil => exact Iff.rfl
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    exact and_congr Iff.rfl (ih (some s) c)

theorem chainA_length (P : Option K → Option K → Node K V → Prop) :
    ∀ (ks : List K) (cs : List (Node K V)) (lo hi : Option K),
      ChainA P lo hi ks cs → cs.length = ks.length + 1
  | [], [c], _, _, _ => rfl
  | [], [], _, _, h => absurd h id
  | [], _ :: _ :: _, _, _, h => absurd h id
  | _ :: _, [], _, _, h => absurd h id
  | s :: ks, c :: cs, lo, hi, h => by
    simp only [ChainA] at h
    simp [chainA_length P ks cs (some s) hi h.2]

/-- The first child of a chain is bounded by `lo` and the first key. -/
theorem chainA_head (P : Option K → Option K → Node K V → Prop) (ks : List K)
    (c : Node K V) (cs : List (Node K V)) (lo hi : Option K)
    (h : ChainA P lo hi ks (c :: cs)) : P lo (headB hi ks) c := by
  cases ks with
  | nil => cases cs with
    | nil => exact h
    | cons _ _ => exact absurd h id
  | cons s ks => exact h.1

/-- Replace the first child (and the lower bound) of a chain. -/
theorem chainA_replaceHead (P : Option K → Option K → Node K V → Prop) (ks : List K)
    (c c' : Node K V) (cs : List (Node K V)) (lo lo' hi : Option K)
    (h : ChainA P lo hi ks (c :: cs)) (hc' : P lo' (headB hi ks) c') :
    ChainA P lo' hi ks (c' :: cs) := by
  cases ks with
  | nil => cases cs with
    | nil => exact hc'
    | cons _ _ => exact absurd h id
  | cons s ks => exact ⟨hc', h.2⟩

/-- A window of two adjacent children around separator `s`: read their
bounds, replace them (with a new separator), or merge them into one. -/
theorem chainA_window2 (P : Option K → Option K → Node K V → Prop) (hi : Option K)
    (s : K) (ks2 : List K) (a b : Node K V) (cs2 : List (Node K V)) :
    ∀ (ks1 : List K) (cs1 : List (Node K V)) (lo : Option K), ks1.length = cs1.length →
      ChainA P lo hi (ks1 ++ s :: ks2) (cs1 ++ a :: b :: cs2) →
      (P (lastB lo ks1) (some s) a ∧ P (some s) (headB hi ks2) b) ∧
      (∀ a' b' s', P (lastB lo ks1) (some s') a' → P (some s') (headB hi ks2) b' →
        ChainA P lo hi (ks1 ++ s' :: ks2) (cs1 ++ a' :: b' :: cs2)) ∧
      (∀ ab, P (lastB lo ks1) (headB hi ks2) ab →
        ChainA P lo hi (ks1 ++ ks2) (cs1 ++ ab :: cs2)) := by
  intro ks1
  induction ks1 with
  | nil =>
    intro cs1 lo hlen h
    cases cs1 with
    | cons _ _ => simp at hlen
    | nil =>
      simp only [List.nil_append] at h ⊢
      refine ⟨⟨h.1, chainA_head P ks2 b cs2 (some s) hi h.2⟩, ?_, ?_⟩
      · intro a' b' s' ha hb
        exact ⟨ha, chainA_replaceHead P ks2 b b' cs2 (some s) (some s') hi h.2 hb⟩
      · intro ab hab
        exact chainA_replaceHead P ks2 b ab cs2 (some s) lo hi h.2 hab
  | cons t ks1 ih =>
    intro cs1 lo hlen h
    cases cs1 with
    | nil => simp at hlen
    | cons c cs1 =>
      simp only [List.cons_append] at h ⊢
      obtain ⟨h1, h2⟩ := h
      obtain ⟨he, hrep, hmerge⟩ := ih cs1 (some t) (by simpa using hlen) h2
      exact ⟨he, fun a' b' s' ha hb => ⟨h1, hrep a' b' s' ha hb⟩,
        fun ab hab => ⟨h1, hmerge ab hab⟩⟩

/-- Extend a chain by one entry on the right. -/
theorem chain_snoc (P : Option K → Option K → Node K V → Prop) (L : List (K × Node K V)) :
    ∀ (lo : Option K) (c : Node K V) (s : K) (hi : Option K) (c' : Node K V),
      Chain P lo (some s) c L → P (some s) hi c' → Chain P lo hi c (L ++ [(s, c')])
  | lo, c, s, hi, c', h, hc' => by
    induction L generalizing lo c with
    | nil => exact ⟨h, hc'⟩
    | cons e rest ih => obtain ⟨t, ch⟩ := e; exact ⟨h.1, ih (some t) ch h.2⟩

/-- Join two chains around a separator (converse of `chain_cut`). -/
theorem chain_join (P : Option K → Option K → Node K V → Prop) (L R : List (K × Node K V))
    (lo hi : Option K) (c rc : Node K V) (s : K)
    (hL : Chain P lo (some s) c L) (hR : Chain P (some s) hi rc R) :
    Chain P lo hi c (L ++ (s, rc) :: R) := by
  induction L generalizing lo c with
  | nil => exact ⟨hL, hR⟩
  | cons e rest ih => obtain ⟨t, ch⟩ := e; exact ⟨hL.1, ih (some t) ch hL.2⟩

/-! ### Arrays of a branch -/

theorem zip_map_fst_snd (es : List (K × Node K V)) :
    (es.map Prod.fst).zip (es.map Prod.snd) = es := by
  induction es with
  | nil => rfl
  | cons e rest ih => obtain ⟨s, c⟩ := e; simp [ih]

theorem mkBranch_arrays (c0 : Node K V) (es : List (K × Node K V)) :
    mkBranch (es.map Prod.fst) (c0 :: es.map Prod.snd) = .branch c0 es := by
  simp [mkBranch, zip_map_fst_snd]

theorem map_fst_zip' (ks : List K) (rest : List (Node K V)) (h : ks.length = rest.length) :
    (ks.zip rest).map Prod.fst = ks :=
  List.map_fst_zip (by omega)

theorem map_snd_zip' (ks : List K) (rest : List (Node K V)) (h : ks.length = rest.length) :
    (ks.zip rest).map Prod.snd = rest :=
  List.map_snd_zip (by omega)

theorem entriesToList_zip (ks : List K) (rest : List (Node K V)) (h : ks.length = rest.length) :
    entriesToList (ks.zip rest) = (rest.map Node.toList).flatten := by
  induction ks generalizing rest with
  | nil => cases rest with
    | nil => rfl
    | cons _ _ => simp at h
  | cons s ks ih =>
    cases rest with
    | nil => simp at h
    | cons c rest => simp [entriesToList, ih rest (by simpa using h)]

theorem toList_branch_flatten (c0 : Node K V) (es : List (K × Node K V)) :
    (Node.branch c0 es).toList = ((c0 :: es.map Prod.snd).map Node.toList).flatten := by
  simp only [Node.toList, List.map_cons, List.flatten_cons]
  congr 1
  rw [← zip_map_fst_snd es, entriesToList_zip _ _ (by simp), map_snd_zip' _ _ (by simp)]

/-! ### Index arithmetic on a window -/

theorem getElem?_window_fst {α : Type} (cs1 : List α) (a : α) (cs2 : List α) :
    (cs1 ++ a :: cs2)[cs1.length]? = some a := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl

theorem getElem?_window_snd {α : Type} (cs1 : List α) (a b : α) (cs2 : List α) :
    (cs1 ++ a :: b :: cs2)[cs1.length + 1]? = some b := by
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; rfl

theorem set_window_fst {α : Type} (cs1 : List α) (a a' : α) (cs2 : List α) :
    (cs1 ++ a :: cs2).set cs1.length a' = cs1 ++ a' :: cs2 := by
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]; rfl

theorem set_window_snd {α : Type} (cs1 : List α) (a b b' : α) (cs2 : List α) :
    (cs1 ++ a :: b :: cs2).set (cs1.length + 1) b' = cs1 ++ a :: b' :: cs2 := by
  rw [List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left]; rfl

theorem eraseIdx_window_snd {α : Type} (cs1 : List α) (a b : α) (cs2 : List α) :
    (cs1 ++ a :: b :: cs2).eraseIdx (cs1.length + 1) = cs1 ++ a :: cs2 := by
  rw [List.eraseIdx_append_of_length_le (by omega), Nat.add_sub_cancel_left]; rfl

/-- The children before and after `lastChild`, as arrays. -/
theorem children_split (c0 : Node K V) (A B : List (K × Node K V)) :
    c0 :: (A ++ B).map Prod.snd =
      (c0 :: A.map Prod.snd).dropLast ++ lastChild c0 A :: B.map Prod.snd := by
  induction A generalizing c0 with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    simp only [List.cons_append, List.map_cons, lastChild]
    rw [ih c]
    cases rest <;> simp [List.dropLast]

theorem children_replaceLast (c0 c' : Node K V) (A B : List (K × Node K V)) :
    (replaceLast c0 A c').1 :: ((replaceLast c0 A c').2 ++ B).map Prod.snd =
      (c0 :: A.map Prod.snd).dropLast ++ c' :: B.map Prod.snd := by
  induction A generalizing c0 with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨s, c⟩ := e
    simp only [replaceLast, List.cons_append, List.map_cons]
    rw [ih c]
    cases rest <;> simp [List.dropLast]

theorem length_dropLast_cons_map (c0 : Node K V) (A : List (K × Node K V)) :
    (c0 :: A.map Prod.snd).dropLast.length = A.length := by
  simp

end ArrayView

/-! ## `Shape`: well-formed except for the minimum fill -/

section Shape

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K] [DecidableLT K]

/-- Minimum fill for a node at height `h`, as `WF` states it. `minBranchLen`
agrees with it for every capacity `with_caps` accepts. -/
def minOf (lc bc : Nat) : Nat → Nat
  | 0 => lc / 2
  | _ + 1 => bc / 2

theorem minBranchLen_eq {bc : Nat} (hbc : 3 ≤ bc) : minBranchLen bc = bc / 2 := by
  simp only [minBranchLen]
  split <;> omega

theorem minLeafLen_eq (lc : Nat) : minLeafLen lc = lc / 2 := rfl

/-- `WF` without the minimum-fill clause. -/
def Shape (lc bc : Nat) : Nat → Option K → Option K → Node K V → Prop
  | 0, lo, hi, .leaf kvs => Sorted kvs ∧ (∀ e ∈ kvs, InBounds lo hi e.1) ∧ kvs.length ≤ lc
  | 0, _, _, .branch _ _ => False
  | _ + 1, _, _, .leaf _ => False
  | h + 1, lo, hi, .branch c0 es =>
    Sorted es ∧ (∀ e ∈ es, InBounds lo hi e.1) ∧ es.length ≤ bc ∧
      Chain (WF lc bc h false) lo hi c0 es

theorem shape_of_wf {lc bc h : Nat} {isRoot : Bool} {lo hi : Option K} {n : Node K V}
    (hw : WF lc bc h isRoot lo hi n) : Shape lc bc h lo hi n := by
  cases h with
  | zero => cases n with
    | leaf kvs => exact ⟨hw.1, hw.2.1, hw.2.2.1⟩
    | branch _ _ => exact absurd hw id
  | succ h => cases n with
    | leaf _ => exact absurd hw id
    | branch c0 es => exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.2⟩

theorem wf_of_shape_nonroot {lc bc h : Nat} {lo hi : Option K} {n : Node K V}
    (hs : Shape lc bc h lo hi n) (hmin : minOf lc bc h ≤ n.len) : WF lc bc h false lo hi n := by
  cases h with
  | zero => cases n with
    | leaf kvs => exact ⟨hs.1, hs.2.1, hs.2.2, Or.inr hmin⟩
    | branch _ _ => exact absurd hs id
  | succ h => cases n with
    | leaf _ => exact absurd hs id
    | branch c0 es =>
      exact ⟨hs.1, hs.2.1, hs.2.2.1, hmin, hs.2.2.2⟩

theorem wf_of_shape_root {lc bc h : Nat} {lo hi : Option K} {n : Node K V}
    (hs : Shape lc bc h lo hi n) (hfill : ∀ c0 es, n = .branch c0 es → 1 ≤ es.length) :
    WF lc bc h true lo hi n := by
  cases h with
  | zero => cases n with
    | leaf kvs => exact ⟨hs.1, hs.2.1, hs.2.2, Or.inl rfl⟩
    | branch _ _ => exact absurd hs id
  | succ h => cases n with
    | leaf _ => exact absurd hs id
    | branch c0 es =>
      refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_, hs.2.2.2⟩
      simpa using hfill c0 es rfl

theorem wf_root_of_nonroot {lc bc h : Nat} {lo hi : Option K} {n : Node K V} (hbc : 2 ≤ bc)
    (hw : WF lc bc h false lo hi n) : WF lc bc h true lo hi n := by
  refine wf_of_shape_root (shape_of_wf hw) ?_
  intro c0 es hn
  subst hn
  cases h with
  | zero => exact absurd hw id
  | succ h =>
    have := hw.2.2.2.1
    simp only [Bool.false_eq_true, if_false] at this
    omega

theorem shape_len_le_leaf {lc bc : Nat} {lo hi : Option K} {n : Node K V}
    (hs : Shape lc bc 0 lo hi n) : n.len ≤ lc := by
  cases n with
  | leaf kvs => exact hs.2.2
  | branch _ _ => exact absurd hs id

theorem shape_len_le_branch {lc bc h : Nat} {lo hi : Option K} {n : Node K V}
    (hs : Shape lc bc (h + 1) lo hi n) : n.len ≤ bc := by
  cases n with
  | leaf _ => exact absurd hs id
  | branch _ _ => exact hs.2.2.1

/-- A well-formed node at height 0 is a leaf, at height `h + 1` a branch. -/
theorem shape_leaf {lc bc : Nat} {lo hi : Option K} {n : Node K V}
    (hs : Shape lc bc 0 lo hi n) : ∃ kvs, n = .leaf kvs := by
  cases n with
  | leaf kvs => exact ⟨kvs, rfl⟩
  | branch _ _ => exact absurd hs id

theorem shape_branch {lc bc h : Nat} {lo hi : Option K} {n : Node K V}
    (hs : Shape lc bc (h + 1) lo hi n) : ∃ c0 es, n = .branch c0 es := by
  cases n with
  | leaf _ => exact absurd hs id
  | branch c0 es => exact ⟨c0, es, rfl⟩

end Shape

/-! ## Keys of a branch around a window -/

section Keys

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K] [DecidableLT K]

theorem lastB_mem (lo : Option K) (ks : List K) (m : K) (h : lastB lo ks = some m) :
    (ks = [] ∧ lo = some m) ∨ m ∈ ks := by
  induction ks generalizing lo with
  | nil => exact Or.inl ⟨rfl, h⟩
  | cons t rest ih =>
    rcases ih (some t) h with ⟨_, ht⟩ | hm
    · cases ht; exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ hm)

theorem lastB_some_of_ne_nil (lo : Option K) (ks : List K) (h : ks ≠ []) :
    ∃ m, lastB lo ks = some m := by
  induction ks generalizing lo with
  | nil => exact absurd rfl h
  | cons t rest ih =>
    cases rest with
    | nil => exact ⟨t, rfl⟩
    | cons _ _ => exact ih (some t) (by simp)

theorem le_lastB_of_sorted (ks : List K) (lo : Option K) (m : K)
    (hs : ks.Pairwise (· < ·)) (h : lastB lo ks = some m) : ∀ t ∈ ks, t ≤ m := by
  induction ks generalizing lo with
  | nil => intro t ht; simp at ht
  | cons a rest ih =>
    simp only [List.pairwise_cons] at hs
    intro t ht
    rcases List.mem_cons.mp ht with hta | ht
    · rw [hta]
      rcases lastB_mem (some a) rest m h with ⟨_, ha⟩ | hm
      · cases ha; exact le_refl _
      · exact le_of_lt (hs.1 m hm)
    · exact ih (some a) hs.2 h t ht

/-- Keys before the window are below anything strictly above the window's
lower bound. -/
theorem forall_lt_of_lastB {ks1 : List K} {lo : Option K} {s' : K}
    (hs : ks1.Pairwise (· < ·)) (h : ∀ m, lastB lo ks1 = some m → m < s') :
    ∀ t ∈ ks1, t < s' := by
  intro t ht
  obtain ⟨m, hm⟩ := lastB_some_of_ne_nil lo ks1 (List.ne_nil_of_mem ht)
  exact lt_of_le_of_lt (le_lastB_of_sorted ks1 lo m hs hm t ht) (h m hm)

/-- Keys after the window are above anything strictly below the window's
upper bound. -/
theorem forall_gt_of_headB {ks2 : List K} {hi : Option K} {s' : K}
    (hs : ks2.Pairwise (· < ·)) (h : ∀ m, headB hi ks2 = some m → s' < m) :
    ∀ t ∈ ks2, s' < t := by
  cases ks2 with
  | nil => intro t ht; simp at ht
  | cons m rest =>
    simp only [List.pairwise_cons] at hs
    intro t ht
    rcases List.mem_cons.mp ht with htm | ht
    · rw [htm]; exact h m rfl
    · exact lt_trans (h m rfl) (hs.1 t ht)

/-- Replacing the window's separator by one strictly between its
neighbours keeps the keys sorted and in bounds. -/
theorem keys_window_set {ks1 ks2 : List K} {s s' : K} {lo hi : Option K}
    (hsk : (ks1 ++ s :: ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ s :: ks2, InBounds lo hi t)
    (hlo : ∀ m, lastB lo ks1 = some m → m < s') (hhi : ∀ m, headB hi ks2 = some m → s' < m) :
    (ks1 ++ s' :: ks2).Pairwise (· < ·) ∧ ∀ t ∈ ks1 ++ s' :: ks2, InBounds lo hi t := by
  simp only [List.pairwise_append, List.pairwise_cons] at hsk ⊢
  have h1 := forall_lt_of_lastB hsk.1 hlo
  have h2 := forall_gt_of_headB hsk.2.1.2 hhi
  refine ⟨⟨hsk.1, ⟨h2, hsk.2.1.2⟩, ?_⟩, ?_⟩
  · intro a ha b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h1 a ha
    · exact hsk.2.2 a ha b (List.mem_cons_of_mem _ hb)
  · intro t ht
    simp only [List.mem_append, List.mem_cons] at ht
    rcases ht with ht | hts | ht
    · exact hbk t (List.mem_append_left _ ht)
    · rw [hts]
      constructor
      · intro l hl
        obtain ⟨m, hm⟩ : ∃ m, lastB lo ks1 = some m := by
          cases ks1 with
          | nil => exact ⟨l, hl⟩
          | cons _ _ => exact lastB_some_of_ne_nil lo _ (by simp)
        rcases lastB_mem lo ks1 m hm with ⟨_, hlm⟩ | hmem
        · rw [hl] at hlm
          rw [Option.some.inj hlm]
          exact le_of_lt (hlo m hm)
        · exact le_of_lt (lt_of_le_of_lt ((hbk m (List.mem_append_left _ hmem)).1 l hl) (hlo m hm))
      · intro h hh
        cases ks2 with
        | nil => rw [hh] at hhi; exact hhi h rfl
        | cons m rest =>
          exact lt_trans (hhi m rfl) ((hbk m (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))).2 h hh)
    · exact hbk t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))

theorem keys_window_erase {ks1 ks2 : List K} {s : K} {lo hi : Option K}
    (hsk : (ks1 ++ s :: ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ s :: ks2, InBounds lo hi t) :
    (ks1 ++ ks2).Pairwise (· < ·) ∧ ∀ t ∈ ks1 ++ ks2, InBounds lo hi t := by
  refine ⟨hsk.sublist ((List.Sublist.refl ks1).append (List.sublist_cons_self s ks2)), ?_⟩
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hbk t (List.mem_append_left _ ht)
  · exact hbk t (List.mem_append_right _ (List.mem_cons_of_mem _ ht))

/-- The window separator sits strictly below the keys after it and `hi`. -/
theorem sep_lt_headB {ks1 ks2 : List K} {s : K} {lo hi : Option K}
    (hsk : (ks1 ++ s :: ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ s :: ks2, InBounds lo hi t) :
    ∀ m, headB hi ks2 = some m → s < m := by
  intro m hm
  cases ks2 with
  | nil => exact (hbk s (List.mem_append_right _ List.mem_cons_self)).2 m hm
  | cons t rest =>
    simp only [headB, Option.some.injEq] at hm
    subst hm
    simp only [List.pairwise_append, List.pairwise_cons] at hsk
    exact hsk.2.1.1 t List.mem_cons_self

/-! ### Nonempty subtrees give strict lower bounds -/

theorem wf_toList_ne_nil (lc bc : Nat) (hlc : 2 ≤ lc) :
    ∀ (h : Nat) (n : Node K V) (lo hi : Option K), WF lc bc h false lo hi n → n.toList ≠ [] := by
  intro h
  induction h with
  | zero =>
    intro n lo hi hw
    cases n with
    | branch _ _ => exact absurd hw id
    | leaf kvs =>
      rcases hw.2.2.2 with h | h
      · cases h
      · simp only [Node.toList]
        exact List.ne_nil_of_length_pos (by omega)
  | succ h ih =>
    intro n lo hi hw
    cases n with
    | leaf _ => exact absurd hw id
    | branch c0 es =>
      have hc0 : WF lc bc h false lo (headBound hi es) c0 := by
        have := chain_split _ [] es lo hi c0 hw.2.2.2.2
        simpa [lastBound, lastChild] using this
      simp only [Node.toList]
      intro hnil
      exact ih c0 _ _ hc0 (List.append_eq_nil_iff.mp hnil).1

/-- A well-formed non-root node between `some m` and `some t` forces `m < t`. -/
theorem wf_lo_lt_hi {lc bc h : Nat} (hlc : 2 ≤ lc) {m t : K} {n : Node K V}
    (hw : WF lc bc h false (some m) (some t) n) : m < t := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (wf_toList_ne_nil lc bc hlc h n _ _ hw)
  have := wf_toList_bounds lc bc h n false _ _ hw e he
  exact lt_of_le_of_lt (this.1 m rfl) (this.2 t rfl)

/-- A shaped node with at least one key has a nonempty `toList`, so it too
forces strict bounds. -/
theorem shape_lo_lt_hi {lc bc h : Nat} (hlc : 2 ≤ lc) {m t : K} {n : Node K V}
    (hs : Shape lc bc h (some m) (some t) n) (hlen : 1 ≤ n.len) : m < t := by
  cases h with
  | zero => cases n with
    | branch _ _ => exact absurd hs id
    | leaf kvs =>
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil kvs (List.ne_nil_of_length_pos hlen)
      have := hs.2.1 e he
      exact lt_of_le_of_lt (this.1 m rfl) (this.2 t rfl)
  | succ h => cases n with
    | leaf _ => exact absurd hs id
    | branch c0 es =>
      cases es with
      | nil => simp [Node.len] at hlen
      | cons e rest =>
        obtain ⟨s, c⟩ := e
        have h1 := hs.2.1 (s, c) List.mem_cons_self
        exact lt_trans (wf_lo_lt_hi hlc hs.2.2.2.1) (h1.2 t rfl)

/-- A branch's keys sit strictly above its lower bound. -/
theorem wf_branch_keys_gt_lo {lc bc h : Nat} (hlc : 2 ≤ lc) {m : K} {hi : Option K}
    {c0 : Node K V} {es : List (K × Node K V)}
    (hw : Shape lc bc (h + 1) (some m) hi (.branch c0 es)) : ∀ e ∈ es, m < e.1 := by
  intro e he
  cases es with
  | nil => simp at he
  | cons x rest =>
    obtain ⟨s, c⟩ := x
    have hms : m < s := wf_lo_lt_hi hlc hw.2.2.2.1
    rcases List.mem_cons.mp he with rfl | he
    · exact hms
    · have hs' := hw.1
      simp only [Sorted, List.pairwise_cons] at hs'
      exact lt_trans hms (hs'.1 e he)

end Keys

/-! ## Arrays back to `Shape` -/

section Arrays

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K] [DecidableLT K]

theorem shape_of_arrays {lc bc h : Nat} {lo hi : Option K} {ks : List K} {cs : List (Node K V)}
    (hlen : cs.length = ks.length + 1) (hsk : ks.Pairwise (· < ·))
    (hbk : ∀ t ∈ ks, InBounds lo hi t) (hcap : ks.length ≤ bc)
    (hch : ChainA (WF lc bc h false) lo hi ks cs) :
    Shape lc bc (h + 1) lo hi (mkBranch ks cs) := by
  cases cs with
  | nil => simp at hlen
  | cons c0 rest =>
    have hr : ks.length = rest.length := by simp at hlen; omega
    simp only [mkBranch, Shape]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have : ((ks.zip rest).map Prod.fst).Pairwise (· < ·) := by
        rw [map_fst_zip' ks rest hr]; exact hsk
      exact List.pairwise_map.mp this
    · intro e he
      exact hbk e.1 (List.of_mem_zip he).1
    · simp [List.length_zip]; omega
    · rw [chain_iff_chainA, map_fst_zip' ks rest hr, map_snd_zip' ks rest hr]
      exact hch

theorem len_mkBranch {ks : List K} {cs : List (Node K V)} (hlen : cs.length = ks.length + 1) :
    (mkBranch ks cs).len = ks.length := by
  cases cs with
  | nil => simp at hlen
  | cons c0 rest => simp at hlen; simp [mkBranch, Node.len, List.length_zip]; omega

theorem toList_mkBranch {ks : List K} {cs : List (Node K V)} (hlen : cs.length = ks.length + 1) :
    (mkBranch ks cs).toList = (cs.map Node.toList).flatten := by
  cases cs with
  | nil => simp at hlen
  | cons c0 rest =>
    simp only [mkBranch, Node.toList, List.map_cons, List.flatten_cons]
    rw [entriesToList_zip ks rest (by simp at hlen; omega)]

end Arrays

/-! ## Leaf repairs -/

section LeafRepairs

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K] [DecidableLT K]

/-- What every window repair establishes: the window replaced by `a'`,
`b'` around `s'`, both sides well-formed, keys still sorted and bounded,
contents preserved. -/
def Window2OK (lc bc h : Nat) (lo hi : Option K) (ks1 ks2 : List K)
    (cs1 cs2 : List (Node K V)) (a b : Node K V)
    (r : List K × List (Node K V)) : Prop :=
  ∃ a' b' s', r = (ks1 ++ s' :: ks2, cs1 ++ a' :: b' :: cs2) ∧
    WF lc bc h false (lastB lo ks1) (some s') a' ∧
    WF lc bc h false (some s') (headB hi ks2) b' ∧
    (ks1 ++ s' :: ks2).Pairwise (· < ·) ∧ (∀ t ∈ ks1 ++ s' :: ks2, InBounds lo hi t) ∧
    a'.toList ++ b'.toList = a.toList ++ b.toList

/-- The merge counterpart: one child in the window's place, one key fewer. -/
def Window1OK (lc bc h : Nat) (lo hi : Option K) (ks1 ks2 : List K)
    (cs1 cs2 : List (Node K V)) (a b : Node K V)
    (r : List K × List (Node K V)) : Prop :=
  ∃ ab, r = (ks1 ++ ks2, cs1 ++ ab :: cs2) ∧
    WF lc bc h false (lastB lo ks1) (headB hi ks2) ab ∧
    (ks1 ++ ks2).Pairwise (· < ·) ∧ (∀ t ∈ ks1 ++ ks2, InBounds lo hi t) ∧
    ab.toList = a.toList ++ b.toList

theorem leaf_wf_iff {lc bc : Nat} {lo hi : Option K} {L : Leaf K V} :
    WF lc bc 0 false lo hi (.leaf L) ↔
      Sorted L ∧ (∀ e ∈ L, InBounds lo hi e.1) ∧ L.length ≤ lc ∧ lc / 2 ≤ L.length := by
  simp [WF]

theorem leaf_shape_iff {lc bc : Nat} {lo hi : Option K} {L : Leaf K V} :
    Shape lc bc 0 lo hi (.leaf L) ↔
      Sorted L ∧ (∀ e ∈ L, InBounds lo hi e.1) ∧ L.length ≤ lc := Iff.rfl

/-- `rotate_leaf_right` on a window whose left leaf can spare an item. -/
theorem rotateLeafRight_window (lc bc : Nat) (hlc : 4 ≤ lc) (ks1 : List K) (s : K) (ks2 : List K)
    (cs1 : List (Node K V)) (L R : Leaf K V) (cs2 : List (Node K V)) (lo hi : Option K)
    (hlen : ks1.length = cs1.length)
    (hsk : (ks1 ++ s :: ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ s :: ks2, InBounds lo hi t)
    (hL : WF lc bc 0 false (lastB lo ks1) (some s) (.leaf L)) (hLlen : lc / 2 < L.length)
    (hR : Shape lc bc 0 (some s) (headB hi ks2) (.leaf R)) (hRlen : R.length < lc / 2)
    (hRdef : lc / 2 ≤ R.length + 1) :
    Window2OK lc bc 0 lo hi ks1 ks2 cs1 cs2 (.leaf L) (.leaf R)
      (rotateLeafRight (ks1 ++ s :: ks2) (cs1 ++ .leaf L :: .leaf R :: cs2) cs1.length) := by
  rw [leaf_wf_iff] at hL
  rw [leaf_shape_iff] at hR
  obtain ⟨hLs, hLb, hLcap, hLmin⟩ := hL
  obtain ⟨hRs, hRb, hRcap⟩ := hR
  rcases List.eq_nil_or_concat L with hnil | ⟨L', last, hL⟩
  · subst hnil; simp at hLlen
  rw [List.concat_eq_append] at hL
  subst hL
  have hgl : (L' ++ [last]).getLast? = some last := List.getLast?_eq_some_iff.mpr ⟨L', rfl⟩
  have hshi := sep_lt_headB hsk hbk
  simp only [Sorted, List.pairwise_append] at hLs
  have hLs' : ∀ a ∈ L', a.1 < last.1 := fun a ha => hLs.2.2 a ha last (List.mem_singleton.mpr rfl)
  -- Evaluate the model.
  simp only [rotateLeafRight, getElem?_window_fst, getElem?_window_snd, hgl,
    List.dropLast_concat]
  rw [set_window_fst, set_window_snd, ← hlen, set_window_fst]
  have hlast_s : last.1 < s := (hLb last (List.mem_append_right _ List.mem_cons_self)).2 s rfl
  have hkeys := keys_window_set (s' := last.1) hsk hbk (by
    intro m hm
    -- `L'` is nonempty (the donor holds more than `lc / 2 ≥ 2` items), and
    -- its first item is at least `m` and below `last`.
    rcases L' with _ | ⟨x, L''⟩
    · simp at hLlen; omega
    have := hLb x (List.mem_append_left _ List.mem_cons_self)
    exact lt_of_le_of_lt (this.1 m hm) (hLs' x List.mem_cons_self))
    (fun m hm => lt_trans hlast_s (hshi m hm))
  refine ⟨.leaf L', .leaf (last :: R), last.1, rfl, ?_, ?_, hkeys.1, hkeys.2, by simp [Node.toList]⟩
  · -- Left half: its own keys below `last`.
    rw [leaf_wf_iff]
    refine ⟨hLs.1, ?_, ?_, ?_⟩
    · intro e he
      exact ⟨(hLb e (List.mem_append_left _ he)).1, fun h hh => by cases hh; exact hLs' e he⟩
    · simp at hLcap ⊢; omega
    · simp at hLlen ⊢; omega
  · -- Right half: `last` goes in front; it is below `s` and `s` is at or
    -- below everything in `R`.
    rw [leaf_wf_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Sorted, List.pairwise_cons]
      exact ⟨fun r hr => lt_of_lt_of_le hlast_s ((hRb r hr).1 s rfl), hRs⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨fun l hl => by cases hl; exact le_refl _,
          fun h hh => lt_trans hlast_s (hshi h hh)⟩
      · exact ⟨fun l hl => by cases hl; exact le_of_lt (lt_of_lt_of_le hlast_s ((hRb e he).1 s rfl)),
          (hRb e he).2⟩
    · simp; omega
    · simp; omega

/-- `rotate_leaf_left` on a window whose right leaf can spare an item. -/
theorem rotateLeafLeft_window (lc bc : Nat) (hlc : 4 ≤ lc) (ks1 : List K) (s : K) (ks2 : List K)
    (cs1 : List (Node K V)) (L R : Leaf K V) (cs2 : List (Node K V)) (lo hi : Option K)
    (hlen : ks1.length = cs1.length)
    (hsk : (ks1 ++ s :: ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ s :: ks2, InBounds lo hi t)
    (hL : Shape lc bc 0 (lastB lo ks1) (some s) (.leaf L)) (hLlen : L.length < lc / 2)
    (hLdef : lc / 2 ≤ L.length + 1)
    (hR : WF lc bc 0 false (some s) (headB hi ks2) (.leaf R)) (hRlen : lc / 2 < R.length) :
    Window2OK lc bc 0 lo hi ks1 ks2 cs1 cs2 (.leaf L) (.leaf R)
      (rotateLeafLeft (ks1 ++ s :: ks2) (cs1 ++ .leaf L :: .leaf R :: cs2) cs1.length) := by
  rw [leaf_shape_iff] at hL
  rw [leaf_wf_iff] at hR
  obtain ⟨hLs, hLb, hLcap⟩ := hL
  obtain ⟨hRs, hRb, hRcap, hRmin⟩ := hR
  rcases R with _ | ⟨first, R'⟩
  · simp at hRlen
  rcases R' with _ | ⟨newFirst, R''⟩
  · simp at hRlen; omega
  have hlo_s : ∀ m, lastB lo ks1 = some m → m < s := by
    intro m hm
    rcases L with _ | ⟨x, L'⟩
    · simp at hLdef; omega
    have := hLb x List.mem_cons_self
    exact lt_of_le_of_lt (this.1 m hm) (this.2 s rfl)
  simp only [Sorted, List.pairwise_cons] at hRs
  have hs_first : s ≤ first.1 := (hRb first List.mem_cons_self).1 s rfl
  have hfirst_new : first.1 < newFirst.1 := hRs.1 newFirst List.mem_cons_self
  -- Evaluate the model.
  simp only [rotateLeafLeft, getElem?_window_fst, getElem?_window_snd]
  rw [set_window_fst, set_window_snd, ← hlen, set_window_fst]
  have hkeys := keys_window_set (s' := newFirst.1) hsk hbk
    (fun m hm => lt_trans (lt_of_lt_of_le (hlo_s m hm) hs_first) hfirst_new)
    (fun m hm => (hRb newFirst (List.mem_cons_of_mem _ List.mem_cons_self)).2 m hm)
  refine ⟨.leaf (L ++ [first]), .leaf (newFirst :: R''), newFirst.1, rfl, ?_, ?_, hkeys.1, hkeys.2,
    by simp [Node.toList]⟩
  · rw [leaf_wf_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Sorted, List.pairwise_append]
      refine ⟨hLs, List.Pairwise.cons (by simp) List.Pairwise.nil, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact lt_of_lt_of_le ((hLb a ha).2 s rfl) hs_first
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact ⟨(hLb e he).1, fun h hh => by
          cases hh; exact lt_trans (lt_of_lt_of_le ((hLb e he).2 s rfl) hs_first) hfirst_new⟩
      · rw [List.mem_singleton] at he
        subst he
        exact ⟨fun l hl => le_of_lt (lt_of_lt_of_le (hlo_s l hl) hs_first),
          fun h hh => by cases hh; exact hfirst_new⟩
    · simp; omega
    · simp; omega
  · rw [leaf_wf_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Sorted, List.pairwise_cons]
      exact ⟨hRs.2.1, hRs.2.2⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨fun l hl => by cases hl; exact le_refl _,
          (hRb e (List.mem_cons_of_mem _ List.mem_cons_self)).2⟩
      · exact ⟨fun l hl => by cases hl; exact le_of_lt (hRs.2.1 e he),
          (hRb e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))).2⟩
    · simp at hRcap ⊢; omega
    · simp at hRlen ⊢; omega

/-- `merge_leaf_pair` on a window whose two leaves fit in one. -/
theorem mergeLeafPair_window (lc bc : Nat) (ks1 : List K) (s : K) (ks2 : List K)
    (cs1 : List (Node K V)) (L R : Leaf K V) (cs2 : List (Node K V)) (lo hi : Option K)
    (hlen : ks1.length = cs1.length)
    (hsk : (ks1 ++ s :: ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ s :: ks2, InBounds lo hi t)
    (hL : Shape lc bc 0 (lastB lo ks1) (some s) (.leaf L))
    (hR : Shape lc bc 0 (some s) (headB hi ks2) (.leaf R))
    (hcap : L.length + R.length ≤ lc) (hmin : lc / 2 ≤ L.length + R.length) :
    Window1OK lc bc 0 lo hi ks1 ks2 cs1 cs2 (.leaf L) (.leaf R)
      (mergeLeafPair (ks1 ++ s :: ks2) (cs1 ++ .leaf L :: .leaf R :: cs2) cs1.length) := by
  rw [leaf_shape_iff] at hL hR
  obtain ⟨hLs, hLb, hLcap⟩ := hL
  obtain ⟨hRs, hRb, hRcap⟩ := hR
  simp only [mergeLeafPair, getElem?_window_fst, getElem?_window_snd]
  rw [set_window_fst, eraseIdx_window_snd, ← hlen, eraseIdx_window]
  have hkeys := keys_window_erase hsk hbk
  refine ⟨.leaf (L ++ R), rfl, ?_, hkeys.1, hkeys.2, by simp [Node.toList]⟩
  rw [leaf_wf_iff]
  refine ⟨?_, ?_, by simpa using hcap, by simpa using hmin⟩
  · simp only [Sorted, List.pairwise_append]
    exact ⟨hLs, hRs, fun a ha b hb => lt_of_lt_of_le ((hLb a ha).2 s rfl) ((hRb b hb).1 s rfl)⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact ⟨(hLb e he).1, fun h hh => lt_trans ((hLb e he).2 s rfl) (sep_lt_headB hsk hbk h hh)⟩
    · constructor
      · intro l hl
        rcases lastB_mem lo ks1 l hl with ⟨_, hlo⟩ | hmem
        · exact le_trans ((hbk s (List.mem_append_right _ List.mem_cons_self)).1 l hlo)
            ((hRb e he).1 s rfl)
        · simp only [List.pairwise_append, List.pairwise_cons] at hsk
          exact le_trans (le_of_lt (hsk.2.2 l hmem s List.mem_cons_self)) ((hRb e he).1 s rfl)
      · exact (hRb e he).2

end LeafRepairs

/-! ## Branch repairs -/

section BranchRepairs

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K] [DecidableLT K]

theorem branch_wf_iff {lc bc hc : Nat} {lo hi : Option K} {c0 : Node K V}
    {es : List (K × Node K V)} :
    WF lc bc (hc + 1) false lo hi (.branch c0 es) ↔
      Sorted es ∧ (∀ e ∈ es, InBounds lo hi e.1) ∧ es.length ≤ bc ∧ bc / 2 ≤ es.length ∧
        Chain (WF lc bc hc false) lo hi c0 es := by
  simp [WF]

theorem branch_shape_iff {lc bc hc : Nat} {lo hi : Option K} {c0 : Node K V}
    {es : List (K × Node K V)} :
    Shape lc bc (hc + 1) lo hi (.branch c0 es) ↔
      Sorted es ∧ (∀ e ∈ es, InBounds lo hi e.1) ∧ es.length ≤ bc ∧
        Chain (WF lc bc hc false) lo hi c0 es := Iff.rfl

/-- `rotate_branch_right` on a window whose left branch can spare an entry. -/
theorem rotateBranchRight_window (lc bc hc : Nat) (hlc : 2 ≤ lc) (_hbc : 4 ≤ bc)
    (ks1 : List K) (s : K) (ks2 : List K) (cs1 : List (Node K V))
    (lc0 : Node K V) (les : List (K × Node K V)) (rc0 : Node K V) (res : List (K × Node K V))
    (cs2 : List (Node K V)) (lo hi : Option K)
    (hlen : ks1.length = cs1.length)
    (hsk : (ks1 ++ s :: ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ s :: ks2, InBounds lo hi t)
    (hL : WF lc bc (hc + 1) false (lastB lo ks1) (some s) (.branch lc0 les))
    (hLlen : bc / 2 < les.length)
    (hR : Shape lc bc (hc + 1) (some s) (headB hi ks2) (.branch rc0 res))
    (hRlen : res.length < bc / 2) (hRdef : bc / 2 ≤ res.length + 1) :
    Window2OK lc bc (hc + 1) lo hi ks1 ks2 cs1 cs2 (.branch lc0 les) (.branch rc0 res)
      (rotateBranchRight (ks1 ++ s :: ks2)
        (cs1 ++ .branch lc0 les :: .branch rc0 res :: cs2) cs1.length) := by
  have hLshape := shape_of_wf hL
  -- The right child's keys sit strictly above `s`.
  have hres_gt : ∀ e ∈ res, s < e.1 := wf_branch_keys_gt_lo hlc hR
  rw [branch_wf_iff] at hL
  rw [branch_shape_iff] at hR
  obtain ⟨hLs, hLb, hLcap, hLmin, hLch⟩ := hL
  obtain ⟨hRs, hRb, hRcap, hRch⟩ := hR
  rcases List.eq_nil_or_concat les with hnil | ⟨les', pm, hles⟩
  · subst hnil; simp at hLlen
  rw [List.concat_eq_append] at hles
  subst hles
  obtain ⟨promoted, movedChild⟩ := pm
  have hgl : (les' ++ [(promoted, movedChild)]).getLast? = some (promoted, movedChild) :=
    List.getLast?_eq_some_iff.mpr ⟨les', rfl⟩
  have hk : (ks1 ++ s :: ks2)[cs1.length]? = some s := by
    rw [← hlen]; exact getElem?_window_fst ks1 s ks2
  have hshi := sep_lt_headB hsk hbk
  -- Facts about the left child.
  have hLs' := hLs
  simp only [Sorted, List.pairwise_append] at hLs'
  have hles_lt : ∀ a ∈ les', a.1 < promoted :=
    fun a ha => hLs'.2.2 a ha (promoted, movedChild) (List.mem_singleton.mpr rfl)
  have hprom := hLb (promoted, movedChild) (List.mem_append_right _ List.mem_cons_self)
  have hprom_s : promoted < s := hprom.2 s rfl
  obtain ⟨hchL, hchM⟩ := chain_cut _ les' [] _ _ lc0 movedChild promoted hLch
  -- Evaluate the model.
  simp only [rotateBranchRight, getElem?_window_fst, getElem?_window_snd, hk, hgl,
    List.dropLast_concat]
  rw [set_window_fst, set_window_snd, ← hlen, set_window_fst]
  have hkeys := keys_window_set (s' := promoted) hsk hbk
    (by
      intro m hm
      rw [hm] at hLshape
      exact wf_branch_keys_gt_lo hlc hLshape (promoted, movedChild)
        (List.mem_append_right _ List.mem_cons_self))
    (fun m hm => lt_trans hprom_s (hshi m hm))
  refine ⟨.branch lc0 les', .branch movedChild ((s, rc0) :: res), promoted, rfl, ?_, ?_,
    hkeys.1, hkeys.2, ?_⟩
  · rw [branch_wf_iff]
    refine ⟨hLs'.1, ?_, ?_, ?_, hchL⟩
    · intro e he
      exact ⟨(hLb e (List.mem_append_left _ he)).1, fun h hh => by cases hh; exact hles_lt e he⟩
    · simp at hLcap ⊢; omega
    · simp at hLlen ⊢; omega
  · rw [branch_wf_iff]
    refine ⟨?_, ?_, ?_, ?_, hchM, hRch⟩
    · simp only [Sorted, List.pairwise_cons]
      exact ⟨fun e he => hres_gt e he, hRs⟩
    · intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨fun l hl => by cases hl; exact le_of_lt hprom_s, fun h hh => hshi h hh⟩
      · exact ⟨fun l hl => by cases hl; exact le_of_lt (lt_trans hprom_s (hres_gt e he)),
          (hRb e he).2⟩
    · simp; omega
    · simp; omega
  · simp [Node.toList, entriesToList_append, entriesToList]

/-- `rotate_branch_left` on a window whose right branch can spare an entry. -/
theorem rotateBranchLeft_window (lc bc hc : Nat) (hlc : 2 ≤ lc) (hbc : 4 ≤ bc)
    (ks1 : List K) (s : K) (ks2 : List K) (cs1 : List (Node K V))
    (lc0 : Node K V) (les : List (K × Node K V)) (rc0 : Node K V) (res : List (K × Node K V))
    (cs2 : List (Node K V)) (lo hi : Option K)
    (hlen : ks1.length = cs1.length)
    (hsk : (ks1 ++ s :: ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ s :: ks2, InBounds lo hi t)
    (hL : Shape lc bc (hc + 1) (lastB lo ks1) (some s) (.branch lc0 les))
    (hLlen : les.length < bc / 2) (hLdef : bc / 2 ≤ les.length + 1)
    (hR : WF lc bc (hc + 1) false (some s) (headB hi ks2) (.branch rc0 res))
    (hRlen : bc / 2 < res.length) :
    Window2OK lc bc (hc + 1) lo hi ks1 ks2 cs1 cs2 (.branch lc0 les) (.branch rc0 res)
      (rotateBranchLeft (ks1 ++ s :: ks2)
        (cs1 ++ .branch lc0 les :: .branch rc0 res :: cs2) cs1.length) := by
  have hRshape := shape_of_wf hR
  rw [branch_shape_iff] at hL
  rw [branch_wf_iff] at hR
  obtain ⟨hLs, hLb, hLcap, hLch⟩ := hL
  obtain ⟨hRs, hRb, hRcap, hRmin, hRch⟩ := hR
  rcases res with _ | ⟨⟨promoted, rch1⟩, rest⟩
  · simp at hRlen
  have hk : (ks1 ++ s :: ks2)[cs1.length]? = some s := by
    rw [← hlen]; exact getElem?_window_fst ks1 s ks2
  have hlo_s : ∀ m, lastB lo ks1 = some m → m < s := by
    intro m hm
    have hL' : Shape lc bc (hc + 1) (some m) (some s) (.branch lc0 les) := by
      rw [← hm]; exact ⟨hLs, hLb, hLcap, hLch⟩
    exact shape_lo_lt_hi hlc hL' (by simp [Node.len]; omega)
  have hs_prom : s < promoted := wf_branch_keys_gt_lo hlc hRshape (promoted, rch1) List.mem_cons_self
  have hRs' := hRs
  simp only [Sorted, List.pairwise_cons] at hRs'
  have hprom_hi := (hRb (promoted, rch1) List.mem_cons_self).2
  -- Evaluate the model.
  simp only [rotateBranchLeft, getElem?_window_fst, getElem?_window_snd, hk]
  rw [set_window_fst, set_window_snd, ← hlen, set_window_fst]
  have hkeys := keys_window_set (s' := promoted) hsk hbk
    (fun m hm => lt_trans (hlo_s m hm) hs_prom) hprom_hi
  refine ⟨.branch lc0 (les ++ [(s, rc0)]), .branch rch1 rest, promoted, rfl, ?_, ?_,
    hkeys.1, hkeys.2, ?_⟩
  · rw [branch_wf_iff]
    refine ⟨?_, ?_, ?_, ?_, chain_snoc _ les _ lc0 s _ rc0 hLch hRch.1⟩
    · simp only [Sorted, List.pairwise_append]
      refine ⟨hLs, List.Pairwise.cons (by simp) List.Pairwise.nil, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact (hLb a ha).2 s rfl
    · intro e he
      rcases List.mem_append.mp he with he | he
      · exact ⟨(hLb e he).1, fun h hh => by cases hh; exact lt_trans ((hLb e he).2 s rfl) hs_prom⟩
      · rw [List.mem_singleton] at he
        subst he
        exact ⟨fun l hl => le_of_lt (hlo_s l hl), fun h hh => by cases hh; exact hs_prom⟩
    · simp; omega
    · simp; omega
  · rw [branch_wf_iff]
    refine ⟨hRs'.2, ?_, ?_, ?_, hRch.2⟩
    · intro e he
      exact ⟨fun l hl => by cases hl; exact le_of_lt (hRs'.1 e he),
        (hRb e (List.mem_cons_of_mem _ he)).2⟩
    · simp at hRcap ⊢; omega
    · simp at hRlen ⊢; omega
  · simp [Node.toList, entriesToList_append, entriesToList]

/-- `merge_branch_pair` on a window whose two branches fit in one. -/
theorem mergeBranchPair_window (lc bc hc : Nat) (hlc : 2 ≤ lc)
    (ks1 : List K) (s : K) (ks2 : List K) (cs1 : List (Node K V))
    (lc0 : Node K V) (les : List (K × Node K V)) (rc0 : Node K V) (res : List (K × Node K V))
    (cs2 : List (Node K V)) (lo hi : Option K)
    (hlen : ks1.length = cs1.length)
    (hsk : (ks1 ++ s :: ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ s :: ks2, InBounds lo hi t)
    (hL : Shape lc bc (hc + 1) (lastB lo ks1) (some s) (.branch lc0 les)) (hLpos : 1 ≤ les.length)
    (hR : Shape lc bc (hc + 1) (some s) (headB hi ks2) (.branch rc0 res))
    (hcap : les.length + 1 + res.length ≤ bc) (hmin : bc / 2 ≤ les.length + 1 + res.length) :
    Window1OK lc bc (hc + 1) lo hi ks1 ks2 cs1 cs2 (.branch lc0 les) (.branch rc0 res)
      (mergeBranchPair (ks1 ++ s :: ks2)
        (cs1 ++ .branch lc0 les :: .branch rc0 res :: cs2) cs1.length) := by
  have hres_gt : ∀ e ∈ res, s < e.1 := wf_branch_keys_gt_lo hlc hR
  rw [branch_shape_iff] at hL hR
  obtain ⟨hLs, hLb, hLcap, hLch⟩ := hL
  obtain ⟨hRs, hRb, hRcap, hRch⟩ := hR
  have hk : (ks1 ++ s :: ks2)[cs1.length]? = some s := by
    rw [← hlen]; exact getElem?_window_fst ks1 s ks2
  have hshi := sep_lt_headB hsk hbk
  have hlo_s : ∀ m, lastB lo ks1 = some m → m < s := by
    intro m hm
    have hL' : Shape lc bc (hc + 1) (some m) (some s) (.branch lc0 les) := by
      rw [← hm]; exact ⟨hLs, hLb, hLcap, hLch⟩
    exact shape_lo_lt_hi hlc hL' (by simp [Node.len]; omega)
  simp only [mergeBranchPair, getElem?_window_fst, getElem?_window_snd, hk]
  rw [set_window_fst, eraseIdx_window_snd, ← hlen, eraseIdx_window]
  have hkeys := keys_window_erase hsk hbk
  refine ⟨.branch lc0 (les ++ (s, rc0) :: res), rfl, ?_, hkeys.1, hkeys.2, ?_⟩
  · rw [branch_wf_iff]
    refine ⟨?_, ?_, ?_, ?_, chain_join _ les res _ _ lc0 rc0 s hLch hRch⟩
    · simp only [Sorted, List.pairwise_append, List.pairwise_cons]
      refine ⟨hLs, ⟨fun e he => hres_gt e he, hRs⟩, ?_⟩
      intro a ha b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact (hLb a ha).2 s rfl
      · exact lt_trans ((hLb a ha).2 s rfl) (hres_gt b hb)
    · intro e he
      simp only [List.mem_append, List.mem_cons] at he
      rcases he with he | rfl | he
      · exact ⟨(hLb e he).1, fun h hh => lt_trans ((hLb e he).2 s rfl) (hshi h hh)⟩
      · exact ⟨fun l hl => le_of_lt (hlo_s l hl), fun h hh => hshi h hh⟩
      · exact ⟨fun l hl => le_of_lt (lt_trans (hlo_s l hl) (hres_gt e he)), (hRb e he).2⟩
    · simp; omega
    · simp; omega
  · simp [Node.toList, entriesToList_append, entriesToList]

end BranchRepairs

/-! ## `fix_branch_child` -/

section Fix

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K] [DecidableLT K]

/-- Which repair `plan_rebalance` picks, and what it knew when it did. -/
theorem planRebalance_spec (children : List (Node K V)) (idx len min : Nat) :
    match planRebalance children idx len min with
    | .borrowFromLeft => 0 < idx ∧ min < childLen children (idx - 1)
    | .borrowFromRight => idx < len ∧ min < childLen children (idx + 1)
    | .mergeWithLeft => 0 < idx ∧ childLen children (idx - 1) ≤ min ∧
        (idx < len → childLen children (idx + 1) ≤ min)
    | .mergeWithRight => idx = 0 ∧ (idx < len → childLen children (idx + 1) ≤ min) := by
  split <;> rename_i heq <;> unfold planRebalance at heq <;>
    simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt] at heq
  · split at heq
    · rename_i h; exact h
    · split at heq
      · cases heq
      · split at heq <;> cases heq
  · split at heq
    · cases heq
    · split at heq
      · rename_i h; exact h
      · split at heq <;> cases heq
  · split at heq
    · cases heq
    · rename_i h1
      split at heq
      · cases heq
      · rename_i h2
        split at heq
        · rename_i h3
          refine ⟨h3, Nat.le_of_not_lt (fun hc => h1 ⟨h3, hc⟩), ?_⟩
          intro hr; exact Nat.le_of_not_lt (fun hc => h2 ⟨hr, hc⟩)
        · cases heq
  · split at heq
    · cases heq
    · rename_i h1
      split at heq
      · cases heq
      · rename_i h2
        split at heq
        · cases heq
        · rename_i h3
          refine ⟨by omega, ?_⟩
          intro hr; exact Nat.le_of_not_lt (fun hc => h2 ⟨hr, hc⟩)

theorem childLen_window_fst (cs1 : List (Node K V)) (a : Node K V) (cs2 : List (Node K V)) :
    childLen (cs1 ++ a :: cs2) cs1.length = a.len := by
  simp [childLen]

theorem childLen_window_snd (cs1 : List (Node K V)) (a b : Node K V) (cs2 : List (Node K V)) :
    childLen (cs1 ++ a :: b :: cs2) (cs1.length + 1) = b.len := by
  simp [childLen]

theorem flatten_window2 (cs1 cs2 : List (Node K V)) {a b a' b' : Node K V}
    (h : a'.toList ++ b'.toList = a.toList ++ b.toList) :
    ((cs1 ++ a' :: b' :: cs2).map Node.toList).flatten =
      ((cs1 ++ a :: b :: cs2).map Node.toList).flatten := by
  simp only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]
  rw [← List.append_assoc a'.toList, h, List.append_assoc]

theorem flatten_window1 (cs1 cs2 : List (Node K V)) {a b ab : Node K V}
    (h : ab.toList = a.toList ++ b.toList) :
    ((cs1 ++ ab :: cs2).map Node.toList).flatten =
      ((cs1 ++ a :: b :: cs2).map Node.toList).flatten := by
  simp only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]
  rw [h, List.append_assoc]

theorem exists_concat_of_length_pos {α : Type} {l : List α} (h : 0 < l.length) :
    ∃ l' x, l = l' ++ [x] := by
  rcases List.eq_nil_or_concat l with rfl | ⟨l', x, hl⟩
  · simp at h
  · exact ⟨l', x, by rw [hl, List.concat_eq_append]⟩

/-- The conclusion shared by every repair case of `fixBranchChild_spec`. -/
def FixOK (lc bc h : Nat) (isRoot : Bool) (lo hi : Option K) (ks : List K)
    (orig node' : Node K V) (under : Bool) : Prop :=
  Shape lc bc (h + 1) lo hi node' ∧ ks.length ≤ node'.len + 1 ∧ node'.len ≤ ks.length ∧
    (isRoot = false → under = decide (node'.len < bc / 2)) ∧ node'.toList = orig.toList

/-- A borrow leaves the key count unchanged. -/
theorem fixOK_of_window2 {lc bc h : Nat} {isRoot : Bool} {lo hi : Option K}
    {ks1 ks2 : List K} {cs1 cs2 : List (Node K V)} {a b a' b' : Node K V} {s s' : K}
    {orig : Node K V}
    (hlen : ks1.length = cs1.length) (hcs2 : cs2.length = ks2.length)
    (hcap : (ks1 ++ s :: ks2).length ≤ bc)
    (hfill : if isRoot then 1 ≤ (ks1 ++ s :: ks2).length else bc / 2 ≤ (ks1 ++ s :: ks2).length)
    (hch : ChainA (WF lc bc h false) lo hi (ks1 ++ s' :: ks2) (cs1 ++ a' :: b' :: cs2))
    (hks : (ks1 ++ s' :: ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ s' :: ks2, InBounds lo hi t)
    (htl : a'.toList ++ b'.toList = a.toList ++ b.toList)
    (horig : orig.toList = ((cs1 ++ a :: b :: cs2).map Node.toList).flatten) :
    FixOK lc bc h isRoot lo hi (ks1 ++ s :: ks2) orig
      (mkBranch (ks1 ++ s' :: ks2) (cs1 ++ a' :: b' :: cs2)) false := by
  have hlenr : (cs1 ++ a' :: b' :: cs2).length = (ks1 ++ s' :: ks2).length + 1 := by simp; omega
  refine ⟨shape_of_arrays hlenr hks hbk (by simp only [List.length_append, List.length_cons] at hcap ⊢; omega) hch, ?_, ?_, ?_, ?_⟩
  · rw [len_mkBranch hlenr]; simp
  · rw [len_mkBranch hlenr]; simp
  · intro hroot; subst hroot; rw [len_mkBranch hlenr]
    simp only [Bool.false_eq_true, if_false] at hfill
    simp at hfill ⊢; omega
  · rw [toList_mkBranch hlenr, horig, flatten_window2 cs1 cs2 htl]

/-- A merge drops one key. -/
theorem fixOK_of_window1 {lc bc h : Nat} {isRoot : Bool} {lo hi : Option K}
    {ks1 ks2 : List K} {cs1 cs2 : List (Node K V)} {a b ab : Node K V} {s : K}
    {orig : Node K V}
    (hlen : ks1.length = cs1.length) (hcs2 : cs2.length = ks2.length)
    (hcap : (ks1 ++ s :: ks2).length ≤ bc)
    (hch : ChainA (WF lc bc h false) lo hi (ks1 ++ ks2) (cs1 ++ ab :: cs2))
    (hks : (ks1 ++ ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ ks2, InBounds lo hi t)
    (htl : ab.toList = a.toList ++ b.toList)
    (horig : orig.toList = ((cs1 ++ a :: b :: cs2).map Node.toList).flatten) :
    FixOK lc bc h isRoot lo hi (ks1 ++ s :: ks2) orig
      (mkBranch (ks1 ++ ks2) (cs1 ++ ab :: cs2))
      (decide ((ks1 ++ s :: ks2).length - 1 < bc / 2)) := by
  have hlenr : (cs1 ++ ab :: cs2).length = (ks1 ++ ks2).length + 1 := by simp; omega
  refine ⟨shape_of_arrays hlenr hks hbk (by simp only [List.length_append, List.length_cons] at hcap ⊢; omega) hch, ?_, ?_, ?_, ?_⟩
  · rw [len_mkBranch hlenr]; simp only [List.length_append, List.length_cons]; omega
  · rw [len_mkBranch hlenr]; simp only [List.length_append, List.length_cons]; omega
  · intro _; rw [len_mkBranch hlenr]; simp
  · rw [toList_mkBranch hlenr, horig, flatten_window1 cs1 cs2 htl]

/-- `fix_branch_child` on a branch whose `children[cs1.length]` is one entry
short of the minimum (`new`, standing where `old` stood in the original,
well-formed chain): the result is shaped, has the same or one fewer key,
reports underfull correctly for a non-root branch, and keeps the entries. -/
theorem fixBranchChild_spec (lc bc h : Nat) (hlc : 4 ≤ lc) (hbc : 4 ≤ bc) (isRoot : Bool)
    (lo hi : Option K) (c0 : Node K V) (es : List (K × Node K V))
    (ks1 ks2 : List K) (cs1 cs2 : List (Node K V)) (old new : Node K V)
    (hkeys : es.map Prod.fst = ks1 ++ ks2) (hchildren : c0 :: es.map Prod.snd = cs1 ++ new :: cs2)
    (hlen : ks1.length = cs1.length)
    (hsk : (ks1 ++ ks2).Pairwise (· < ·)) (hbk : ∀ t ∈ ks1 ++ ks2, InBounds lo hi t)
    (hcap : (ks1 ++ ks2).length ≤ bc)
    (hfill : if isRoot then 1 ≤ (ks1 ++ ks2).length else bc / 2 ≤ (ks1 ++ ks2).length)
    (hchain : ChainA (WF lc bc h false) lo hi (ks1 ++ ks2) (cs1 ++ old :: cs2))
    (hnew : Shape lc bc h (lastB lo ks1) (headB hi ks2) new)
    (hunder : new.len < minOf lc bc h) (hdef : minOf lc bc h ≤ new.len + 1)
    (node' : Node K V) (under : Bool)
    (hfix : fixBranchChild lc bc (.branch c0 es) cs1.length = (node', under)) :
    FixOK lc bc h isRoot lo hi (ks1 ++ ks2) (Node.branch c0 es) node' under := by
  have hcs2 : cs2.length = ks2.length := by
    have h1 := congrArg List.length hkeys
    have h2 := congrArg List.length hchildren
    simp at h1 h2; omega
  have hlenks : 1 ≤ (ks1 ++ ks2).length := by
    split at hfill <;> omega
  have hidx : cs1.length ≤ (ks1 ++ ks2).length := by simp; omega
  have htl0 : (Node.branch c0 es).toList = ((cs1 ++ new :: cs2).map Node.toList).flatten := by
    rw [toList_branch_flatten, hchildren]
  have hmb := minBranchLen_eq (bc := bc) (by omega)
  -- Evaluate the model down to the plan.
  simp only [fixBranchChild] at hfix
  rw [show es.map (·.1) = ks1 ++ ks2 from hkeys,
    show c0 :: es.map (·.2) = cs1 ++ new :: cs2 from hchildren] at hfix
  simp only [if_neg (by omega : ¬ (ks1 ++ ks2).length = 0), Nat.min_eq_left hidx,
    getElem?_window_fst] at hfix
  cases h with
  | zero =>
    obtain ⟨kvsN, rfl⟩ := shape_leaf hnew
    simp only [rebalanceLeafChild] at hfix
    have hplan := planRebalance_spec (cs1 ++ Node.leaf kvsN :: cs2) cs1.length
      (ks1 ++ ks2).length (minLeafLen lc)
    rcases hp : planRebalance (cs1 ++ Node.leaf kvsN :: cs2) cs1.length (ks1 ++ ks2).length
        (minLeafLen lc) with _ | _ | _ | _ <;>
      rw [hp] at hplan hfix <;>
      simp only [Rebalance.mergesSiblings, Bool.false_and, Bool.true_and, Prod.mk.injEq] at hfix <;>
      obtain ⟨rfl, rfl⟩ := hfix
    · -- Borrow from the left leaf.
      obtain ⟨hpos, hdon⟩ := hplan
      obtain ⟨cs1', left, rfl⟩ := exists_concat_of_length_pos hpos
      obtain ⟨ks1', sL, rfl⟩ := exists_concat_of_length_pos (by omega : 0 < ks1.length)
      have hlen' : ks1'.length = cs1'.length := by simp at hlen; omega
      have hidx' : (cs1' ++ [left]).length - 1 = cs1'.length := by simp
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hsk hbk hcap hfill hchain htl0 hdon ⊢
      rw [hidx'] at hdon ⊢
      rw [childLen_window_fst] at hdon
      obtain ⟨⟨hwl, _⟩, hrep, _⟩ := chainA_window2 _ hi sL ks2 left old cs2 ks1' cs1' lo hlen' hchain
      obtain ⟨L, rfl⟩ := shape_leaf (shape_of_wf hwl)
      rw [lastB_append_singleton] at hnew
      have hw := rotateLeafRight_window lc bc hlc ks1' sL ks2 cs1' L kvsN cs2 lo hi hlen' hsk hbk hwl
        (by simpa [Node.len, minLeafLen] using hdon) hnew hunder hdef
      obtain ⟨a', b', s', hres, hwa, hwb, hks, hbk', htl⟩ := hw
      rw [hres]
      exact fixOK_of_window2 hlen' hcs2 hcap hfill (hrep a' b' s' hwa hwb) hks hbk' htl htl0
    · -- Borrow from the right leaf.
      obtain ⟨hlt, hdon⟩ := hplan
      have hks2 : ks2 ≠ [] := by intro hnil; subst hnil; simp at hlt; omega
      rcases ks2 with _ | ⟨sR, ks2'⟩
      · exact absurd rfl hks2
      rcases cs2 with _ | ⟨right, cs2'⟩
      · simp at hcs2
      rw [childLen_window_snd] at hdon
      obtain ⟨⟨_, hwr⟩, hrep, _⟩ := chainA_window2 _ hi sR ks2' old right cs2' ks1 cs1 lo hlen hchain
      obtain ⟨R, rfl⟩ := shape_leaf (shape_of_wf hwr)
      have hw := rotateLeafLeft_window lc bc hlc ks1 sR ks2' cs1 kvsN R cs2' lo hi hlen hsk hbk hnew
        hunder hdef hwr (by simpa [Node.len, minLeafLen] using hdon)
      obtain ⟨a', b', s', hres, hwa, hwb, hks, hbk', htl⟩ := hw
      rw [hres]
      exact fixOK_of_window2 hlen (by simpa using hcs2) hcap hfill (hrep a' b' s' hwa hwb) hks hbk'
        htl htl0
    · -- Merge with the left leaf.
      obtain ⟨hpos, hsib, _⟩ := hplan
      obtain ⟨cs1', left, rfl⟩ := exists_concat_of_length_pos hpos
      obtain ⟨ks1', sL, rfl⟩ := exists_concat_of_length_pos (by omega : 0 < ks1.length)
      have hlen' : ks1'.length = cs1'.length := by simp at hlen; omega
      have hidx' : (cs1' ++ [left]).length - 1 = cs1'.length := by simp
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hsk hbk hcap hfill hchain htl0 hsib ⊢
      rw [hidx'] at hsib ⊢
      rw [childLen_window_fst] at hsib
      obtain ⟨⟨hwl, _⟩, _, hmerge⟩ := chainA_window2 _ hi sL ks2 left old cs2 ks1' cs1' lo hlen' hchain
      obtain ⟨L, rfl⟩ := shape_leaf (shape_of_wf hwl)
      rw [lastB_append_singleton] at hnew
      have hLmin := (leaf_wf_iff.mp hwl).2.2.2
      simp only [Node.len, minLeafLen, minOf] at hsib hunder hdef
      have hw := mergeLeafPair_window lc bc ks1' sL ks2 cs1' L kvsN cs2 lo hi hlen' hsk hbk
        (shape_of_wf hwl) hnew (by omega) (by omega)
      obtain ⟨ab, hres, hwab, hks, hbk', htl⟩ := hw
      rw [hres, hmb]
      exact fixOK_of_window1 hlen' hcs2 hcap (hmerge ab hwab) hks hbk' htl htl0
    · -- Merge with the right leaf.
      obtain ⟨hzero, hsib⟩ := hplan
      have hks2 : ks2 ≠ [] := by intro hnil; subst hnil; simp only [List.append_nil] at hlenks; omega
      rcases ks2 with _ | ⟨sR, ks2'⟩
      · exact absurd rfl hks2
      rcases cs2 with _ | ⟨right, cs2'⟩
      · simp at hcs2
      have hsib' := hsib (by simp; omega)
      rw [childLen_window_snd] at hsib'
      obtain ⟨⟨_, hwr⟩, _, hmerge⟩ := chainA_window2 _ hi sR ks2' old right cs2' ks1 cs1 lo hlen hchain
      obtain ⟨R, rfl⟩ := shape_leaf (shape_of_wf hwr)
      have hRmin := (leaf_wf_iff.mp hwr).2.2.2
      simp only [Node.len, minLeafLen, minOf] at hsib' hunder hdef
      have hw := mergeLeafPair_window lc bc ks1 sR ks2' cs1 kvsN R cs2' lo hi hlen hsk hbk
        hnew (shape_of_wf hwr) (by omega) (by omega)
      obtain ⟨ab, hres, hwab, hks, hbk', htl⟩ := hw
      rw [hres, hmb]
      exact fixOK_of_window1 hlen (by simpa using hcs2) hcap (hmerge ab hwab) hks hbk' htl htl0
  | succ hc =>
    obtain ⟨nc0, nes, rfl⟩ := shape_branch hnew
    simp only [rebalanceBranchChild] at hfix
    have hplan := planRebalance_spec (cs1 ++ Node.branch nc0 nes :: cs2) cs1.length
      (ks1 ++ ks2).length (minBranchLen bc)
    rcases hp : planRebalance (cs1 ++ Node.branch nc0 nes :: cs2) cs1.length (ks1 ++ ks2).length
        (minBranchLen bc) with _ | _ | _ | _ <;>
      rw [hp] at hplan hfix <;>
      simp only [Rebalance.mergesSiblings, Bool.false_and, Bool.true_and, Prod.mk.injEq] at hfix <;>
      obtain ⟨rfl, rfl⟩ := hfix <;>
      rw [hmb] at hplan
    · -- Borrow from the left branch.
      obtain ⟨hpos, hdon⟩ := hplan
      obtain ⟨cs1', left, rfl⟩ := exists_concat_of_length_pos hpos
      obtain ⟨ks1', sL, rfl⟩ := exists_concat_of_length_pos (by omega : 0 < ks1.length)
      have hlen' : ks1'.length = cs1'.length := by simp at hlen; omega
      have hidx' : (cs1' ++ [left]).length - 1 = cs1'.length := by simp
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hsk hbk hcap hfill hchain htl0 hdon ⊢
      rw [hidx'] at hdon ⊢
      rw [childLen_window_fst] at hdon
      obtain ⟨⟨hwl, _⟩, hrep, _⟩ := chainA_window2 _ hi sL ks2 left old cs2 ks1' cs1' lo hlen' hchain
      obtain ⟨lc0, les, rfl⟩ := shape_branch (shape_of_wf hwl)
      rw [lastB_append_singleton] at hnew
      simp only [Node.len, minOf] at hdon hunder hdef
      have hw := rotateBranchRight_window lc bc hc (by omega) hbc ks1' sL ks2 cs1' lc0 les nc0 nes cs2
        lo hi hlen' hsk hbk hwl hdon hnew hunder hdef
      obtain ⟨a', b', s', hres, hwa, hwb, hks, hbk', htl⟩ := hw
      rw [hres]
      exact fixOK_of_window2 hlen' hcs2 hcap hfill (hrep a' b' s' hwa hwb) hks hbk' htl htl0
    · -- Borrow from the right branch.
      obtain ⟨hlt, hdon⟩ := hplan
      have hks2 : ks2 ≠ [] := by intro hnil; subst hnil; simp at hlt; omega
      rcases ks2 with _ | ⟨sR, ks2'⟩
      · exact absurd rfl hks2
      rcases cs2 with _ | ⟨right, cs2'⟩
      · simp at hcs2
      rw [childLen_window_snd] at hdon
      obtain ⟨⟨_, hwr⟩, hrep, _⟩ := chainA_window2 _ hi sR ks2' old right cs2' ks1 cs1 lo hlen hchain
      obtain ⟨rc0, res, rfl⟩ := shape_branch (shape_of_wf hwr)
      simp only [Node.len, minOf] at hdon hunder hdef
      have hw := rotateBranchLeft_window lc bc hc (by omega) hbc ks1 sR ks2' cs1 nc0 nes rc0 res cs2'
        lo hi hlen hsk hbk hnew hunder hdef hwr hdon
      obtain ⟨a', b', s', hres, hwa, hwb, hks, hbk', htl⟩ := hw
      rw [hres]
      exact fixOK_of_window2 hlen (by simpa using hcs2) hcap hfill (hrep a' b' s' hwa hwb) hks hbk'
        htl htl0
    · -- Merge with the left branch.
      obtain ⟨hpos, hsib, _⟩ := hplan
      obtain ⟨cs1', left, rfl⟩ := exists_concat_of_length_pos hpos
      obtain ⟨ks1', sL, rfl⟩ := exists_concat_of_length_pos (by omega : 0 < ks1.length)
      have hlen' : ks1'.length = cs1'.length := by simp at hlen; omega
      have hidx' : (cs1' ++ [left]).length - 1 = cs1'.length := by simp
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hsk hbk hcap hfill hchain htl0 hsib ⊢
      rw [hidx'] at hsib ⊢
      rw [childLen_window_fst] at hsib
      obtain ⟨⟨hwl, _⟩, _, hmerge⟩ := chainA_window2 _ hi sL ks2 left old cs2 ks1' cs1' lo hlen' hchain
      obtain ⟨lc0, les, rfl⟩ := shape_branch (shape_of_wf hwl)
      rw [lastB_append_singleton] at hnew
      have hLmin := (branch_wf_iff.mp hwl).2.2.2.1
      simp only [Node.len, minOf] at hsib hunder hdef
      have hw := mergeBranchPair_window lc bc hc (by omega) ks1' sL ks2 cs1' lc0 les nc0 nes cs2 lo hi
        hlen' hsk hbk (shape_of_wf hwl) (by omega) hnew (by omega) (by omega)
      obtain ⟨ab, hres, hwab, hks, hbk', htl⟩ := hw
      rw [hres, hmb]
      exact fixOK_of_window1 hlen' hcs2 hcap (hmerge ab hwab) hks hbk' htl htl0
    · -- Merge with the right branch.
      obtain ⟨hzero, hsib⟩ := hplan
      have hks2 : ks2 ≠ [] := by intro hnil; subst hnil; simp only [List.append_nil] at hlenks; omega
      rcases ks2 with _ | ⟨sR, ks2'⟩
      · exact absurd rfl hks2
      rcases cs2 with _ | ⟨right, cs2'⟩
      · simp at hcs2
      have hsib' := hsib (by simp; omega)
      rw [childLen_window_snd] at hsib'
      obtain ⟨⟨_, hwr⟩, _, hmerge⟩ := chainA_window2 _ hi sR ks2' old right cs2' ks1 cs1 lo hlen hchain
      obtain ⟨rc0, res, rfl⟩ := shape_branch (shape_of_wf hwr)
      have hRmin := (branch_wf_iff.mp hwr).2.2.2.1
      simp only [Node.len, minOf] at hsib' hunder hdef
      have hw := mergeBranchPair_window lc bc hc (by omega) ks1 sR ks2' cs1 nc0 nes rc0 res cs2' lo hi
        hlen hsk hbk hnew (by omega) (shape_of_wf hwr) (by omega) (by omega)
      obtain ⟨ab, hres, hwab, hks, hbk', htl⟩ := hw
      rw [hres, hmb]
      exact fixOK_of_window1 hlen (by simpa using hcs2) hcap (hmerge ab hwab) hks hbk' htl htl0

end Fix

/-! ## `remove_rec` and `remove` -/

section Remove

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K] [DecidableLT K]

theorem wf_min_le_len {lc bc h : Nat} {lo hi : Option K} {n : Node K V}
    (hw : WF lc bc h false lo hi n) : minOf lc bc h ≤ n.len := by
  cases h with
  | zero => cases n with
    | leaf kvs =>
      rcases hw.2.2.2 with h | h
      · cases h
      · exact h
    | branch _ _ => exact absurd hw id
  | succ h => cases n with
    | leaf _ => exact absurd hw id
    | branch c0 es =>
      have := hw.2.2.2.1
      simp only [Bool.false_eq_true, if_false] at this
      exact this

theorem chainA_of_chain_split (P : Option K → Option K → Node K V → Prop) (lo hi : Option K)
    (c0 : Node K V) (A B : List (K × Node K V)) (h : Chain P lo hi c0 (A ++ B)) :
    ChainA P lo hi (A.map Prod.fst ++ B.map Prod.fst)
      ((c0 :: A.map Prod.snd).dropLast ++ lastChild c0 A :: B.map Prod.snd) := by
  have := (chain_iff_chainA P lo hi c0 (A ++ B)).mp h
  rwa [List.map_append, children_split] at this

/-- `leaf_remove`: what it returns and what it leaves. -/
theorem leafRemove_spec {kvs : Leaf K V} {k : K} (hs : Sorted kvs) :
    match leafRemove kvs k with
    | none => ∀ e ∈ kvs, e.1 ≠ k
    | some (v, kvs') =>
      (k, v) ∈ kvs ∧ kvs' = eraseSorted k kvs ∧ Sorted kvs' ∧ (∀ e ∈ kvs', e ∈ kvs) ∧
        kvs'.length + 1 = kvs.length := by
  obtain ⟨A, B, rfl, hidx, hA, hB⟩ := lowerBound_spec kvs k hs
  simp only [leafRemove, hidx, getElem?_append_length]
  have hsB : Sorted B := hs.sublist (List.sublist_append_right A B)
  cases B with
  | nil =>
    simp only [List.head?_nil]
    intro e he
    simp only [List.append_nil] at he
    exact ne_of_lt (hA e he)
  | cons e B =>
    simp only [List.head?_cons]
    by_cases hke : k < e.1
    · rw [if_pos hke]
      have hgt := forall_gt_of_head_gt hsB hke
      show ∀ x ∈ A ++ e :: B, x.1 ≠ k
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact ne_of_lt (hA x hx)
      · exact (ne_of_lt (hgt x hx)).symm
    · rw [if_neg hke]
      have hek : e.1 = k := by
        rcases lt_trichotomy e.1 k with h' | h' | h'
        · exact absurd h' (hB e List.mem_cons_self)
        · exact h'
        · exact absurd h' hke
      show (k, e.2) ∈ A ++ e :: B ∧ (A ++ e :: B).eraseIdx A.length = eraseSorted k (A ++ e :: B) ∧
        Sorted ((A ++ e :: B).eraseIdx A.length) ∧
        (∀ x ∈ (A ++ e :: B).eraseIdx A.length, x ∈ A ++ e :: B) ∧
        ((A ++ e :: B).eraseIdx A.length).length + 1 = (A ++ e :: B).length
      rw [eraseIdx_window]
      refine ⟨?_, (eraseSorted_present A e B hA hek).symm, ?_, ?_,
        by simp only [List.length_append, List.length_cons]; omega⟩
      · have : (k, e.2) = e := by
          rcases e with ⟨ek, ev⟩; simp at hek; simp [hek]
        rw [this]; exact List.mem_append_right _ List.mem_cons_self
      · exact hs.sublist ((List.Sublist.refl A).append (List.sublist_cons_self e B))
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact List.mem_append_left _ hx
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)

/-- `remove_rec` on a well-formed node: the removed pair was there, the
result's entries are `eraseSorted` of the old, the result is shaped at the
same height and bounds with the same or one fewer key, and (below the
root) the underflow flag is exact. -/
theorem removeRec_spec (lc bc : Nat) (hlc : 4 ≤ lc) (hbc : 4 ≤ bc) (k : K) :
    ∀ (h : Nat) (n : Node K V) (isRoot : Bool) (lo hi : Option K),
      WF lc bc h isRoot lo hi n → InBounds lo hi k →
      match removeRec lc bc k n with
      | none => ∀ e ∈ n.toList, e.1 ≠ k
      | some (v, n', under) =>
        (k, v) ∈ n.toList ∧ n'.toList = eraseSorted k n.toList ∧ Shape lc bc h lo hi n' ∧
          n.len ≤ n'.len + 1 ∧ n'.len ≤ n.len ∧
          (isRoot = false → under = decide (n'.len < minOf lc bc h)) := by
  intro h
  induction h with
  | zero =>
    intro n isRoot lo hi hwf hk
    cases n with
    | branch _ _ => exact absurd hwf id
    | leaf kvs =>
      obtain ⟨hs, hb, hlen, _⟩ := hwf
      rw [removeRec]
      have hspec := leafRemove_spec (k := k) hs
      rcases hres : leafRemove kvs k with _ | ⟨v, kvs'⟩ <;> rw [hres] at hspec
      · exact hspec
      · obtain ⟨hmem, heq, hs', hsub, hlen'⟩ := hspec
        refine ⟨hmem, heq, ⟨hs', fun e he => hb e (hsub e he), by omega⟩, ?_, ?_, ?_⟩
        · simp [Node.len]; omega
        · simp [Node.len]; omega
        · intro _; rfl
  | succ h ih =>
    intro n isRoot lo hi hwf hk
    cases n with
    | leaf _ => exact absurd hwf id
    | branch c0 entries =>
      obtain ⟨hs, hb, hlen, hmin, hchain⟩ := hwf
      rw [removeRec]
      try simp only []
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
      have htl := toList_branch_split c0 A B
      have hspec : eraseSorted k (Node.branch c0 (A ++ B)).toList =
          frontList c0 A ++ eraseSorted k (lastChild c0 A).toList ++ entriesToList B := by
        rw [htl, List.append_assoc, eraseSorted_append_left _ _ hfront,
          eraseSorted_append_right _ _ hsuffix, List.append_assoc]
      have hkeysA := replaceLast_keys c0 A
      have hlenA := replaceLast_length c0 A
      have hcmin := wf_min_le_len hchild
      rcases hres : removeRec lc bc k (lastChild c0 A) with _ | ⟨v, child', cu⟩ <;>
        simp only [hres] at hrec ⊢
      · -- Not found below: not anywhere in this node.
        intro e he
        rw [htl] at he
        simp only [List.mem_append] at he
        rcases he with (he | he) | he
        · exact ne_of_lt (hfront e he)
        · exact hrec e he
        · exact (ne_of_lt (hsuffix e he)).symm
      obtain ⟨hmem, heq, hshape, hl1, hl2, hflag⟩ := hrec
      have hflag' : cu = decide (child'.len < minOf lc bc h) := by
        first | exact hflag rfl | exact hflag trivial | exact hflag (by simp)
      have hmem' : (k, v) ∈ (Node.branch c0 (A ++ B)).toList := by
        rw [htl]; exact List.mem_append_left _ (List.mem_append_right _ hmem)
      have hkeys : (A ++ B).map Prod.fst = ((replaceLast c0 A child').2 ++ B).map Prod.fst := by
        simp [hkeysA child']
      have hnode1 : (Node.branch (replaceLast c0 A child').1 ((replaceLast c0 A child').2 ++ B)).toList =
          eraseSorted k (Node.branch c0 (A ++ B)).toList := by
        rw [toList_branch_split, frontList_replaceLast, lastChild_replaceLast, heq, hspec]
      cases cu with
      | false =>
        -- The child is still at or above its minimum: put it back.
        simp only [Bool.false_eq_true, if_false]
        have hcmin' : minOf lc bc h ≤ child'.len := by
          refine Nat.le_of_not_lt (fun hlt => ?_)
          rw [decide_eq_true hlt] at hflag'
          cases hflag'
        have hwc : WF lc bc h false _ _ child' := wf_of_shape_nonroot hshape hcmin'
        refine ⟨hmem', hnode1, ⟨sorted_of_keys_eq hkeys hs, forall_key_of_keys_eq hkeys _ hb, ?_,
          chain_replace _ A B lo hi c0 child' hchain hwc⟩, ?_, ?_, ?_⟩
        · simp only [List.length_append, hlenA child'] at hlen ⊢; exact hlen
        · simp [Node.len, hlenA child']
        · simp [Node.len, hlenA child']
        · intro hroot; subst hroot
          simp only [Bool.false_eq_true, if_false] at hmin
          simp only [Node.len, List.length_append, hlenA child', minOf]
          simp at hmin ⊢; omega
      | true =>
        -- The child is one short: repair it here.
        simp only [if_true]
        have hunder : child'.len < minOf lc bc h := of_decide_eq_true hflag'.symm
        rcases hfix : fixBranchChild lc bc
            (Node.branch (replaceLast c0 A child').1 ((replaceLast c0 A child').2 ++ B)) A.length
          with ⟨node', under'⟩
        have hchA := chainA_of_chain_split _ lo hi c0 A B hchain
        have hsk : (A.map Prod.fst ++ B.map Prod.fst).Pairwise (· < ·) := by
          rw [← List.map_append]; exact List.pairwise_map.mpr hs
        have hbk : ∀ t ∈ A.map Prod.fst ++ B.map Prod.fst, InBounds lo hi t := by
          intro t ht
          rw [← List.map_append] at ht
          obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
          exact hb e he
        have hlenks : (A.map Prod.fst ++ B.map Prod.fst).length = (A ++ B).length := by simp
        have hfix' := fixBranchChild_spec lc bc h hlc hbc isRoot lo hi _ _ (A.map Prod.fst)
          (B.map Prod.fst) ((c0 :: A.map Prod.snd).dropLast) (B.map Prod.snd) (lastChild c0 A)
          child'
          (by rw [List.map_append, hkeysA child'])
          (children_replaceLast c0 child' A B)
          (by simp)
          hsk hbk (by rw [hlenks]; exact hlen) (by rw [hlenks]; exact hmin) hchA
          (by rw [lastB_map_fst, headB_map_fst]; exact hshape)
          hunder (by omega) node' under'
          (by rw [← hfix]; congr 1; simp)
        obtain ⟨hshape', hl1', hl2', hflag'', htl'⟩ := hfix'
        refine ⟨hmem', by rw [htl', hnode1], hshape', ?_, ?_, ?_⟩
        · simp only [Node.len, List.length_append, List.length_map] at hl1' ⊢; omega
        · simp only [Node.len, List.length_append, List.length_map] at hl2' ⊢; omega
        · intro hroot
          rw [hflag'' hroot]
          rfl

theorem removeTree_eq_none {lc bc : Nat} {root : Node K V} {k : K}
    (hres : removeRec lc bc k root = none) : removeTree lc bc root k = none := by
  unfold removeTree; rw [hres]

theorem removeTree_eq_leaf {lc bc : Nat} {root : Node K V} {k : K} {v : V} {kvs : Leaf K V}
    {under : Bool} (hres : removeRec lc bc k root = some (v, .leaf kvs, under)) :
    removeTree lc bc root k = some (v, .leaf kvs) := by
  unfold removeTree; rw [hres]

theorem removeTree_eq_branch {lc bc : Nat} {root : Node K V} {k : K} {v : V} {c0 : Node K V}
    {es : List (K × Node K V)} {under : Bool}
    (hres : removeRec lc bc k root = some (v, .branch c0 es, under)) :
    removeTree lc bc root k =
      if es.length ≤ 2 then some (v, checkRootCollapse lc (.branch c0 es))
      else some (v, .branch c0 es) := by
  unfold removeTree; rw [hres]

/-- `remove` on a well-formed root: the removed pair was there, the new
tree's entries are `eraseSorted` of the old, and the new root is
well-formed at the same height or one lower (root collapse). -/
theorem removeTree_spec (lc bc : Nat) (hlc : 4 ≤ lc) (hbc : 4 ≤ bc) (h : Nat) (root : Node K V)
    (k : K) (hwf : WF lc bc h true none none root) :
    match removeTree lc bc root k with
    | none => ∀ e ∈ root.toList, e.1 ≠ k
    | some (v, root') =>
      (k, v) ∈ root.toList ∧ root'.toList = eraseSorted k root.toList ∧
        ∃ h', h' ≤ h ∧ WF lc bc h' true none none root' := by
  have hk : InBounds (K := K) none none k :=
    ⟨(fun _ hl => by cases hl), (fun _ hh => by cases hh)⟩
  have hspec := removeRec_spec lc bc hlc hbc k h root true none none hwf hk
  rcases hres : removeRec lc bc k root with _ | ⟨v, root', under⟩ <;> rw [hres] at hspec
  · rw [removeTree_eq_none hres]
    exact hspec
  obtain ⟨hmem, htl, hshape, hl1, hl2, _⟩ := hspec
  cases root' with
  | leaf kvs =>
    rw [removeTree_eq_leaf hres]
    exact ⟨hmem, htl, h, Nat.le_refl _, wf_of_shape_root hshape (fun _ _ hn => by cases hn)⟩
  | branch c0' es =>
    cases h with
    | zero => exact absurd hshape id
    | succ hc =>
      obtain ⟨hs', hb', hcap', hchain'⟩ := hshape
      have hroot_wf : 1 ≤ es.length →
          WF lc bc (hc + 1) true none none (.branch c0' es) := fun hpos =>
        wf_of_shape_root ⟨hs', hb', hcap', hchain'⟩ (fun _ _ hn => by cases hn; exact hpos)
      rw [removeTree_eq_branch hres]
      by_cases hle : es.length ≤ 2
      · rw [if_pos hle]
        show (k, v) ∈ root.toList ∧
          (checkRootCollapse lc (.branch c0' es)).toList = eraseSorted k root.toList ∧
          ∃ h', h' ≤ hc + 1 ∧ WF lc bc h' true none none (checkRootCollapse lc (.branch c0' es))
        simp only [checkRootCollapse]
        by_cases hgt : es.length + 1 > 2
        · rw [if_pos hgt]
          exact ⟨hmem, htl, hc + 1, Nat.le_refl _, hroot_wf (by omega)⟩
        · rw [if_neg hgt]
          rcases es with _ | ⟨⟨s, c1⟩, rest⟩
          · -- One child: it becomes the root.
            have hwc : WF lc bc hc false none none c0' := hchain'
            have hne : c0'.toList ≠ [] := wf_toList_ne_nil lc bc (by omega) hc c0' _ _ hwc
            have hcons : consolidateRootChildren lc none [c0'] = some (some c0') := by
              cases c0' with
              | leaf L =>
                cases L with
                | nil => exact absurd rfl hne
                | cons x L' => rfl
              | branch _ _ => rfl
            simp only [List.map_nil]
            rw [hcons]
            refine ⟨hmem, ?_, hc, Nat.le_succ _, wf_root_of_nonroot (by omega) hwc⟩
            rw [← htl]; simp [Node.toList, entriesToList]
          · rcases rest with _ | ⟨_, _⟩
            · -- Two children: two leaves merge if they fit; otherwise stay.
              have hwc0 : WF lc bc hc false none (some s) c0' := hchain'.1
              have hwc1 : WF lc bc hc false (some s) none c1 := hchain'.2
              have hne0 : c0'.toList ≠ [] := wf_toList_ne_nil lc bc (by omega) hc c0' _ _ hwc0
              have hne1 : c1.toList ≠ [] := wf_toList_ne_nil lc bc (by omega) hc c1 _ _ hwc1
              cases hc with
              | zero =>
                obtain ⟨L, rfl⟩ := shape_leaf (shape_of_wf hwc0)
                obtain ⟨R, rfl⟩ := shape_leaf (shape_of_wf hwc1)
                rw [leaf_wf_iff] at hwc0 hwc1
                cases L with
                | nil => exact absurd rfl hne0
                | cons x L' =>
                cases R with
                | nil => exact absurd rfl hne1
                | cons y R' =>
                have hcons : consolidateRootChildren lc none
                    (Node.leaf (x :: L') :: [(s, Node.leaf (y :: R'))].map (·.2)) =
                    if (x :: L').length + (y :: R').length ≤ lc
                    then some (some (.leaf ((x :: L') ++ (y :: R')))) else none := rfl
                rw [hcons]
                by_cases hfit : (x :: L').length + (y :: R').length ≤ lc
                · rw [if_pos hfit]
                  refine ⟨hmem, ?_, 0, by omega, ?_⟩
                  · rw [← htl]; simp [Node.toList, entriesToList]
                  · rw [WF]
                    refine ⟨?_, fun e _ => ⟨(fun _ hl => by cases hl), (fun _ hh => by cases hh)⟩,
                      by simp at hfit ⊢; omega, Or.inl rfl⟩
                    simp only [Sorted, List.pairwise_append]
                    exact ⟨hwc0.1, hwc1.1, fun a ha b hb =>
                      lt_of_lt_of_le ((hwc0.2.1 a ha).2 s rfl) ((hwc1.2.1 b hb).1 s rfl)⟩
                · rw [if_neg hfit]
                  exact ⟨hmem, htl, 1, Nat.le_refl _, hroot_wf (by simp)⟩
              | succ hc' =>
                obtain ⟨lc0, les, rfl⟩ := shape_branch (shape_of_wf hwc0)
                obtain ⟨rc0, res, rfl⟩ := shape_branch (shape_of_wf hwc1)
                have hcons : consolidateRootChildren lc none
                    (Node.branch lc0 les :: [(s, Node.branch rc0 res)].map (·.2)) = none := rfl
                rw [hcons]
                exact ⟨hmem, htl, hc' + 1 + 1, Nat.le_refl _, hroot_wf (by simp)⟩
            · simp at hgt
      · rw [if_neg hle]
        exact ⟨hmem, htl, hc + 1, Nat.le_refl _, hroot_wf (by omega)⟩

end Remove

end BPlusTree
