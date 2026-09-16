import BPlusTree.Model.Tree
import BPlusTree.Model.Delete

/-!
# Model of `check_invariants_detailed`

The runtime checker in `src/common.rs`, arm for arm, minus the leaf
sibling-pointer checks (the model has no pointers). `validateNode`
threads the checker's `ValidationState` (entries counted, last key seen)
and returns the subtree's height, which `validate_branch` requires every
child to agree on. `Map` is `BPlusTreeMap` itself: the root plus the
stored `entry_count` that `len()` reports and the checker compares with
its count.
-/

namespace BPlusTree

open Std

section Check

variable {K V : Type} [LT K] [LE K] [IsLinearOrder K] [LawfulOrderLT K]
  [DecidableLT K]

/-- `ValidationState` without its pointer: `total_items` and `prev_key`. -/
structure VState (K : Type) where
  totalItems : Nat
  prevKey : Option K

/-- `keys.windows(2)`: each key strictly below the next. -/
def keysIncreasing : List K → Bool
  | a :: b :: rest => decide (a < b) && keysIncreasing (b :: rest)
  | _ => true

/-- The two bound checks: `keys[0] < low` and `keys[last] >= high` reject. -/
def boundsOK (lo hi : Option K) (keys : List K) : Bool :=
  (match lo, keys.head? with
    | some l, some k0 => decide (¬ k0 < l)
    | _, _ => true) &&
  (match hi, keys.getLast? with
    | some h, some kl => decide (kl < h)
    | _, _ => true)

/-- `observe_leaf`'s check: the leaf's first key is above the last key
seen (`keys[0] <= prev_key` rejects). -/
def observeOK (st : VState K) (kvs : Leaf K V) : Bool :=
  match st.prevKey, kvs.head? with
  | some p, some k0 => decide (p < k0.1)
  | _, _ => true

/-- `observe_leaf` on a nonempty leaf: after the check, its last key
becomes the last key seen and its length is counted. -/
def observeLeaf (st : VState K) (kvs : Leaf K V) : Option (VState K) :=
  if observeOK st kvs then some ⟨st.totalItems + kvs.length, kvs.getLast?.map (·.1)⟩ else none

/-- `validate_leaf`: the state afterwards and the height 0. -/
def validateLeaf (lc : Nat) (lo hi : Option K) (isRoot : Bool) (st : VState K)
    (kvs : Leaf K V) : Option (VState K × Nat) :=
  if lc < kvs.length then none
  else if kvs.length = 0 ∧ isRoot = false then none
  else if isRoot = false ∧ kvs.length < minLeafLen lc then none
  else if kvs.length = 0 then some (st, 0)
  else if keysIncreasing (kvs.map (·.1)) = false then none
  else if boundsOK lo hi (kvs.map (·.1)) = false then none
  else (observeLeaf st kvs).map fun st' => (st', 0)

mutual
/-- `validate_node`: the state afterwards and the subtree's height. -/
def validateNode (lc bc : Nat) (lo hi : Option K) (isRoot : Bool) (st : VState K) :
    Node K V → Option (VState K × Nat)
  | .leaf kvs => validateLeaf lc lo hi isRoot st kvs
  | .branch c0 es =>
    let keys := es.map (·.1)
    let len := keys.length
    if bc < len then none
    else if len = 0 then none
    else if isRoot = false ∧ len < minBranchLen bc then none
    else if keysIncreasing keys = false then none
    else if boundsOK lo hi keys = false then none
    else validateChildren lc bc lo hi st c0 es
termination_by n => sizeOf n
decreasing_by all_goals (simp_wf <;> omega)

/-- The children loop of `validate_branch`: `children[i]` is validated
between `keys[i - 1]` and `keys[i]`, the state threads through, and every
child's height must equal the first's. Returns the branch's height. -/
def validateChildren (lc bc : Nat) (lo hi : Option K) (st : VState K) :
    Node K V → List (K × Node K V) → Option (VState K × Nat)
  | c, [] =>
    match validateNode lc bc lo hi false st c with
    | none => none
    | some (st', d) => some (st', d + 1)
  | c, (s, c') :: rest =>
    match validateNode lc bc lo (some s) false st c with
    | none => none
    | some (st1, d1) =>
      match validateChildren lc bc (some s) hi st1 c' rest with
      | none => none
      | some (st2, d2) => if d1 + 1 = d2 then some (st2, d2) else none
termination_by c es => sizeOf c + sizeOf es
decreasing_by all_goals (simp_wf <;> omega)
end

/-- `check_invariants_detailed` on a tree whose stored length is `count`. -/
def checkInvariants (lc bc : Nat) (root : Node K V) (count : Nat) : Bool :=
  match validateNode lc bc none none true ⟨0, none⟩ root with
  | none => false
  | some (st, _) => decide (st.totalItems = count)

/-- `BPlusTreeMap`: the root and `entry_count`. -/
structure Map (K V : Type) where
  root : Node K V
  count : Nat

/-- `insert`: `entry_count` grows exactly when no old value came back. -/
def Map.insert (lc bc : Nat) (m : Map K V) (k : K) (v : V) : Map K V × Option V :=
  match insertTree lc bc m.root k v with
  | (root', old) => (⟨root', if old.isNone then m.count + 1 else m.count⟩, old)

/-- `remove`: `entry_count` shrinks on success. -/
def Map.remove (lc bc : Nat) (m : Map K V) (k : K) : Option (V × Map K V) :=
  match removeTree lc bc m.root k with
  | none => none
  | some (v, root') => some (v, ⟨root', m.count - 1⟩)

/-- `len`. -/
def Map.len (m : Map K V) : Nat := m.count

end Check

end BPlusTree
