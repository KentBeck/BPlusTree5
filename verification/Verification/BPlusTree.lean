import Mathlib.Order.Basic
import Mathlib.Data.List.Sort

-- B+ Tree Model
inductive BPlusTree (K V : Type) [LinearOrder K]
| leaf (keys : List K) (vals : List V)
| branch (keys : List K) (children : List (BPlusTree K V))

variable {K V : Type} [LinearOrder K]

-- Helper: Check if a list is sorted
def sorted (l : List K) : Prop := List.Sorted (· < ·) l

-- Helper: Safe list access
def get_opt {α} : List α -> Nat -> Option α
| [], _ => none
| a::_, 0 => some a
| _::as, n+1 => get_opt as n

-- 1. Sortedness
inductive NodeSorted : BPlusTree K V -> Prop
| leaf {keys vals} : sorted keys -> NodeSorted (BPlusTree.leaf keys vals)
| branch {keys children} : 
    sorted keys -> 
    (∀ c ∈ children, NodeSorted c) -> 
    NodeSorted (BPlusTree.branch keys children)

-- 2. Separation
def all_keys_lt (t : BPlusTree K V) (k : K) : Prop :=
  match t with
  | BPlusTree.leaf keys _ => ∀ x ∈ keys, x < k
  | BPlusTree.branch keys children => 
      (∀ x ∈ keys, x < k) /\ (∀ c ∈ children, all_keys_lt c k)

def all_keys_ge (t : BPlusTree K V) (k : K) : Prop :=
  match t with
  | BPlusTree.leaf keys _ => ∀ x ∈ keys, x >= k
  | BPlusTree.branch keys children => 
      (∀ x ∈ keys, x >= k) /\ (∀ c ∈ children, all_keys_ge c k)

inductive SeparatorsValid : BPlusTree K V -> Prop
| leaf {keys vals} : SeparatorsValid (BPlusTree.leaf keys vals)
| branch {keys children} :
    keys.length + 1 = children.length ->
    (∀ i : Nat, i < keys.length -> 
       match get_opt children i, get_opt children (i+1), get_opt keys i with
       | some left, some right, some k => 
           all_keys_lt left k /\ 
           all_keys_ge right k
       | _, _, _ => True
    ) ->
    (∀ c ∈ children, SeparatorsValid c) ->
    SeparatorsValid (BPlusTree.branch keys children)

-- 3. Balance (Height)
def height : BPlusTree K V -> Nat
| BPlusTree.leaf _ _ => 0
| BPlusTree.branch _ children => 
    match children with
    | [] => 0
    | (c :: _) => 1 + height c

inductive Balanced : BPlusTree K V -> Prop
| leaf {keys vals} : Balanced (BPlusTree.leaf keys vals)
| branch {keys children} :
    (match children with
     | [] => True
     | (c :: cs) => 
         let h := height c
         ∀ child ∈ cs, height child = h) ->
    (∀ c ∈ children, Balanced c) ->
    Balanced (BPlusTree.branch keys children)

-- Combined Invariant
def ValidTree (t : BPlusTree K V) : Prop :=
  NodeSorted t /\ SeparatorsValid t /\ Balanced t

-- Operations (Draft)

def insert_list (k : K) (v : V) : List K -> List V -> List K × List V
| [], _ => ([k], [v])
| k'::ks, [] => ([k, k'], [v]) -- Should not happen in valid tree
| k'::ks, v'::vs =>
    if k < k' then (k::k'::ks, v::v'::vs)
    else if k == k' then (k::ks, v::vs) -- Update
    else 
      let (new_ks, new_vs) := insert_list k v ks vs
      (k'::new_ks, v'::new_vs)

theorem insert_list_sorted (k : K) (v : V) (keys : List K) (vals : List V) :
  sorted keys -> sorted (insert_list k v keys vals).1 := by
  sorry

def insert_leaf (keys : List K) (vals : List V) (k : K) (v : V) : List K × List V :=
  insert_list k v keys vals

def insert (t : BPlusTree K V) (k : K) (v : V) : BPlusTree K V :=
  match t with
  | BPlusTree.leaf keys vals =>
      let (new_keys, new_vals) := insert_leaf keys vals k v
      BPlusTree.leaf new_keys new_vals
  | BPlusTree.branch keys children =>
      -- Recursive insert logic
      t -- Placeholder

-- Theorems to prove
theorem insert_preserves_valid (t : BPlusTree K V) (k : K) (v : V) :
  ValidTree t -> ValidTree (insert t k v) := by
  sorry
