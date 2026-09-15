/-!
# The abstract specification

A map is a sorted association list. `insertSorted` is what `insert` must
agree with through `toList`: replace the value if the key is present, else
place the pair in key order.
-/

namespace BPlusTree

section Spec

variable {K V : Type} [LT K] [DecidableLT K]

/-- Insertion into a sorted association list. -/
def insertSorted (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | e :: rest =>
    if e.1 < k then e :: insertSorted k v rest
    else if k < e.1 then (k, v) :: e :: rest
    else (k, v) :: rest

/-- Removal from a sorted association list: drop the entry with the key,
if any. -/
def eraseSorted (k : K) : List (K × V) → List (K × V)
  | [] => []
  | e :: rest =>
    if e.1 < k then e :: eraseSorted k rest
    else if k < e.1 then e :: rest
    else rest

/-- `core::ops::Bound`, the two ends of a `range` query. -/
inductive Bound (K : Type) where
  | unbounded
  | included (k : K)
  | excluded (k : K)

/-- Does an entry satisfy a start bound? (`x >= k`, or `x > k` when
excluded.) -/
def Bound.admitsFrom {V : Type} : Bound K → K × V → Bool
  | .unbounded, _ => true
  | .included k, e => decide (¬ e.1 < k)
  | .excluded k, e => decide (k < e.1)

/-- Does an entry satisfy an end bound? (`x <= k`, or `x < k` when
excluded.) -/
def Bound.admitsTo {V : Type} : Bound K → K × V → Bool
  | .unbounded, _ => true
  | .included k, e => decide (¬ k < e.1)
  | .excluded k, e => decide (e.1 < k)

/-- The entries of a sorted association list inside two bounds: what
`range` must yield through `toList`. On a sorted list the entries below
the start form a prefix and those within the end form a prefix, so this
is the slice between them. -/
def rangeSorted (start stop : Bound K) (l : List (K × V)) : List (K × V) :=
  (l.dropWhile (fun e => !start.admitsFrom e)).takeWhile stop.admitsTo

end Spec

end BPlusTree
