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

end Spec

end BPlusTree
