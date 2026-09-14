# Lean model and proofs

A Lean 4 model of the B+ tree in `../src`, with proofs of the invariants the
Rust `check_invariants_detailed` checks at runtime. See
`../LEAN_VERIFICATION_PLAN.md` for scope and the phases; this directory is
where the phases land.

Build with `lake build` (toolchain pinned in `lean-toolchain`; no Mathlib,
only core `Std`). CI runs it on every push.

## Correspondence

Each model definition mirrors one Rust function by name and keeps its
arithmetic verbatim. The proofs are about the model; this table is the
link a reviewer checks by eye.

| Rust (`src/`) | Lean | Proved |
|---|---|---|
| `shift_right` + `write_kv_at` | `insertAt` (`Model/Leaf.lean`) | shape on a split list |
| `Ok(idx)` arm value overwrite | `replaceAt` | shape on a split list |
| `binary_search_keys` on a leaf | `lowerBound` | cuts a sorted leaf into keys `< k` and keys `≥ k` |
| split arm of `leaf_insert_or_split` (`left_count`, `left_keep`) | `leafSplit` | `leafSplit_eq`: both `left_keep` cases equal "insert, then cut at `(len + 1) / 2`" |
| `leaf_insert_or_split` | `leafInsertOrSplit` | `leafInsertOrSplit_noSplit`, `leafInsertOrSplit_split` |
| `validate_leaf_key_order_and_bounds` (strictly increasing) | `Sorted` | preserved by both outcomes |
| `validate_leaf_occupancy` (`cap / 2 ≤ len ≤ cap`) | length bounds in the split theorem | both halves, for every `cap ≥ 1` |

What the two main theorems say, given a sorted leaf within capacity:

- `NoSplit`: the leaf stays sorted and within capacity. If a value is
  returned, that key-value pair was in the leaf and the length is
  unchanged. If none is, the key was absent and the length grew by one.
- `Split`: both halves are sorted and hold between `cap / 2` and `cap`
  entries; the separator is the right half's first key, strictly above
  every left key and at or below every right key; the key was absent; and
  the two halves concatenated are the old leaf with the new entry
  inserted at its sorted position.

Not modelled here: node memory, sibling pointers, and the parent's
handling of the split. Those are the next phases.
