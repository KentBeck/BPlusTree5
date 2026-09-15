# Lean model and proofs

A Lean 4 model of the B+ tree in `../src`, with proofs of the invariants the
Rust `check_invariants_detailed` checks at runtime. See
`../LEAN_VERIFICATION_PLAN.md` for scope and the phases; this directory is
where the phases land.

Build with `lake build` (toolchain pinned in `lean-toolchain`; no Mathlib,
only core `Std`). CI runs it on every push.

## Replay

`./lean/replay.sh` (from the repo root) builds `examples/gen_trace.rs`,
runs nine configurations of mixed inserts and removes against the Rust
tree (leaf and branch capacities from 4×4 to 32×256, key spaces from
heavy-duplicate to sparse, the fuzz suite's remove ratio and a
remove-heavy one, each followed by a drain that removes every remaining
key down to the empty tree), and writes each operation with its return
value plus, at intervals, a 64-bit FNV-1a digest of the tree's shape as
`dump_shape` renders it, with the full shape once at the end.
`lake exe replay` replays every operation through `insertTree` and
`removeTree`, checks each return value, renders its tree the same way,
and compares digests and the final shape. With
`cargo build --features delete_profile --example gen_trace` the generator
also reports how many leaf and branch borrows, merges, and root
collapses a trace exercised. Digests keep the traces small, so the large
configurations check every 10 to 100 operations. On a mismatch the Lean
side prints its shape and the script reruns the generator to print the
Rust shape at the same operation, with a token diff. CI runs it on every
push. FNV rather than a cryptographic hash because neither side is
adversarial and both implementations are ten lines that can be compared
by eye.

The replay is the only check on the delete model so far: its theorems
are not written yet, so shape equality across these traces is what
currently ties `removeTree` to `delete.rs`.

A shape match is stronger than the differential fuzz's map comparison:
it checks the same splits, the same separators, and the same leaf
contents, so it is the evidence that the model is the code and not just
a model of the same map. Traces cover insert only until the model has
`remove`.

## Correspondence

Each model definition mirrors one Rust function by name and keeps its
arithmetic verbatim. The proofs are about the model; this table is the
link a reviewer checks by eye.

| Rust (`src/`) | Lean | Proved |
|---|---|---|
| `shift_right` + `write_kv_at` | `insertAt` (`Model/Leaf.lean`) | shape on a split list |
| `Ok(idx)` arm value overwrite | `replaceAt` | shape on a split list |
| `binary_search_keys` on a leaf | `lowerBound` | cuts a sorted leaf into keys `< k` and keys `≥ k` |
| `split_leaf` (cut at `(len + 1) / 2`, separator = right half's first key) | `leafSplit` | halves' lengths, halves concatenate to the leaf |
| split arm of `leaf_insert_or_split` (split, route by separator, ordinary insert) | `leafSplitInsert` | never yields `NoSplit`; see the split theorem |
| `leaf_insert_or_split` | `leafInsertOrSplit` | `leafInsertOrSplit_noSplit`, `leafInsertOrSplit_split` |
| `validate_leaf_key_order_and_bounds` (strictly increasing) | `Sorted` | preserved by both outcomes |
| `validate_leaf_occupancy` (`cap / 2 ≤ len ≤ cap`) | length bounds in the split theorem | both halves, for every `cap ≥ 2` |
| entry view of a branch (`children[0]`, then `(keys[i], children[i+1])`) | `Branch` (`Model/Branch.lean`) | |
| `branch_open_gap` + writes in `branch_apply_split` | `insertAt` on the entries | sorted given `SepFits` |
| `left_count` / `left_keep` in `branch_insert_and_split` | `cutInsert` | `cutInsert_eq`: equals "insert, then cut at `(len + 1) / 2`" |
| promotion in `branch_insert_and_split` (key up, child becomes `children[0]`) | `branchInsertAndSplit` | see the split theorem |
| `branch_apply_split` | `branchApplySplit` | `branchApplySplit_noSplit`, `branchApplySplit_split` |
| `grow_root` | `growRoot` | `growRoot_spec` |
| node kinds (`NodeTag::Leaf` / `Branch`) | `Node` (`Model/Tree.lean`) | |
| `child_for_key` (child after the last separator `≤ k`) | `takeWhile (sepLE k)` + `lastChild` | the picked child's bounds contain `k` |
| `insert_rec` | `insertRec` | `insertRec_wf` |
| `insert` (with root growth) | `insertTree` | `insertTree_wf` |
| `check_invariants_detailed` bounds, order, fill; plus uniform leaf depth | `WF` (`Proofs/Tree.lean`) | preserved by insert |
| `dump_shape` / `shape_hash` (test-only, `compat_test_api`) | `shape` / `fnv1a` (`Replay/Main.lean`) | compared on every replayed trace |
| the leaves' entries left to right (what `items()` yields) | `Node.toList` (`Model/Tree.lean`) | `insertTree_toList`: insert = `insertSorted` on it |
| sorted-association-list insert (the spec) | `insertSorted` (`Model/Spec.lean`) | |
| `keys[]` / `children[]` view of a branch | `Node.keysOf`, `Node.childrenOf`, `mkBranch` (`Model/Delete.lean`) | |
| `leaf_remove` | `leafRemove` | replay |
| `plan_rebalance`, `child_len` | `planRebalance`, `childLen` | replay |
| `rotate_leaf_right` / `rotate_leaf_left` / `merge_leaf_pair` | same names | replay |
| `rotate_branch_right` / `rotate_branch_left` / `merge_branch_pair` | same names | replay |
| `rebalance_leaf_child` / `rebalance_branch_child` / `fix_branch_child` | same names | replay |
| `remove_rec` | `removeRec` | replay |
| `consolidate_root_children` + `absorb_root_child` | `consolidateRootChildren` | replay |
| `check_root_collapse`, `remove` | `checkRootCollapse`, `removeTree` | replay |

What the two main theorems say, given a sorted leaf within capacity:

- `NoSplit`: the leaf stays sorted and within capacity. If a value is
  returned, that key-value pair was in the leaf and the length is
  unchanged. If none is, the key was absent and the length grew by one.
- `Split`: both halves are sorted and hold between `cap / 2` and `cap`
  entries; the separator is the right half's first key, strictly above
  every left key and at or below every right key; the key was absent; and
  the two halves concatenated are the old leaf with the new entry
  inserted at its sorted position.

What the branch theorems say, given sorted entries and a separator that
fits strictly between the entries on either side of the split child
(`SepFits`, which is what a child split provides):

- `NoSplit`: the first child is unchanged, the entries are the old ones
  with `(sep, right)` inserted at the child's slot, still sorted, one
  longer, within capacity.
- `Split`: both halves are sorted and hold between `cap / 2` and `cap`
  entries for every `cap ≥ 1`; the promoted key is strictly above every
  left key and strictly below every right key; the left half keeps the
  first child; and left entries, the promoted entry, and right entries
  concatenate to the old entries with the new one inserted.
- `grow_root`: a one-entry branch over the old root and the new sibling.

The tree-level theorem `insertRec_wf` composes the two. `WF h isRoot lo hi
n` says: keys strictly increasing in every node, every key inside the
bounds the ancestors' separators impose, fill between `cap / 2` and `cap`
except at the root, and every leaf at height 0 (so all leaves at one
depth, which the Rust checker does not test). Insert preserves it at the
same height, or, when the root splits, one higher. Along the way the
branch theorems' `SepFits` is discharged: the split child's new separator
lies strictly inside that child's slot bounds, which are the neighbouring
separators.

`insertTree_toList` is the functional half: the new tree's `toList` is
`insertSorted k v` of the old one, and the returned value is the one
previously stored under `k` (present iff some value is returned). With
`insertTree_wf` this is the complete Phase 1 statement for insert.

Not modelled here: `range`, `get`, node memory, and sibling pointers.
Not yet proved: anything about `removeTree`.
