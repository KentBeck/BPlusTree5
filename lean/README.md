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
and compares digests and the final shape. At intervals the generator
also records the read paths: `get` of a random key, `first`, `last`,
and `range` with random bounds of every kind (unbounded, included,
excluded, in either order); the replayer answers each from `getTree`,
`firstTree`, `lastTree`, and `rangeTree` and compares the results, the
range as an item count plus a digest of the items. With
`cargo build --features delete_profile --example gen_trace` the generator
also reports how many leaf and branch borrows, merges, and root
collapses a trace exercised. Digests keep the traces small, so the large
configurations check every 10 to 100 operations. On a mismatch the Lean
side prints its shape and the script reruns the generator to print the
Rust shape at the same operation, with a token diff. CI runs it on every
push. FNV rather than a cryptographic hash because neither side is
adversarial and both implementations are ten lines that can be compared
by eye.

The delete and read models are both replayed and proved
(`Proofs/Delete.lean`, `Proofs/Read.lean`).

A shape match is stronger than the differential fuzz's map comparison:
it checks the same splits, the same separators, and the same leaf
contents, so it is the evidence that the model is the code and not just
a model of the same map. The range queries are also what ties the
model's one assumption about the leaf sibling chain to the Rust: the
model treats the chain as leaf order, the Rust checker verifies that at
every check line, and the ranges walk it.

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
| `keys[]` / `children[]` view of a branch | `Node.keysOf`, `Node.childrenOf`, `mkBranch` (`Model/Delete.lean`); `ChainA` (`Proofs/Delete.lean`) | `chain_iff_chainA`, `shape_of_arrays` |
| `leaf_remove` | `leafRemove` | `leafRemove_spec` |
| `plan_rebalance`, `child_len` | `planRebalance`, `childLen` | `planRebalance_spec`: what each choice knew, and that every sibling it measured is present |
| `rotate_leaf_right` / `rotate_leaf_left` / `merge_leaf_pair` | same names | `*_window`: repaired window well-formed, keys ordered, contents kept |
| `rotate_branch_right` / `rotate_branch_left` / `merge_branch_pair` | same names | `*_window`, likewise |
| `rebalance_leaf_child` / `rebalance_branch_child` / `fix_branch_child` | same names | `fixBranchChild_spec` |
| `remove_rec` | `removeRec` | `removeRec_spec` |
| `check_root_collapse`, `remove` | `checkRootCollapse`, `removeTree` | `removeTree_spec` |
| sorted-association-list removal (the spec) | `eraseSorted` (`Model/Spec.lean`) | |
| `leaf_for_key` / `child_for_key` | `leafForKey` (`Model/Read.lean`), with the entries of the leaves either side | `leafForKey_spec`: `toList = pre ++ leaf ++ post`, `pre < k < post` |
| `leaf_search`, `get` | `leafSearch`, `getTree` | `getTree_spec`: `get k = some v ↔ (k, v) ∈ toList` |
| `leftmost_leaf`, `first` / `rightmost_leaf`, `last` | `leftmostLeaf`, `firstTree` / `rightmostLeaf`, `lastTree` | `firstTree_spec`, `lastTree_spec`: head and last of `toList` |
| `Bound`, `cut_in_leaf`, `resolve_front`, `resolve_back`, `make_items`, `range`, `items` | `Bound` (`Model/Spec.lean`), `cutInLeaf`, `resolveFront`, `resolveBack`, `makeItems`, `rangeTree`, `itemsTree` | `rangeTree_spec`, `itemsTree_spec` |
| the entries between two bounds (the spec) | `rangeSorted` (`Model/Spec.lean`) | |
| `check_invariants_detailed`, `validate_node` / `validate_leaf` / `validate_branch`, `observe_leaf`, `ValidationState` | `checkInvariants`, `validateNode` / `validateLeaf` / `validateChildren`, `observeLeaf`, `VState` (`Model/Check.lean`) | `checkInvariants_iff`: accepts exactly `WF` trees with the right stored length |
| `BPlusTreeMap` with `entry_count`, `insert` / `remove` / `len` | `Map`, `Map.insert` / `Map.remove` / `Map.len` | `Map.insert_wf`, `Map.remove_wf`: the stored length stays `toList.length` |

Each Rust site a lemma justifies carries a `Lean:` line in its doc
comment naming the lemma; `grep -rn 'Lean:' src` lists them all.

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

What the delete theorems say, for a well-formed tree with both
capacities at least 4 (what `with_caps` enforces):

- `removeTree_spec`: if the key is absent nothing is returned and no
  entry has it; otherwise the returned value was stored under the key,
  the new tree's `toList` is `eraseSorted k` of the old, and the new root
  is well-formed at the same height or one lower.
- `removeRec_spec`, the inductive core: below the root, a node that lost
  an entry is `Shape` (well-formed except possibly one short of the
  minimum), and the underflow flag it reports is exactly "below the
  minimum".
- `fixBranchChild_spec`: given the original well-formed chain and the
  one-short child in its slot, `fix_branch_child` yields a shaped branch
  with the same or one fewer key, an exact underflow flag below the root,
  and the same entries. It dispatches on `planRebalance_spec` to six
  window lemmas, one per rotation and merge on each node kind, each
  stating that the repaired window is well-formed on both sides with the
  separator strictly between its neighbours.

The proofs settled the defensive arms `delete.rs` used to carry: under
`WF`, `fix_branch_child` never saw `len == 0` or a missing child, its
`child_idx.min(len)` clamp was the identity, `plan_rebalance` never
measured a missing sibling, and root collapse never met an empty leaf
child or ended with no survivor. Those arms are gone from the Rust; the
remaining `debug_assert!`s there name the preconditions the theorems
supply, and `check_root_collapse` is now the two-case function
`checkRootCollapse` mirrors.

What the read theorems say, for a well-formed tree (`Proofs/Read.lean`):

- `getTree_spec`: `get k` returns `some v` exactly when `(k, v)` is an
  entry. The descent lemma behind it, `leafForKey_spec`, splits `toList`
  into the entries before the reached leaf (all below `k`), the leaf, and
  the entries after it (all above `k`).
- `firstTree_spec`, `lastTree_spec`: `first` and `last` are the head and
  last entry of `toList`, with the leftmost and rightmost leaves nonempty
  whenever they are not the root.
- `rangeTree_spec`: `range` yields `rangeSorted start stop toList`, the
  entries between the bounds, for every combination of unbounded,
  included and excluded bounds, inverted ones included; `itemsTree_spec`
  is the unbounded case. The proof turns the model's positions into
  counts: on a sorted list the entries below the start bound form a
  prefix, and so do those within the end bound, so `resolve_front` lands
  on the first count, `resolve_back` on the second, and the slice
  between them is the spec. The only fact about the sibling chain the
  model relies on is that it lists the leaves in tree order, which the
  Rust invariant checker verifies.

What the checker theorem says (`Proofs/Check.lean`): `Model/Check.lean`
mirrors `check_invariants_detailed` arm for arm, threading its
`ValidationState` (entries counted, last key seen) and returning each
subtree's height, which `validate_branch` now requires every child to
agree on. `checkInvariants_iff` states that the checker accepts a tree
with stored length `count` exactly when the tree is `WF` at some height
and `count` is its number of entries. So the runtime checker, which the
fuzzers run after every mutation, tests precisely the invariant the
proofs preserve, `len()` included: `Map.insert_wf` and `Map.remove_wf`
carry `entry_count` along with the tree. Not mirrored: the two
sibling-pointer checks, which have no counterpart in a pointer-free
model; the replay's range queries are what exercises them.

## The heap model

`Model/Heap.lean` is the lower model the plan's Phase 2b calls for:
nodes in a store keyed by id (`Std.HashMap`), leaves carrying their
`prev` / `next` sibling ids, and every operation as explicit state
passing whose primitives fault (`none`) on a read, write or free of an
unallocated id or on a violated `debug_assert!` precondition. Node
contents reuse the tree model's functions; the heap model adds exactly
the plumbing the tree model abstracts away, at the sites the Rust uses
it: `alloc_leaf_block` / `alloc_branch_block`, `link_leaf_after` /
`unlink_leaf`, `free_emptied_leaf` / `free_emptied_branch`,
`empty_branch`, `replace_root`, `drop_subtree`. `rangeH` walks `next`
the way `Items::next` does instead of assuming the chain.

The replay runs it beside the tree model on every trace: no operation
or query may fault, return values must match the Rust, at every digest
line the store must abstract to the same tree and pass `heapInvOK`
(store = reachable nodes, no id twice, leaves chained in tree order),
chain-walking ranges must match the Rust, and dropping the tree at the
end must leave the store empty. Removing the old-next `prev` update in
`linkLeafAfter`, or the unlink in `freeEmptiedLeaf`, is caught at the
first split or the first merge.

What is proved (`Proofs/Heap.lean`):

- The store primitives: what a read sees after a write, an alloc or a
  free, and that every allocated id stays below `fresh`.
- `Linked h prev leaves next`, the doubly-linked chain, with its append
  law and `linkLeafAfter_spec`: exactly which three records change.
- `insertRecH_sim`, by induction on height: below a well-formed subtree
  with its leaves chained between two neighbours, `insertRecH` never
  faults, its result abstracts to the tree model's `insertRec`, the
  subtree's ids grow by exactly the ids allocated, the new leaves are
  chained between the same neighbours, and nothing outside the subtree
  changes except the successor leaf's `prev`.
- `insertH_sim`: given `HeapInv` (the root's bookkeeping, no id twice,
  every id below `fresh`, the store holding exactly the reachable ids,
  the leaves chained end to end, the stored count), `insert` on the heap
  model never faults, returns what the tree model returns, and
  re-establishes `HeapInv` for the tree model's new tree. For insert
  this is no use after free, no double free, no node leak, and
  sibling-chain integrity.

Not yet proved at this level: `remove` (modelled and replayed; its
simulation is next), the reads, and the value-token accounting.

Not modelled here: node memory itself, byte offsets, and aliasing, which
stay with Miri.
