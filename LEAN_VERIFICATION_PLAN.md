# Lean Verification Plan

Plan for proving this B+ tree correct in Lean 4. The proof targets the
algorithm, not the raw-memory code: no Rust-to-Lean pipeline handles the
`unsafe` pointer manipulation this crate is built from, so the split of
responsibilities is

| Concern | Tool |
|---|---|
| Split points, separator choice, borrow/merge policy, root grow/collapse, range bounds, `len` | Lean model proof (this plan) |
| Memory safety: double frees, leaks, use-after-free, sibling-chain corruption, `ptr::copy` overlap | Miri + drop-tracking differential fuzz (already in CI) |
| The Lean model actually matches the Rust | One-to-one function names and arithmetic, plus replaying fuzz traces through the compiled model |

A logic bug in any of the first row's items is a silent data bug that Miri
never flags and the fuzzer finds only if a seed happens to hit it. That is
the gap the proof closes.

## What the proof will not cover

Every function in `src/` works on raw blocks through `ptr::copy`,
`ptr::read`, and carved offsets. Aeneas, the Rust-to-Lean translator,
accepts only a safe subset with no raw pointers. Verifying the memory
manipulation itself would mean Verus (permission-token reasoning about
raw pointers) and a rewrite in its dialect; that is out of scope here.
Lean has no production separation-logic framework for Rust.

Two lawfulness assumptions carry over from `std::collections::BTreeMap`:
`K: Ord` is a total order, and `K::clone` returns an equal key (leaf
separators are clones of data keys).

## Correctness gate

Unchanged from the other plans: `cargo test`, the extended differential
fuzz, and Miri stay the gate for every Rust change. The proof adds a
second gate for the model: `lake build` with no `sorry`.

## Phase 1 — pin the spec

The abstract state is a sorted association list from keys to values,
obtained by `toList`. Every public operation gets a theorem against it:

| Rust | Spec theorem |
|---|---|
| `insert k v` | ~~`toList (insert k v t) = insertSorted k v (toList t)`; returns the old value at `k`~~ — DONE |
| `remove k` | ~~`toList (remove k t) = eraseSorted k (toList t)`; returns the value at `k`~~ — DONE |
| `get k` | `get k t = (toList t).lookup k` |
| `range lo hi` | `(range lo hi t).toList = (toList t).filter (inBounds lo hi)`, including excluded and inverted bounds |
| `first` / `last` | head and last of `toList` |
| `len` | `length (toList t)`; the stored `entry_count` equals it |
| `clear`, `is_empty` | trivial from the above |

Precedent: Lean's own `Std.TreeMap` is verified in exactly this style
(operations on a model tree, a `WF` predicate, lemmas stated via
`toList`). Copy its structure and lemma naming.

## Phase 2 — the model tree

```lean
inductive Node (K V : Type)
  | leaf   (kvs : List (K × V))
  | branch (c0 : Node K V) (entries : List (K × Node K V))

structure Tree (K V) where
  root      : Option (Node K V)
  count     : Nat
  leafCap   : Nat   -- ≥ 4
  branchCap : Nat   -- ≥ 4
```

A branch is "first child plus (separator, child) entries", which is the
entry view `branch_insert_and_split` already uses. Port each Rust
function one-to-one, same name, same arithmetic:

- `split_leaf` then the ordinary insert: the left half keeps
  `(len + 1) / 2` items, the separator is the right half's first key, and
  the new entry goes to whichever half the separator routes it to.
- `branch_insert_and_split`: same `left_count`/`left_keep`, then promote
  the right node's first entry; its key goes up, its child becomes the
  right node's `c0`.
- `plan_rebalance`: borrow from left if it holds more than `min`, else
  from right, else merge with left, else with right.
- `rotate_leaf_*` re-derive the separator from data; `rotate_branch_*`
  pass it through. `merge_leaf_into` drops the separator;
  `merge_branch_into` moves it down.
- `remove_rec` returns the value and an "underflowed" flag;
  `fix_branch_child` turns a child merge into a parent underflow.
- `check_root_collapse` (one child hands over; two leaves that fit merge)
  / `replace_root`.

`insert_rec` and `remove_rec` are both direct recursions, so the model's
`insert` and `remove` port them one-to-one with no bridging lemma.

Keeping names aligned is what makes the "the Lean matches the Rust" step
reviewable by eye; do not refactor the model into something prettier
than the code until the code has been refactored to match.

**Status:** `lean/BPlusTree/Model/Leaf.lean`, `Model/Branch.lean`, and
`Model/Tree.lean` port `insert.rs` in full (`leafInsertOrSplit`,
`branchApplySplit`, `branchInsertAndSplit`, `growRoot`, `insertRec`,
`insertTree`) and define `Node.toList`. `Model/Delete.lean` ports
`delete.rs` in full (`leafRemove`, `planRebalance`, the two leaf and two
branch rotations, the two merges, `fixBranchChild`, `removeRec`,
`checkRootCollapse`, `removeTree`), replayed and proved. Range and get
are not started.

## Phase 2b — the heap model (memory safety)

The list model has no allocation, so "no double free" is vacuous there.
A second, lower model puts nodes in a store keyed by node identity and
runs the operations in a state monad whose primitives can fault:

```lean
abbrev NodeId := Nat
inductive NodeRec (K V)
  | leaf   (kvs : List (K × V)) (prev next : Option NodeId)
  | branch (keys : List K) (children : List NodeId)
structure Heap (K V) where
  nodes : Finmap NodeId (NodeRec K V)
  fresh : NodeId
abbrev M K V := StateT (Heap K V) (Except MemFault)
-- read / write / free fault on an unallocated id; alloc never faults
```

Its primitives are the Rust's: `alloc_leaf_block` / `free_leaf_block`,
`free_emptied_leaf` with its length-zero precondition, `link_leaf_after`
/ `unlink_leaf`, `drop_subtree` versus the incremental frees. The
theorems it adds:

- **No use after free, no double free:** on a well-formed heap every
  operation returns `Except.ok`. A dangling read or a second free is the
  only way to fault, so success on all inputs is the proof.
- **No node leak:** after every operation the store's domain equals the
  nodes reachable from the root.
- **No double drop, no lost `K`/`V`:** values as unique tokens; each
  token appears exactly once across the store, the return value, and the
  explicitly dropped set. This is the fuzz suite's `Tracked` canary,
  proven rather than sampled, and it covers `rotate_leaf_*` dropping the
  old separator, `merge_leaf_pair` dropping one, and `replace_root`
  emptying the root before freeing it.
- **Sibling chain integrity:** `prev`/`next` are in the model, so the
  doubly-linked invariant `link_leaf_after` and `unlink_leaf` maintain is
  provable. The list model cannot state it.

The heap model refines the list model by simulation; the list model
refines the spec as before. Byte-level concerns (offsets in `layout.rs`,
`ptr::copy` overlap, uninitialised reads, aliasing) stay with Miri.
Verifying the Rust source itself for memory safety would be Kani
(bounded model checking of unsafe Rust), a separate item that
complements this plan.

## Phase 3 — the invariant

`WF t` is the conjunction of, per node:

1. **Ordered**: keys strictly increasing within a node.
2. **Bounded**: every key in child `i` is `≥` separator `i-1` and `<`
   separator `i` (the exact bounds `validate_branch` passes down).
3. **Fill**: leaf `len ≤ leafCap`, branch `len ≤ branchCap`; non-root
   leaf `len ≥ leafCap / 2`; non-root branch `len ≥ branchCap / 2`. The
   root is exempt below; a root leaf may be empty.
4. **Uniform depth**: every leaf sits at the same depth.
5. **Count**: `count = length (toList t)`.

**Status:** `WF` is defined in `lean/BPlusTree/Proofs/Tree.lean` with
items 1–4 (indexed by height, so item 4 is built in). Item 5 is a
one-line addition now that `toList` exists but is not yet part of `WF`.
The checker equivalence below is not started.

Then prove `check_invariants_detailed t = ok ↔ WF t` (minus item 4, which
the Rust checker does not test; see below). That ties the proof to the
fuzzer, which runs the checker after every mutation. The leaf sibling
chain is a pointer artifact with no model counterpart; the fuzzer and
Miri own it.

## Phase 4 — preservation and refinement

In this order, because difficulty rises sharply:

1. `get`, `first`, `last`, `contains_key` — read-only, warm-up.
2. `insert` including root growth. Key lemmas, all `omega` once the
   model is right, for every `cap ≥ 4`:
   - ~~leaf split~~ — DONE (`lean/BPlusTree/Proofs/Leaf.lean`).
     The Rust now splits a full leaf first and then runs the ordinary
     insert on the half the separator routes the key to, so the model's
     `leafSplit` is a `take`/`drop` at `(len + 1) / 2` and the old
     `left_keep` case analysis (and its equivalence theorem) are gone.
     `leafInsertOrSplit_split` gives both halves sorted with
     `cap / 2 ≤ len ≤ cap`, the separator bounding both sides, and the
     halves concatenating to the inserted list; `leafInsertOrSplit_noSplit`
     covers the absorb and overwrite arms. The split theorem needs
     `cap ≥ 2` (a one-item leaf would split into an empty right half,
     and the Rust reads its first key); `with_caps` enforces 4.
   - ~~branch split~~ — DONE (`lean/BPlusTree/Proofs/Branch.lean`).
     `cutInsert_eq` shows the `left_keep` arithmetic equals "insert, then
     cut at `(len + 1) / 2`"; `branchApplySplit_split` gives both halves
     sorted with `cap / 2 ≤ len ≤ cap` for every `cap ≥ 1`, the promoted
     key strictly between them, the first child kept on the left, and the
     entries preserved as a sequence. `branchApplySplit_noSplit` covers
     the absorb arm and `growRoot_spec` root growth.
   - ~~whole-tree insert~~ — DONE (`lean/BPlusTree/Proofs/Tree.lean`).
     `insertRec_wf`, by induction on height: a `NoSplit` result is `WF`
     at the same height and bounds; a `Split` result is two `WF`
     non-root halves around a separator strictly inside the bounds. That
     strictness is what discharges the branch theorems' `SepFits` at the
     parent. `insertTree_wf` adds root growth.
   - ~~`toList` refinement~~ — DONE. `Node.toList` is the leaves' entries
     left to right; `insertTree_toList` gives
     `toList (insert k v t) = insertSorted k v (toList t)` and the
     returned old value. Insert is complete at the model level.
3. `range` bound resolution: `cut_in_leaf` with `after_equal`, the
   hop to the next/previous leaf when the cut sits at an edge, and the
   inverted-bounds check in `make_items`. Double-ended iteration:
   `next` and `next_back` together enumerate exactly the filtered list.
4. ~~`remove` with the four repairs and root collapse~~ — DONE
   (`lean/BPlusTree/Proofs/Delete.lean`, about 1,650 lines).
   `removeTree_spec`: the removed pair was stored, `toList` becomes
   `eraseSorted k` of the old, and the root stays well-formed at the same
   height or one lower. The listed lemmas are all there: the deficit is
   exactly one (`Shape` plus the length facts in `removeRec_spec`), each
   borrow and merge is a window lemma with the fill arithmetic, a merge
   drops one parent key and the flag is exact below the root
   (`fixBranchChild_spec`), and root collapse is handled case by case.
   Proved in the array view `delete.rs` uses (`ChainA`), with window
   lemmas to swap two adjacent children in a chain.

## Phase 5 — tie it back to the Rust

1. ~~Compile the model (`lake exe`) and replay op traces through it~~ —
   DONE for insert (`lean/replay.sh`, `examples/gen_trace.rs`,
   `lean/Replay/Main.lean`). The comparison is on the tree *shape*
   (`dump_shape`: every leaf's entries and every separator, nested), not
   just the map, across eight capacity/key-space configurations. Checks
   are 64-bit FNV-1a digests of the shape (small traces, frequent
   checks) with one full shape at the end; on a mismatch the driver
   reruns the generator to print both shapes at the failing op. CI runs
   it on every push. Traces now mix inserts and removes (`I k v old`,
   `R k res`, return values checked too) and end with a drain to the
   empty tree, so every rebalance and root-collapse path in `delete.rs`
   is compared against the model: about 150k ops and 30k checks in nine
   seconds. Add `G k` when the model gains `get`.
2. Cite proofs from the code: a one-line comment at each Rust site that
   a lemma justifies (split arithmetic, merge fit, the depth bound).
3. Add the uniform-depth check to `check_invariants_detailed` (cheap:
   return depth from `validate_node` and compare across children).

## Concrete findings the plan already produced

Reading the code for this plan surfaced items that the proof will force
a decision on; each is either a theorem or a code change.

1. **Depth bound.** Insert used to record its descent in a fixed
   64-slot array guarded only by a `debug_assert`; a deeper tree would
   have written past it in release. Insert is recursive again, so the
   array is gone, but the theorem is still worth having: non-root
   branches hold `≥ 2` keys, so leaf count grows as `3^(depth - 2)`, and
   `depth t ≤ log₃ (leafCount t) + 2` bounds the recursion depth of both
   `insert_rec` and `remove_rec`.
2. **Defensive paths with unclear reachability** — SETTLED by the delete
   proofs: under `WF`, `fix_branch_child` never sees `len == 0` or a
   missing child and its `child_idx.min(len)` clamp is the identity;
   `plan_rebalance` never measures a missing sibling; root collapse never
   meets an empty leaf child or ends with no survivor. The Rust arms are
   now removed (`fix_branch_child` asserts its preconditions,
   `check_root_collapse` is a two-case function, the `RootChild` enum and
   `consolidate_root_children` / `absorb_root_child` are gone) and the
   model was simplified in step so it still mirrors the code. Still
   `Option`-shaped for a null child that cannot occur: `child_for_key` in
   `common.rs`, shared with the unmodelled lookup paths.
3. **The runtime checker never verifies uniform leaf depth.** The model
   proves it; adding the check to the Rust validator is Phase 5.3.
4. **`min_branch_len`'s `cap <= 2` arm is dead** since `with_caps`
   rejects capacities below 4. Delete it.
5. **Branch split cannot be split-first.** Leaves can split before
   inserting because no key leaves the leaf. A branch promotes one key,
   so a full branch with an even `cap` splits into `cap / 2 - 1` and
   `cap / 2` keys, and the smaller side is below `min_branch_len` unless
   the incoming entry happens to land there. The fused arithmetic in
   `branch_insert_and_split` (choose the promotion point knowing where
   the new entry goes) is what keeps both sides at `≥ cap / 2`. The
   theorem to prove is that fused arithmetic, not a simpler replacement.

## Open decisions

- ~~**Iterative vs recursive insert.**~~ — DECIDED: recursive. It
  matches `remove_rec` and the model one-to-one and removes the fixed
  path array. Measured on the switch back (cachegrind, 200k
  hash-scattered inserts at cap 128): 7.3% more instructions
  (89.1M → 95.6M), identical D1 and LL misses, and an interleaved
  wall-clock A/B of 2M inserts within noise (medians 0.587s vs 0.589s).
  Same conclusion as the original switch in the other direction: insert
  is miss-bound, and the instruction count does not reach the clock.
- **Mathlib or plain Std.** Mathlib gives `LinearOrder` and sorted-list
  lemmas for free; Std keeps the dependency light and matches
  `Std.TreeMap`'s proofs. Start with Std and add Mathlib only if the
  list lemmas become the bottleneck.

## Effort

Phases 1–3 plus `get` and `insert`: about two weeks for someone fluent in
Lean. `remove` is the bulk of the work and can double that. `range` sits
between. Phase 2b roughly doubles the total again: two to three months
for both levels. Nothing here blocks on Rust changes.

## Layout

```
lean/
  lakefile.toml, lean-toolchain, README.md (correspondence table)
  BPlusTree/Model/Leaf.lean     -- leaf half of insert.rs (done)
  BPlusTree/Model/Branch.lean   -- branch half, root growth (done)
  BPlusTree/Model/Spec.lean     -- insertSorted, the abstract spec (done)
  BPlusTree/Model/Tree.lean     -- Node, toList, insertRec, insertTree (done)
  BPlusTree/Model/Delete.lean   -- delete.rs, node by node (done)
  BPlusTree/Model/Heap.lean     -- Phase 2b
  BPlusTree/Proofs/Leaf.lean    -- leaf split and insert theorems (done)
  BPlusTree/Proofs/Branch.lean  -- branch split, apply-split, root growth (done)
  BPlusTree/Proofs/Spec.lean    -- insertSorted lemmas, leaf equations (done)
  BPlusTree/Proofs/Tree.lean    -- WF, chains, insert preserves WF and
                                --   refines insertSorted (done)
  BPlusTree/Proofs/Delete.lean  -- array-view chains, window repairs,
                                --   fixBranchChild, removeRec, removeTree (done)
  BPlusTree/Proofs/WF.lean      -- checker equivalence
  BPlusTree/Proofs/Range.lean   -- Phase 4.3
  BPlusTree/Proofs/Depth.lean   -- finding 1
  BPlusTree/Proofs/Heap.lean    -- Phase 2b theorems
  Replay/Main.lean, replay.sh   -- Phase 5.1 shape replay (done)
```
