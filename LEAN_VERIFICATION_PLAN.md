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
| `insert k v` | `toList (insert k v t) = insertSorted k v (toList t)`; returns the old value at `k` |
| `remove k` | `toList (remove k t) = (toList t).filter (·.1 ≠ k)`; returns the value at `k` |
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

- `leaf_insert_or_split`: `left_count = (len + 1) / 2`, `left_keep`
  adjusted by whether the insert lands left, new separator is the right
  leaf's first key.
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
- `check_root_collapse` / `consolidate_root_children` / `replace_root`.

The Rust `insert` descends iteratively with a recorded path and unwinds
splits bottom-up. The model's `insert` is a direct recursion (the shape
`insert_rec` had before commit 1f54f7d). Either keep that gap and prove
one lemma that the path-array loop computes the recursive fold, or make
the Rust recursive again (see "Open decisions").

Keeping names aligned is what makes the "the Lean matches the Rust" step
reviewable by eye; do not refactor the model into something prettier
than the code until the code has been refactored to match.

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
   - leaf split: `(cap + 1) / 2 ≥ cap / 2` and
     `cap + 1 - (cap + 1) / 2 ≥ cap / 2`, so both halves meet the minimum;
   - branch split: after promotion both sides hold `≥ cap / 2` keys.
3. `range` bound resolution: `cut_in_leaf` with `after_equal`, the
   hop to the next/previous leaf when the cut sits at an edge, and the
   inverted-bounds check in `make_items`. Double-ended iteration:
   `next` and `next_back` together enumerate exactly the filtered list.
4. `remove` with the four repairs and root collapse. Key lemmas:
   - underflow means exactly `min - 1` (a child at `≥ min` loses one);
   - borrow: donor at `> min` stays `≥ min` after giving one, receiver
     reaches `min`;
   - leaf merge: `(min - 1) + min ≤ cap`;
   - branch merge: `(min - 1) + 1 + min ≤ cap` (tight for even `cap`);
   - a merge removes one parent entry, so the parent underflows iff it
     was at `min`, which is what `fix_branch_child` reports;
   - `check_root_collapse` with `len ≤ 2` after a removal yields a WF
     tree with the same `toList`.

## Phase 5 — tie it back to the Rust

1. Compile the model (`lake exe`) and replay the differential fuzz op
   traces through it, comparing `toList` after every op with the Rust
   tree's `items()`. Deterministic seeds make this a fixed test, not a
   fuzz run.
2. Cite proofs from the code: a one-line comment at each Rust site that
   a lemma justifies (split arithmetic, merge fit, the depth bound).
3. Add the uniform-depth check to `check_invariants_detailed` (cheap:
   return depth from `validate_node` and compare across children).

## Concrete findings the plan already produced

Reading the code for this plan surfaced items that the proof will force
a decision on; each is either a theorem or a code change.

1. **`MAX_DEPTH = 64` is guarded only by a `debug_assert`.** In release,
   a deeper tree writes past the path array. Non-root branches hold
   `≥ 2` keys, so leaf count grows as `3^(depth - 2)`, and depth 64 is
   unreachable for any addressable tree. Prove
   `depth t ≤ log₃ (leafCount t) + 2` and cite it at the array.
2. **Defensive paths with unclear reachability.** `fix_branch_child`
   clamps `child_idx` to `len` and tolerates a null child;
   `plan_rebalance` and `child_len` treat a null sibling as length 0;
   `absorb_root_child` handles an empty leaf under a branch root. My
   reading is that no live tree reaches these states. The model must
   either prove that and the Rust deletes the branches, or admit the
   states into `WF`. Either outcome improves the code.
3. **The runtime checker never verifies uniform leaf depth.** The model
   proves it; adding the check to the Rust validator is Phase 5.3.
4. **`min_branch_len`'s `cap <= 2` arm is dead** since `with_caps`
   rejects capacities below 4. Delete it.

## Open decisions

- **Iterative vs recursive insert.** Recursive matches `remove_rec` and
  the model one-to-one and removes the fixed path array. Iterative was
  measured at 13.6% fewer instructions but wall-clock neutral (commit
  1f54f7d). Recommendation: recursive, decided on symmetry rather than
  proof needs, with an A/B measurement in the commit.
- **Mathlib or plain Std.** Mathlib gives `LinearOrder` and sorted-list
  lemmas for free; Std keeps the dependency light and matches
  `Std.TreeMap`'s proofs. Start with Std and add Mathlib only if the
  list lemmas become the bottleneck.

## Effort

Phases 1–3 plus `get` and `insert`: about two weeks for someone fluent in
Lean. `remove` is the bulk of the work and can double that. `range` sits
between. Nothing here blocks on Rust changes except the optional insert
decision.

## Layout

```
lean/
  lakefile.lean
  BPlusTree/Model.lean      -- Node, Tree, toList, the ported operations
  BPlusTree/WF.lean         -- the invariant, checker equivalence
  BPlusTree/Insert.lean     -- Phase 4.2
  BPlusTree/Range.lean      -- Phase 4.3
  BPlusTree/Remove.lean     -- Phase 4.4
  BPlusTree/Depth.lean      -- finding 1
  Replay/Main.lean          -- Phase 5.1 executable
```
