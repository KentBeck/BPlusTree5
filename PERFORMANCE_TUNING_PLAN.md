# Performance Tuning Plan

Plan for closing the gaps between `BPlusTreeMap` and `std::collections::BTreeMap`,
grounded in measurements taken on 2026-08-26 (Linux x86-64, rustc 1.94.1, release
profile, 1M `u64` keys unless noted). Reproduce with:

```
cargo run --release --example perf_probe
cargo run --release --bin bench_insert   # etc.
```

## Correctness gate (applies to every change below)

Every tuning change must pass, in order, before it lands:

1. `cargo test` — full suite (~250 tests, includes the differential fuzz tests
   in `tests/differential_fuzz.rs`, which check tree invariants after every
   mutation and track live values to catch double-frees and leaks).
2. `cargo test --release --test differential_fuzz -- --ignored` — extended
   fuzz: ~3.2M ops across 160 seed/capacity configurations.
3. `cargo +nightly miri test --test differential_fuzz` and
   `cargo +nightly miri test --test drop_and_clear_tests -- --include-ignored`
   — undefined-behavior check on the raw-memory paths.
4. `cargo run --release --example perf_probe` — confirm the intended win and
   no regression in the operations that already beat std (get, delete, bulk
   iteration, sequential insert).

One change per commit, with before/after numbers in the commit message.

## Where we stand today

Wins (keep these; do not regress):

| Operation (cap=128, 1M items)     | vs std::BTreeMap |
|-----------------------------------|------------------|
| get (random)                      | 1.4–2.7× faster  |
| delete                            | ~1.1× faster     |
| full iteration fwd/back (≥100k)   | 2–3.6× faster    |
| sequential (sorted) insert        | 1.2× faster      |

Losses:

| Operation                              | vs std::BTreeMap        |
|----------------------------------------|-------------------------|
| `first()` / `last()` (1M items)        | ~400,000× slower        |
| `len()` / `is_empty()` (1M items)      | O(n) vs O(1) (~0.4 ms/call) |
| random insert (best cap=16)            | 1.35× slower (0.27s vs 0.20s) |
| random insert (cap=128)                | 1.65× slower            |
| range scan, 100 items × 100k queries   | 1.3× slower             |
| tiny cursor iterations (10 items)      | 1.16× slower            |
| backward iteration, small tree (10k)   | 1.7× slower             |
| mixed insert/get/delete (cap=16)       | 1.6× slower             |

Note: `bench_range`'s dramatic 2.5–3× losses come from `with_cache_lines(2, 2)`
(128-byte nodes → ~6-entry leaves, deep tree). At cap=128 the same workload is
only 1.3× behind. Node-size choice dominates; see item 7.

## P0 — asymptotic bugs (large wins, low risk)

### 1. Cache the length: make `len()` / `is_empty()` O(1)

`lib.rs:209` computes `len()` by walking the entire leaf linked list. Add a
`len: usize` field to `BPlusTreeMap`, maintained in `insert` (+1 on new key),
`remove` (−1 on hit), `clear`/`Drop` (reset). `items()` (`iterate.rs:275`)
already calls `len()`, so every full-iterator construction currently pays an
O(n) walk before yielding the first element — this fix also repairs that.

Verification: add a check to `check_invariants_detailed` that the cached value
equals the walked total, so the fuzz suite validates the counter on every
mutation for free.

### 2. `first()` and `last()` in O(log n)

`iterate.rs:369-375`: `first()` builds a full `items()` iterator (O(n) via
`len()`), and `last()` consumes an entire iterator with `.last()` — O(n) even
after fix 1. Replace with direct reads: `leftmost_leaf()` → element 0;
`rightmost_leaf()` → element `len-1`. Both helpers already exist in
`common.rs`. Measured today: 10k first/last pairs take 38.4s vs std's 0.1ms.

## P1 — random insert (1.35–1.65× behind)

The macOS sample profile (`profile.txt`) and the capacity sweep both point at
per-level search + leaf memmove + descent overhead. Attack in this order,
measuring after each step:

### 3. Stop zeroing vacated slots on the split paths

`insert.rs` (lines 133, 140, 183, 192, 214, 222–241) and `move_kv_at`
(`common.rs:94-95`) `write_bytes`-zero every slot they move out of. Node
occupancy is defined solely by `hdr.len` — drop/iteration/search never read
past it — so the memsets are pure overhead on every split and every borrow.
Remove them. This is exactly the kind of change the Miri gate exists for: if
any code path actually relies on the zeroing, Miri and the drop-tracking fuzz
will catch it.

### 4. Iterative descent with cached carve

`insert_rec` (`insert.rs:60`) recurses, re-carving the branch on the way back
up to do the child-split fixup. Convert to an iterative descent that records
`(node, child_idx)` in a small fixed array (depth ≤ ~12 for u16 caps), then
applies split fixups bottom-up. Removes call overhead and lets the compiler
keep layouts in registers. Apply the same shape to `remove` afterwards if it
wins (delete currently beats std, so only port it if the win is clear).

### 5. Adaptive intra-node search

`binary_search_keys` (`common.rs:70`) is a plain `slice::binary_search`. std's
B-tree deliberately uses branch-free/linear search inside nodes because at
node sizes ≤ ~16 the branch mispredictions of binary search cost more than the
extra comparisons, and a linear scan over a contiguous `u64` array
auto-vectorizes. Implement: linear scan when `len ≤ 16` (or when
`size_of::<K>() ≤ 16`), binary search above. This is the single hook that
touches every operation (get already wins — re-verify it after this change).

### 6. Decouple leaf capacity from branch capacity

`new(capacity)` (`lib.rs:184`) uses one number for both layouts. The sweep
shows random insert is best at cap=16 (memmove cost grows with leaf size) while
get/iteration are best at cap=128 (shallower tree, better locality). A larger
branch fan-out with a moderate leaf (e.g. leaf 16–32, branch 64–128) should
get both: shallow descent, small shifts. Add `with_caps(leaf_cap, branch_cap)`,
re-run the sweep as a 2-D grid, and pick better defaults for `new()`.

### 7. Revisit default node byte-budgets

`with_cache_lines(2, 2)` (used by `bench_range`) yields ~6-entry nodes and is
2.5–3× behind std; the same code at cap=128 is within 1.3×. Benchmark the
byte-budget constructor at 4/8/16 cache lines and document a recommended
default (likely ≥ 8 lines for leaves). Cheap: measurement + docs, no tree code.

### 8. Node allocation pooling (churn workloads)

Every split allocates via `alloc::alloc` and every merge deallocates
(`node_alloc.rs`). A per-tree free list of node blocks (leaf and branch blocks
are fixed-size, so this is a push/pop of raw pointers) removes malloc from the
split/merge hot path. Expected to help the mixed workload (1.6× behind) and
delete-heavy phases most. Keep it optional/simple: cap the pool (e.g. 64
nodes) so memory doesn't grow monotonically.

## P2 — iterator fine-tuning (1.15–1.7× gaps)

### 9. Cache leaf state in the iterator; precompute the range end

`Items::next` (`iterate.rs:100-142`) re-carves the leaf and re-reads
`hdr.len` on every element, and for bounded ranges compares the key against
`end_bound` on every element. Restructure `ItemsInner::Lazy` to hold
`cur_keys: *const K, cur_vals: *const V, cur_end: usize` refreshed only on
leaf hop, and resolve the end bound once at initialization to a concrete
`(end_leaf, end_idx)` position so the per-item check becomes an index/pointer
compare. Targets the 1.3× range-scan and 1.16× cursor gaps. (`clone_bound`'s
per-`range()` key clones also disappear for the common case.)

### 10. Iterative, cached `next_back`

`next_back` (`iterate.rs:221`) recurses on leaf transitions and re-carves per
element. Apply the same loop + cached-leaf treatment as `next`. Fixes the
1.7× backward-iteration gap on small trees.

### 11. Make `items_range()` lazy

`iterate.rs:330-340` still collects into a `Vec` (marked TODO). Route it
through the same lazy machinery as `range()`.

## Sequencing

1. Items 1–2 first: trivial, huge, and they de-noise every later benchmark
   (any bench touching `len()`/`items()` currently measures the O(n) walk).
2. Items 3–5 as separate commits against `perf_probe`'s random-insert sweep.
3. Item 9 against the range/cursor probes.
4. Items 6–8, 10–11 in whatever order the remaining gaps justify.

Stop when random insert, range scan, and mixed are within ~1.1× of std or
ahead; the structure (contiguous fixed-size nodes, linked leaves) should keep
its existing get/iteration advantages throughout.
