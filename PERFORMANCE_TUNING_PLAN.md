# Performance Tuning Plan

Plan for closing the gaps between `BPlusTreeMap` and `std::collections::BTreeMap`.
Scope decision: **only larger capacities matter** — all benchmarking and tuning
targets capacities ≥ 64 (benches standardize on 128). Small-capacity configs
are used only by correctness tests, where they cheaply force split/merge/borrow
edge cases.

Measurements from 2026-08-26 (Linux x86-64, rustc 1.94.1, release profile,
1M `u64` keys unless noted). Reproduce with:

```
cargo run --release --example perf_probe   # capacity sweep 64-512 + gap probes
cargo run --release --bin bench_insert     # ins/get/del/mix/iter at cap=128
cargo run --release --bin bench_range      # range scans at cap=128
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
   no regression in the operations that already beat std (get, delete, mixed,
   iteration, sequential insert).

One change per commit, with before/after numbers in the commit message.

## Where we stand today (cap=128, 1M items)

Wins (keep these; do not regress):

| Operation                          | vs std::BTreeMap |
|------------------------------------|------------------|
| get (random)                       | 1.9× faster      |
| delete                             | 1.1× faster      |
| mixed 50/30/20 ins/get/del         | 1.2× faster      |
| full iteration (fwd and back)      | 3–5× faster      |
| full-tree range scan               | 1.25× faster     |
| sequential (sorted) insert         | 1.2× faster      |

Losses:

| Operation                              | vs std::BTreeMap                 |
|----------------------------------------|----------------------------------|
| `len()` / `is_empty()` (1M items)      | O(n) vs O(1) (~0.4 ms per call)  |
| random insert                          | 1.16× slower (bench_insert keys) to 1.6× slower (hash-scattered probe keys) |
| range scan, 100–10k items              | 1.6–2.1× slower                  |
| tiny cursor iterations (10 items)      | 1.16× slower                     |
| backward iteration, small tree (10k)   | 1.7× slower                      |

Capacity sweep (random insert, probe keys): 64 → 0.372s, 128 → 0.412s,
256 → 0.443s, 512 → 0.608s (std: 0.254s). Insert degrades with leaf size
because every insert memmoves half a leaf on average (~1KB at cap=128);
get/iteration prefer the larger nodes. That tension motivates item 5.

## P0 — asymptotic bugs (large wins, low risk)

### 1. `len()` / `is_empty()` are O(n) — decision pending

`lib.rs:209` computes `len()` by walking the entire leaf linked list
(~0.4 ms at 1M items; every other mainstream map is O(1)). The obvious fix —
a cached `len: usize` maintained by insert/remove/clear and cross-checked by
`check_invariants_detailed` so the fuzzer validates it on every mutation — is
one the author is reluctant to take on (a denormalization plus a maintenance
obligation in every mutation path).

The cost profile if it stays O(n): any caller that consults `len()` or
`is_empty()` per operation (capacity-eviction guards, drain-until-empty
loops, per-tick metrics) goes quadratic. Independent of that decision, do the
cheap decoupling: `items()` (`iterate.rs:275`) calls `len()` only to seed
`size_hint`, so today every full-iterator construction pays an O(n) walk
before the first element — make the iterator track position lazily instead,
and document `len()` as O(n) if it stays that way.

### 2. ~~`first()` and `last()` in O(log n)~~ — DONE

Fixed: `first()`/`last()` now read directly from the leftmost/rightmost leaf
instead of building/consuming a full `items()` iterator. Measured: 10k
first/last pairs went from 39s to 0.1ms — parity with std.

## P1 — the real per-op gaps

### 3. Range/cursor iterator: cache leaf state, precompute the end

`Items::next` (`iterate.rs:100-142`) re-carves the leaf and re-reads
`hdr.len` on every element, and for bounded ranges compares the key against
`end_bound` on every element; `range()` also clones both bound keys up front.
Restructure `ItemsInner::Lazy` to hold `cur_keys: *const K, cur_vals: *const
V, cur_idx, cur_end` refreshed only on leaf hop, and resolve the end bound
once at initialization to a concrete `(end_leaf, end_idx)` position so the
per-item check becomes an index/pointer compare. This targets the largest
steady-state loss: 1.6–2.1× on 100–10k-item range scans and 1.16× on tiny
cursor iterations. Full-scan iteration already wins, so verify no regression
there (its per-item cost is the same loop).

### 4. Random insert path

1.16–1.6× behind depending on key distribution. The macOS sample profile
(`profile.txt`) attributes the time to intra-leaf binary search + memmove
(`insert.rs:63`), branch descent (`insert.rs:65-66`), and split work. In
order of expected value:

a. **Stop zeroing vacated slots on split paths.** `insert.rs` (lines 133,
   140, 183, 192, 214, 222–241) and `move_kv_at` (`common.rs:94-95`)
   `write_bytes`-zero every slot they move out of. Node occupancy is defined
   solely by `hdr.len` — drop/iteration/search never read past it — so the
   memsets are pure overhead on every split and borrow. Remove them; the Miri
   gate exists precisely to prove nothing relied on the zeroing.

b. **Iterative descent with cached carve.** `insert_rec` (`insert.rs:60`)
   recurses and re-carves the branch on the way back up for split fixups.
   Convert to an iterative descent recording `(node, child_idx)` in a small
   fixed array (depth ≤ 4–5 at cap≥64 for any realistic n), then apply split
   fixups bottom-up. Removes call overhead and keeps layouts in registers.

c. **Branchless intra-node binary search.** `binary_search_keys`
   (`common.rs:70`) is `slice::binary_search`, which carries bounds checks and
   unpredictable branches. At cap=128 it runs 7 iterations per level. Replace
   with a branchless (conditional-move) search over the raw key array,
   optionally with a one-step prefetch of the child line. This hook serves
   every operation — re-verify get (currently 1.9× ahead) doesn't regress.

### 5. Decoupled leaf/branch capacities (within the large-cap regime)

`new(capacity)` (`lib.rs:184`) uses one number for both layouts, but the
sweep shows the tension: insert cost rises with leaf size (memmove of half a
leaf per insert), while descent depth falls with branch fan-out. A config
like leaf=64 / branch=256 plausibly beats uniform 128 on inserts without
giving up lookup depth. Add `with_caps(leaf_cap, branch_cap)`, grid-measure
{64,128,256}×{128,256,512}, and set `new()`'s internal split to the winner.
No configuration below 64 is in scope.

### 6. Node allocation pooling (churn workloads)

Every split allocates via `alloc::alloc` and every merge deallocates
(`node_alloc.rs`). A per-tree free list of node blocks (leaf and branch
blocks are fixed-size, so this is a push/pop of raw pointers) removes malloc
from the split/merge path. Helps insert and delete-heavy churn. Keep it
bounded (e.g. 64 pooled nodes per kind) so memory doesn't grow monotonically.

## P2 — smaller cleanups

### 7. Iterative, cached `next_back`

`next_back` (`iterate.rs:221`) recurses on leaf transitions and re-carves per
element. Apply the same loop + cached-leaf treatment as item 3. Fixes the
1.7× backward-iteration gap on small trees (large trees already win).

### 8. Make `items_range()` lazy

`iterate.rs:330-340` still collects into a `Vec` (marked TODO). Route it
through the same lazy machinery as `range()`.

### 9. Keep benchmarks honest about capacity

Done in this change: `bench_insert` now defaults to cap=128 (was 16), and
`bench_range` plus the range/asm profile binaries use `new(128)` (was
`with_cache_lines(2, 2)` ≈ 6-entry nodes, which made range look 2.5–3×
worse than the tree actually is). Any future benchmark must use cap ≥ 64.

## Sequencing

1. Item 1's decoupling first (item 2 is done): de-noises any benchmark that
   constructs full iterators, which currently pay the O(n) `len()` walk.
2. Item 3 against the range/cursor probes in `perf_probe`.
3. Items 4a–4c as separate commits against the random-insert sweep.
4. Items 5–6 next if insert is still behind; 7–8 as cleanups.

Stop when random insert and mid-size range scans are within ~1.1× of std or
ahead; the structure (contiguous fixed-size nodes, linked leaves) should keep
its existing get/mixed/iteration advantages throughout.
