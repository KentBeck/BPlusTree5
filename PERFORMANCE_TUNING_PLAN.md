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

**Measurement note:** this environment has a ±10–15% run-to-run noise floor
(std's own numbers swing that much between runs). Never compare numbers from
separate runs. To claim a win, build the before and after binaries side by
side (`git worktree add` the parent commit) and interleave several rounds of
both; the effect must clear the interleaved spread.

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
| `len()` (1M items)                     | O(n) vs O(1) (~0.4 ms per call)  |
| random insert                          | parity (bench_insert keys) to 1.4× slower (hash-scattered probe keys) |
| single-item range seek / tiny cursors  | 1.1–1.2× slower (descent-bound) |

Capacity sweep (random insert, probe keys): 64 → 0.372s, 128 → 0.412s,
256 → 0.443s, 512 → 0.608s (std: 0.254s). Insert degrades with leaf size
because every insert memmoves half a leaf on average (~1KB at cap=128);
get/iteration prefer the larger nodes. That tension motivates item 5.

## P0 — asymptotic bugs (large wins, low risk)

### 1. `len()` is O(n) — decision pending (`is_empty()` now O(1))

`lib.rs` computes `len()` by walking the entire leaf linked list
(~0.4 ms at 1M items; every other mainstream map is O(1)). `is_empty()` no
longer pays this: the invariants (a branch root has children; non-root
leaves are never empty) mean emptiness is decidable from the root header
alone, so it is now O(1) and checked against std::BTreeMap by the fuzzer. The obvious fix —
a cached `len: usize` maintained by insert/remove/clear and cross-checked by
`check_invariants_detailed` so the fuzzer validates it on every mutation — is
one the author is reluctant to take on (a denormalization plus a maintenance
obligation in every mutation path).

The cost profile if it stays O(n): any caller that consults `len()` per
operation (capacity-eviction guards, per-tick metrics) goes quadratic;
drain-until-empty loops are fine now that `is_empty()` is O(1). Independent of that decision, do the
cheap decoupling: `items()` (`iterate.rs:275`) calls `len()` only to seed
`size_hint`, so today every full-iterator construction pays an O(n) walk
before the first element — make the iterator track position lazily instead,
and document `len()` as O(n) if it stays that way.

### 2. ~~`first()` and `last()` in O(log n)~~ — DONE

Fixed: `first()`/`last()` now read directly from the leftmost/rightmost leaf
instead of building/consuming a full `items()` iterator. Measured: 10k
first/last pairs went from 39s to 0.1ms — parity with std.

## P1 — the real per-op gaps

### 3. ~~Range/cursor iterator: cache leaf state, precompute the end~~ — DONE

The iterator now resolves both bounds to concrete (leaf, index) positions at
construction and caches the current leaf's key/value pointers, so per-item
work is an index compare and two pointer reads — no key comparisons, no
re-carving, no bound-key clones. `items()` no longer calls the O(n) `len()`
(the item-1 decoupling), `items_range()` is lazy instead of collecting a Vec
(old item 8), and `next_back` got the same treatment (old item 7).

The rewrite also fixed two latent double-ended-iteration bugs, now covered
by the fuzzer: `range(..).rev()` yielded nothing (the back cursor was never
initialized for ranges), and interleaved `next()`/`next_back()` could yield
elements twice (the cursors never checked for meeting).

Measured after: bench_range flipped from 0.5–0.8× (losing) to 1.17–2.17×
faster at every range size; full iteration is 2.7–10× faster than std at
every size, forward and backward (backward at 10k was 1.7× slower, now 2.7×
faster). Still behind: single-item seeks and 10-item cursor hops (1.1–1.2×),
which are now pure descent cost — item 4c is the lever.

### 4. Random insert path

1.16–1.6× behind depending on key distribution. The macOS sample profile
(`profile.txt`) attributes the time to intra-leaf binary search + memmove
(`insert.rs:63`), branch descent (`insert.rs:65-66`), and split work. In
order of expected value:

a. ~~**Stop zeroing vacated slots on split paths.**~~ — DONE, but
   **perf-neutral**. All `write_bytes` zeroing of vacated key/value/child
   slots on the insert split paths, the delete borrow/merge paths, and
   `move_kv_at` is removed; occupancy is defined solely by `hdr.len` (the
   null child-pointer sentinels in delete.rs stay — `check_root_collapse`
   reads them). Proved safe by the full gate including Miri over the fuzz,
   drop/clear, and borrowing suites. An interleaved A/B of the before/after
   binaries showed no gain beyond noise (the commit message's claimed
   improvement was cross-run variance — see the measurement note below).
   Kept anyway: fewer stores, and the code no longer implies occupancy
   depends on zeroed slots. Splits are simply too rare (~1 per cap/2
   inserts) for their memsets to matter.

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

(Items 7 and 8 — cached iterative `next_back`, lazy `items_range()` — were
absorbed into item 3's rewrite.)

### 9. Keep benchmarks honest about capacity

Done in this change: `bench_insert` now defaults to cap=128 (was 16), and
`bench_range` plus the range/asm profile binaries use `new(128)` (was
`with_cache_lines(2, 2)` ≈ 6-entry nodes, which made range look 2.5–3×
worse than the tree actually is). Any future benchmark must use cap ≥ 64.

## Sequencing

1. ~~Items 1 (decoupling), 2, 3, 7, 8~~ — done.
2. Items 4a–4c as separate commits against the random-insert sweep; 4c also
   serves the remaining tiny-seek/cursor gap.
3. Items 5–6 next if insert is still behind.

Stop when random insert and mid-size range scans are within ~1.1× of std or
ahead; the structure (contiguous fixed-size nodes, linked leaves) should keep
its existing get/mixed/iteration advantages throughout.
