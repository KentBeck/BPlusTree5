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
both; the effect must clear the interleaved spread. For effects below the
noise floor, `valgrind --tool=cachegrind --cache-sim=yes` gives deterministic
instruction and cache-miss counts (see `examples/insert_only.rs`).

## Where we stand today (cap=128, 1M items)

Wins (keep these; do not regress):

| Operation                          | vs std::BTreeMap |
|------------------------------------|------------------|
| get (random)                       | 1.9× faster      |
| delete (`with_caps(32, 256)`)      | 1.10× faster     |
| mixed 50/30/20 ins/get/del         | 1.2× faster      |
| full iteration (fwd and back)      | 3–5× faster      |
| full-tree range scan               | 1.25× faster     |
| sequential (sorted) insert         | 1.2× faster      |
| `len()` (1M items)                 | parity (~0.4 ns per call) |

Losses:

| Operation                              | vs std::BTreeMap                 |
|----------------------------------------|----------------------------------|
| delete (`new(128)`)                    | 1.10× slower                     |
| random insert                          | parity (bench_insert keys) to 1.4× slower (hash-scattered probe keys) |
| single-item range seek / tiny cursors  | 1.1–1.2× slower (descent-bound) |

Capacity sweep (random insert, probe keys): 64 → 0.372s, 128 → 0.412s,
256 → 0.443s, 512 → 0.608s (std: 0.254s). Insert degrades with leaf size
because every insert memmoves half a leaf on average (~1KB at cap=128);
get/iteration prefer the larger nodes. That tension motivates item 5.

## P0 — asymptotic bugs (large wins, low risk)

### 1. ~~`len()` is O(n)~~ — DONE

The map now stores `entry_count`, increments it only for a new key, decrements
it only for a successful removal, and resets it in `clear()`. Both `len()` and
`is_empty()` are simple reads of that count. `check_invariants_detailed`
independently counts the entries in the leaves and rejects a stale stored
count, so every differential-fuzz invariant check audits the bookkeeping.

Measured on a one-million-item tree: 10k `len()` calls fell from 3.56–3.70s
(356–370 microseconds each) to 0.35–0.44ns each, matching std::BTreeMap—about
a million-fold speedup. Interleaved million- and five-million-key mutation
benchmarks found insertion, removal, and mixed-workload changes within the
normal run-to-run spread.

### 2. ~~`first()` and `last()` in O(log n)~~ — DONE

Fixed: `first()`/`last()` now read directly from the leftmost/rightmost leaf
instead of building/consuming a full `items()` iterator. Measured: 10k
first/last pairs went from 39s to 0.1ms — parity with std.

## P1 — the real per-op gaps

### 3. ~~Range/cursor iterator: cache leaf state, precompute the end~~ — DONE

The iterator now resolves both bounds to concrete (leaf, index) positions at
construction and caches the current leaf's key/value pointers, so per-item
work is an index compare and two pointer reads — no key comparisons, no
re-carving, no bound-key clones. `items()` does not consult `len()`,
`items_range()` is lazy instead of collecting a Vec
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

1.16–1.6× behind depending on key distribution. A sampling profile
attributes the time to intra-leaf binary search + memmove, branch descent,
and split work. In order of expected value:

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

b. ~~**Iterative descent.**~~ — DONE. `insert()` now descends iteratively,
   recording `(branch, child_idx)` and applying split fixups bottom-up via
   `branch_apply_split`; `insert_rec` is gone. Cachegrind (deterministic):
   13.6% fewer instructions (88.8M → 76.6M for 200k inserts), D1/LL misses
   identical. Wall-clock neutral on this machine because the workload is
   memory-bound (~17 D1 misses per insert, unchanged); the instruction win
   is real but hidden behind stalls. Bonus: no unbounded recursion.

   **Key diagnosis from the cache simulation: random insert is D1-miss
   bound, not instruction bound.** Instruction-shaving alone won't move
   wall time; reducing misses per operation is the lever.

c. **Branchless intra-node binary search + child prefetch.**
   `binary_search_keys` (`common.rs:70`) is `slice::binary_search`. Per the
   diagnosis in 4b, the branchless-cmov half of this item is demoted (it
   shaves instructions, not misses). The promising half is the memory side:
   a search that prefetches the child line mid-descent, or a two-level
   layout that touches fewer key cache lines per node (e.g. a first-line
   "router" of evenly spaced keys). Measure with cachegrind miss counts
   first, wall clock second.

### 5. ~~Decoupled leaf/branch capacities~~ — DONE (`with_caps`)

`with_caps(leaf_cap, branch_cap)` decouples the two; `new(c)` is now
`with_caps(c, c)`. The differential fuzzer covers asymmetric configurations
in both directions (including under Miri).

Grid measurements (cachegrind, 200k hash-scattered inserts, workload-phase
deltas): leaf 32 cuts insert D1 misses 37% vs leaf 128 (3.56M → 2.23M) and
leaf 64 cuts 29%; get misses are unchanged; iteration/range pay +8–20% in
the simulator. On real hardware (interleaved wall clock, 1M keys) the scan
penalty vanishes behind prefetch and **`with_caps(32, 256)` won or tied
`new(128)` in every round of every workload**: build ~0.32s vs 0.37s,
build+get ~0.63s vs 0.80s (leaf search touches 4 cache lines, not 16),
build+range ~0.34s vs 0.42s, build+iter a tie. That puts random insert at
~1.2–1.3× of std (from 1.4–1.6× at uniform 128) and widens the get lead.

Whether `new()` should default to a split like this is an API-taste call
for the author; the benches keep `new(128)` as the standard config, and
`perf_probe` prints a `32/256` row alongside for comparison.

The same split also flips random deletion from a loss to a win. In 15
interleaved one-million-key samples, `new(128)` was 1.10× slower than std
while `with_caps(32, 256)` was 1.10× faster. `bench_delete` accepts both
capacities and alternates which implementation runs first.

### 6. Delete repair diagnosis

Feature-gated structural counters (`delete_profile`) show that allocation
pooling is not the next lever. The faster 32/256 configuration performs
44,760 leaf merges/deallocations per million removals, versus only 11,276
at 128/128; it wins despite doing about four times as much allocator churn.

The clearer target is the nearly unconditional repair check at each ancestor.
Both configurations run about one leaf and one branch rebalance check per
removal, but branch repairs are rare: 2,883 borrows/merges at 128/128 and
11,234 at 32/256 per million removals. Have recursive deletion propagate an
`underflow` result so parents skip `fix_branch_child` when the child remains
full enough. Measure that as its own change before reconsidering a bounded
node free list.

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
