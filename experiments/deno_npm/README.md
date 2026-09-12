# Experiment: BPlusTreeMap inside Deno's npm resolver

A real-situation test of `BPlusTreeMap`: take a production project whose
core algorithm is built on `std::collections::BTreeMap`, swap in our tree
through the `bplustree-compat` shim, run the project's tests, then run the
project's own benchmarks with both maps interleaved.

## Choosing the host

Five candidates were surveyed (Materialize, Deno, Foundry, Biome,
SurrealDB) for (1) a `BTreeMap` on a genuinely hot path, (2) a strong test
suite, (3) real microbenchmarks, and (4) buildability on a 4-core, 15 GB,
30 GB-disk box without Docker.

| Project     | Hot ordered map?                                                | Tests             | Benchmarks                     | Build in isolation | Verdict |
|-------------|-----------------------------------------------------------------|-------------------|--------------------------------|--------------------|---------|
| Materialize | No. Hot state lives in differential-dataflow arrangements; the one per-record map was already moved from `BTreeMap` to `ahash::HashMap` (`src/row-spine`). `BucketChain` (≤64 entries) is the only bench-covered site. | 3,465 | criterion, 30 files | Needs rustc 1.97.1, cmake-built librdkafka/protobuf/RocksDB, 60–120 min, more disk than available | Poor |
| **Deno**    | **Yes: `libs/npm/resolution/graph.rs`, the npm peer-dependency solver, ~200 `BTreeMap` mentions in 3.5k lines of algorithm.** `deno_core`'s `GothamState`/`ResourceTable` are also BTreeMaps but need V8 to measure. | 245 in `deno_npm`, pure Rust, no network | divan `resolution::test` (synthetic, offline) and `resolution::nextjs_resolve` (real packuments) | `cargo test -p deno_npm`: no V8, ~300 crates | **Chosen** |
| Foundry     | No. revm, anvil storage, fork cache, fuzz dictionary are all hash maps; remaining BTreeMaps exist for deterministic output. | 2,500+ (many need RPC) | None (only a hyperfine end-to-end harness that clones GitHub repos) | 15–25 GB target dir | Poor |
| Biome       | No. Engine is rowan + `FxHashMap` (589 mentions vs 213 BTreeMap); one CSS semantic-model site. | 3,890 + 8,822 snapshots | criterion/divan, fixtures downloaded from a CDN | Fine | Poor |
| SurrealDB   | No. The per-record `Object` map already moved from `BTreeMap` to a sorted-`Vec` `VecMap`; the in-memory KV is the external `surrealmx` crate. | 2,506 in core | criterion, incl. a ready-made BTreeMap-vs-VecMap A/B bench | Heavy | Poor |

Deno's `deno_npm` crate is the only host where an ordered map is the
algorithm rather than configuration, and it is testable and benchmarkable
without building the runtime.

## What was substituted

`bplustree.patch` (against Deno commit in `DENO_COMMIT`) changes seven
lines of source: every `use std::collections::BTreeMap` / `BTreeSet` in
`libs/npm` becomes `use bplustree_compat::BTreeMap` / `BTreeSet`, and the
crate gains a path dependency on `compat/`. Nothing else in the resolver
changed. The maps involved:

- `Node::children: BTreeMap<StackString, NodeId>` (one per graph node, cloned)
- `PeersResolution::{resolved_peers, missing_peers}`
- `Graph::root_packages: BTreeMap<Rc<PackageNv>, NodeId>`
- `peer_fallbacks`, the `VersionReqsByVersion` nested maps, and the
  tracing / snapshot maps and sets.

Methods the resolver relies on that `BPlusTreeMap` did not have and the
shim (or the library) had to supply: `entry().or_default()`, `iter_mut`,
`retain`, `Clone`, `Debug`, `Hash`, `from([...])`, owned `into_iter`,
`BTreeSet`, and serde derives.

## Library changes the experiment forced

Before the swap could compile, the library itself needed:

1. Lookups by borrowed key (`get`, `remove`, `range` … over
   `Q: ?Sized` where `K: Borrow<Q>`), matching std.
2. `Send`/`Sync` impls (the map holds raw pointers, so it was neither).
3. `items_mut`, `values_mut`, `range_mut`.
4. A lazy root: the constructor no longer allocates a leaf, so an empty
   map is free. The resolver creates many maps that stay empty.

The compat crate composes the rest (entry API, `retain`, `append`,
`split_off`, `pop_first/last`, owned iteration, trait impls) from those
primitives and is checked against std by a differential test.

## Results

All 245 `deno_npm` tests pass on the B+ tree. Both benchmark binaries were
built from the same Deno checkout and run interleaved; every row below is
one full divan run (100 samples for `test`, 1000 for `nextjs_resolve`).

Synthetic resolver benchmark, `resolution::test` (26 packages × 100
versions, in-memory registry), median per run:

| Round | std BTreeMap | BPlusTreeMap (512 B leaves) |
|-------|--------------|-----------------------------|
| 1     | 31.44 ms     | 32.32 ms                    |
| 2     | 29.45 ms     | 32.97 ms                    |
| 3     | 29.42 ms     | 34.17 ms                    |
| 4     | 29.58 ms     | 33.74 ms                    |
| 5     | 30.40 ms     | 33.84 ms                    |

Real-world benchmark, `resolution::nextjs_resolve` (resolving `next@15.1.2`
against 58 cached npm packuments), median per run:

| Round | std BTreeMap | BPlusTreeMap (512 B leaves) |
|-------|--------------|-----------------------------|
| 1     | 2.010 ms     | 2.106 ms                    |
| 2     | 2.034 ms     | 2.179 ms                    |
| 3     | 2.039 ms     | 2.117 ms                    |

**The B+ tree is 10–12% slower on the synthetic benchmark and 4–7% slower
on the real one. There is no systemic improvement; the regression is
consistent across every interleaved round, well outside the run-to-run
spread.**

## Why

Callgrind and cachegrind on `resolution::test` (10 samples each,
deterministic):

| Metric              | std BTreeMap   | BPlusTreeMap   | Δ      |
|---------------------|----------------|----------------|--------|
| Instructions        | 3,043 M        | 3,162 M        | +3.9%  |
| D1 misses           | 34.78 M        | 37.13 M        | +6.8%  |
| I1 misses           | 14.03 M        | 15.20 M        | +8.3%  |
| LL misses           | 0.248 M        | 0.268 M        | +8.4%  |
| malloc calls        | 1.33 M         | 1.30 M         | −2%    |

Two facts explain the result:

1. **The maps are a small share of the work.** In both builds the
   resolver's time goes to semver matching (`VersionReq::matches` 26% of
   instructions, `Version::cmp` 7%), the allocator (~10%), hashing, and
   cloning package info. All ordered-map code together is roughly 2–4% of
   instructions. Even a zero-cost map could not produce a systemic win
   here; the ceiling was a few percent.
2. **These are tiny maps, and the tree is tuned for big ones.** A node's
   `children` map holds a handful of dependencies; `root_packages` holds
   100 entries at most. std's `BTreeMap` keeps up to 11 entries in a
   single 11-slot node. Our leaf for `(StackString, NodeId)` holds 18
   slots (512-byte payload budget), so each map touches more cache lines
   than the data needs, and the shim's composed operations (entry API as
   `contains_key` + `insert` + `get_mut`, `clone` as per-item insert,
   owned iteration as repeated `pop_first`) cost extra descents that std
   does structurally. The extra D1/I1 misses and the 4% more
   instructions add up to the 10% wall-time gap.

The strengths measured in this repo's own benchmarks (1.9× faster random
`get`, 3–5× faster iteration at a million `u64` keys) come from large,
cache-friendly leaves. That design works against the map in the regime
this host lives in: thousands of maps with fewer than twenty entries each.

## Leaf-size check

To test whether node size alone explains the gap, a third binary was
built with the shim's default leaf budget lowered from 512 to 256 bytes
(9 slots for this key/value pair, close to std's 11). Four interleaved
rounds of `resolution::test`, medians (this session ran noisier than the
first set):

| Round | std BTreeMap | B+ tree, 512 B leaves | B+ tree, 256 B leaves |
|-------|--------------|-----------------------|-----------------------|
| 1     | 32.67 ms     | 33.31 ms              | 34.94 ms              |
| 2     | 33.33 ms     | 34.86 ms              | 34.81 ms              |
| 3     | 31.92 ms     | 34.35 ms              | 34.57 ms              |
| 4     | 32.30 ms     | 36.17 ms              | 35.47 ms              |

Smaller leaves do not close the gap. The remaining cost is in the
per-operation constant factors of the tiny-map regime: the shim's composed
entry API (three descents for a vacant insert), item-by-item `clone`, and
`pop_first`-driven owned iteration, against std's single-node fast paths.
Those are fixable in the library (a native `entry`, a structural clone, a
draining owned iterator), but the ceiling in this host is a few percent,
not a systemic win.

## Reproducing

```
experiments/deno_npm/run.sh [work-dir] [rounds]
```

clones Deno at the pinned commit, applies the patch, runs the tests, builds
both benchmark binaries, and runs them interleaved. The Next.js benchmark
needs the npm registry reachable by its own HTTP client; behind a proxy
whose CA the client does not trust, pre-fill `target/.deno_npm/<name>`
with `curl` for each package it asks for (58 packuments for `next@15.1.2`).
