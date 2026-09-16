# Experiment: BPlusTreeMap inside Deno's npm resolver

A real-situation test of `BPlusTreeMap`: take a production project whose
core algorithm is built on `std::collections::BTreeMap`, swap in our tree,
run the project's tests, then run the project's own benchmarks with both
maps interleaved.

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
`libs/npm` becomes `use bplustree::BPlusTreeMap as BTreeMap` /
`BPlusTreeSet as BTreeSet`, and the crate gains a path dependency on this
one. Nothing else in the resolver changed. The maps involved:

- `Node::children: BTreeMap<StackString, NodeId>` (one per graph node, cloned)
- `PeersResolution::{resolved_peers, missing_peers}`
- `Graph::root_packages: BTreeMap<Rc<PackageNv>, NodeId>`
- `peer_fallbacks`, the `VersionReqsByVersion` nested maps, and the
  tracing / snapshot maps and sets.

Methods the resolver relies on that the library did not have:
`entry().or_default()`, `iter_mut`, `retain`, `Clone`, `Debug`, `Hash`,
`from([...])`, owned `into_iter`, an ordered set, and serde.

## Library changes the experiment forced

The first run of this experiment went through a separate shim crate that
composed the missing pieces out of the tree's primitives. That shim is
gone: the library now has the standard library's API itself, and the
substitution is a plain import change.

What had to be built:

1. Lookups by borrowed key (`get`, `remove`, `range` … over `Q: ?Sized`
   where `K: Borrow<Q>`), matching std.
2. `Send`/`Sync` impls (the map holds raw pointers, so it was neither).
3. `iter_mut`, `values_mut`, `range_mut`.
4. A lazy root: the constructor allocates no leaf, so an empty map is
   free. The resolver creates many maps that stay empty.
5. A native entry API. The lookup that decides vacant from occupied keeps
   the value's slot, and filling a vacant entry descends once because
   the insert hands back the slot it wrote.
6. A native owning iterator that walks the leaf chain and frees each leaf
   as it empties, where the shim popped the first entry repeatedly at a
   descent apiece.
7. `retain`, `append`, `split_off`, `pop_first`/`pop_last`,
   `remove_entry` (one descent: the key is read out of its slot), the
   ordered set, the trait impls, and optional serde.

`tests/std_compatibility.rs` drives this map and `std::collections::BTreeMap`
through the same operations and asserts the answers agree.

## Results

All 245 `deno_npm` tests pass on the B+ tree. Both benchmark binaries were
built from the same Deno checkout and run interleaved; every row below is
one full divan run (100 samples for `test`, 1000 for `nextjs_resolve`).

Synthetic resolver benchmark, `resolution::test` (26 packages x 100
versions, in-memory registry), median per run:

| Round | std BTreeMap | BPlusTreeMap |
|-------|--------------|--------------|
| 1     | 31.18 ms     | 34.55 ms     |
| 2     | 32.04 ms     | 34.02 ms     |
| 3     | 30.90 ms     | 33.97 ms     |
| 4     | 30.02 ms     | 33.09 ms     |
| 5     | 30.13 ms     | 36.52 ms     |

Real-world benchmark, `resolution::nextjs_resolve` (resolving `next@15.1.2`
against 58 cached npm packuments), median per run:

| Round | std BTreeMap | BPlusTreeMap |
|-------|--------------|--------------|
| 1     | 1.873 ms     | 1.980 ms     |
| 2     | 1.902 ms     | 2.007 ms     |
| 3     | 1.928 ms     | 2.046 ms     |

**The B+ tree is about 10% slower on the synthetic benchmark and about 6%
slower on the real one. There is no systemic improvement; the regression
is consistent across every interleaved round.**

## Why

Cachegrind on `resolution::test`, 10 samples, deterministic. The middle
column is the first run of this experiment, where the missing API was
composed in a shim crate; the right column is the same benchmark after
the library grew the API natively.

| Metric       | std BTreeMap | via the shim   | native         |
|--------------|--------------|----------------|----------------|
| Instructions | 3,043 M      | 3,162 M (+3.9%)| 3,175 M (+4.3%)|
| D1 misses    | 34.78 M      | 37.13 M (+6.8%)| 35.26 M (+0.5%)|
| I1 misses    | 14.03 M      | 15.20 M (+8.3%)| 15.37 M (+9.8%)|
| LL misses    | 0.248 M      | 0.268 M (+8.4%)| 0.267 M (+7.8%)|

Two things this says.

**The composed operations really were costing data-cache misses, and
making them native recovered almost all of them.** The shim's entry API
descended up to three times to fill one vacant slot, its owned iterator
popped the first entry at a descent apiece, and `remove_entry` looked the
key up twice. Those are gone: an occupied entry keeps the slot its lookup
landed on, a vacant one is filled by the insert that already knows where
it wrote, the owning iterator walks the leaf chain, and `remove_entry`
reads the stored key out of its slot. The extra data-cache misses over
std fell from 6.8% to 0.5%.

**It bought no wall-clock time.** The instruction count did not fall with
the misses; it rose slightly, because threading the value slot out of
`insert` adds a store to every insert, whether or not an entry wanted it.
The benchmark is where it was: about 10% behind.

The reason the earlier write-up gave still holds, and is the one that
matters. Ordered-map code is roughly 2-4% of this workload's
instructions. The resolver spends its time on semver matching
(`VersionReq::matches` is 26% of instructions, `Version::cmp` another
7%), the allocator, hashing and cloning package info. A map that cost
nothing at all could not have produced a systemic win here, and the maps
in question hold a handful to a hundred entries each where std keeps up
to eleven in a single node. The prediction that a native entry API and a
draining owned iterator were "the levers" was wrong: they were real
improvements to the library, and they are invisible in this host.

## Leaf-size check

To test whether node size alone explains the gap, a third binary was
built with the default leaf budget lowered from 512 to 256 bytes (9 slots
for this key/value pair, close to std's 11). Four interleaved rounds of
`resolution::test`, medians (that session ran noisier than the others):

| Round | std BTreeMap | 512 B leaves | 256 B leaves |
|-------|--------------|--------------|--------------|
| 1     | 32.67 ms     | 33.31 ms     | 34.94 ms     |
| 2     | 33.33 ms     | 34.86 ms     | 34.81 ms     |
| 3     | 31.92 ms     | 34.35 ms     | 34.57 ms     |
| 4     | 32.30 ms     | 36.17 ms     | 35.47 ms     |

Smaller leaves do not close the gap either.

## Reproducing

```
experiments/deno_npm/run.sh [work-dir] [rounds]
```

clones Deno at the pinned commit, applies the patch, runs the tests, builds
both benchmark binaries, and runs them interleaved. The Next.js benchmark
needs the npm registry reachable by its own HTTP client; behind a proxy
whose CA the client does not trust, pre-fill `target/.deno_npm/<name>`
with `curl` for each package it asks for (58 packuments for `next@15.1.2`).
