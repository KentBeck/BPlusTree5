Integration tests for `BPlusTreeMap`, run with `cargo test`.

`std_compatibility.rs` is the one that defines the public API: it drives this
map and `std::collections::BTreeMap` (and the two sets) through the same
operations and asserts that every answer agrees. Anything the standard
library's map can do, that file does to both.

The rest of the suite came from the BPlusTree3 project and exercises the tree
structure itself: splits, merges, borrows, the leaf chain, and drop behaviour.
`test_utils.rs` holds the helpers those files include via `mod test_utils;`.

These tests build the library with its `internal` feature, which exposes node
capacities and invariant checks that are not public API (a dev-dependency on
the crate itself turns it on, so plain `cargo test` is enough). That is how a
test can build a tree with four-entry nodes and force the rebalancing paths
after a handful of inserts.

The differential fuzz suite has an extended mode:
`cargo test --release --test differential_fuzz -- --ignored`.
