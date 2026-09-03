Integration tests for `BPlusTreeMap`. Most of the suite was imported from the
BPlusTree3 project to drive API compatibility; `test_utils.rs` holds the shared
helpers those files include via `mod test_utils;`.

Run everything with `cargo test`. The differential fuzz suite has an extended
mode: `cargo test --release --test differential_fuzz -- --ignored`.
