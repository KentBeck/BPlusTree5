//! Differential fuzzing against std::collections::BTreeMap.
//!
//! Stronger than fuzz_tests.rs: checks tree invariants after every mutation,
//! uses drop-tracking values to catch double-frees and leaks, exercises
//! random range queries, get_mut, first/last, and clear, across many
//! capacities. Deterministic PRNG; failures print the seed for replay.

use bplustree::BPlusTreeMap;
use std::collections::BTreeMap;
use std::ops::Bound;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

const CANARY: u64 = 0xDEAD_BEEF_CAFE_F00D;

/// Value that counts live instances (per-run counter, parallel-test safe)
/// and carries a canary so a read after free or a double drop is detected
/// instead of silently misbehaving.
#[derive(Debug)]
struct Tracked {
    canary: u64,
    val: i64,
    live: Arc<AtomicUsize>,
}

impl Tracked {
    fn new(val: i64, live: &Arc<AtomicUsize>) -> Self {
        live.fetch_add(1, Ordering::SeqCst);
        Tracked { canary: CANARY, val, live: Arc::clone(live) }
    }
    fn get(&self) -> i64 {
        assert_eq!(self.canary, CANARY, "canary destroyed: use-after-free?");
        self.val
    }
}

impl Drop for Tracked {
    fn drop(&mut self) {
        assert_eq!(self.canary, CANARY, "double free detected");
        self.canary = 0;
        self.live.fetch_sub(1, Ordering::SeqCst);
    }
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn random_bound(rng: &mut Rng, key_space: u64) -> Bound<i64> {
    let k = rng.below(key_space) as i64;
    match rng.below(3) {
        0 => Bound::Included(k),
        1 => Bound::Excluded(k),
        _ => Bound::Unbounded,
    }
}

fn run_differential(seed: u64, capacity: usize, ops: usize, key_space: u64) {
    run_differential_caps(seed, capacity, capacity, ops, key_space)
}

fn run_differential_caps(seed: u64, leaf_cap: usize, branch_cap: usize, ops: usize, key_space: u64) {
    // Miri runs orders of magnitude slower; a few hundred ops per config is
    // still enough to cross split/merge/borrow paths at small capacities.
    let ops = if cfg!(miri) { ops.min(300) } else { ops };
    let mut rng = Rng(seed);
    let live = Arc::new(AtomicUsize::new(0));
    let mut tree: BPlusTreeMap<i64, Tracked> =
        BPlusTreeMap::with_caps(leaf_cap, branch_cap).unwrap();
    let mut model: BTreeMap<i64, i64> = BTreeMap::new();
    let ctx =
        |op: usize| format!("seed={:#x} caps={}/{} op#{}", seed, leaf_cap, branch_cap, op);

    for op in 0..ops {
        match rng.below(100) {
            // insert (40%)
            0..=39 => {
                let k = rng.below(key_space) as i64;
                let v = rng.next() as i64;
                let old_tree = tree.insert(k, Tracked::new(v, &live)).map(|t| t.get());
                let old_model = model.insert(k, v);
                assert_eq!(old_tree, old_model, "insert mismatch: {}", ctx(op));
                tree.check_invariants_detailed()
                    .unwrap_or_else(|e| panic!("invariants after insert: {}: {}", ctx(op), e));
            }
            // remove (30%)
            40..=69 => {
                let k = rng.below(key_space) as i64;
                let got = tree.remove(&k).map(|t| t.get());
                let exp = model.remove(&k);
                assert_eq!(got, exp, "remove mismatch: {}", ctx(op));
                tree.check_invariants_detailed()
                    .unwrap_or_else(|e| panic!("invariants after remove: {}: {}", ctx(op), e));
            }
            // get / contains (10%)
            70..=79 => {
                let k = rng.below(key_space) as i64;
                assert_eq!(
                    tree.get(&k).map(|t| t.get()),
                    model.get(&k).copied(),
                    "get mismatch: {}",
                    ctx(op)
                );
                assert_eq!(tree.contains_key(&k), model.contains_key(&k));
            }
            // get_mut and mutate (5%)
            80..=84 => {
                let k = rng.below(key_space) as i64;
                let v = rng.next() as i64;
                match (tree.get_mut(&k), model.get_mut(&k)) {
                    (Some(t), Some(m)) => {
                        assert_eq!(t.get(), *m, "get_mut value mismatch: {}", ctx(op));
                        t.val = v;
                        *m = v;
                    }
                    (None, None) => {}
                    (t, m) => panic!(
                        "get_mut presence mismatch ({:?} vs {:?}): {}",
                        t.is_some(),
                        m.is_some(),
                        ctx(op)
                    ),
                }
            }
            // random range query (10%)
            85..=94 => {
                let a = random_bound(&mut rng, key_space);
                let b = random_bound(&mut rng, key_space);
                // Skip inverted / invalid bound pairs that std panics on.
                let valid = match (&a, &b) {
                    (Bound::Included(x), Bound::Included(y)) => x <= y,
                    (Bound::Included(x), Bound::Excluded(y))
                    | (Bound::Excluded(x), Bound::Included(y)) => x <= y,
                    (Bound::Excluded(x), Bound::Excluded(y)) => x < y,
                    _ => true,
                };
                if valid {
                    match rng.below(3) {
                        0 => {
                            let got: Vec<(i64, i64)> =
                                tree.range((a, b)).map(|(k, v)| (*k, v.get())).collect();
                            let exp: Vec<(i64, i64)> =
                                model.range((a, b)).map(|(k, v)| (*k, *v)).collect();
                            assert_eq!(got, exp, "range {:?}..{:?} mismatch: {}", a, b, ctx(op));
                        }
                        1 => {
                            let got: Vec<(i64, i64)> = tree
                                .range((a, b))
                                .rev()
                                .map(|(k, v)| (*k, v.get()))
                                .collect();
                            let exp: Vec<(i64, i64)> =
                                model.range((a, b)).rev().map(|(k, v)| (*k, *v)).collect();
                            assert_eq!(
                                got, exp,
                                "reverse range {:?}..{:?} mismatch: {}",
                                a, b, ctx(op)
                            );
                        }
                        _ => {
                            // Interleaved double-ended consumption must yield each
                            // element exactly once, meeting in the middle.
                            let mut ti = tree.range((a, b));
                            let mut mi = model.range((a, b));
                            loop {
                                let front = rng.below(2) == 0;
                                let (g, e) = if front {
                                    (
                                        ti.next().map(|(k, v)| (*k, v.get())),
                                        mi.next().map(|(k, v)| (*k, *v)),
                                    )
                                } else {
                                    (
                                        ti.next_back().map(|(k, v)| (*k, v.get())),
                                        mi.next_back().map(|(k, v)| (*k, *v)),
                                    )
                                };
                                assert_eq!(
                                    g, e,
                                    "interleaved range {:?}..{:?} (front={}) mismatch: {}",
                                    a, b, front, ctx(op)
                                );
                                if g.is_none() {
                                    break;
                                }
                            }
                            // Exhausted from one end means exhausted from both.
                            assert!(ti.next().is_none(), "next after exhaustion: {}", ctx(op));
                            assert!(
                                ti.next_back().is_none(),
                                "next_back after exhaustion: {}",
                                ctx(op)
                            );
                        }
                    }
                }
            }
            // first/last + full iteration (4%)
            95..=98 => {
                assert_eq!(
                    tree.first().map(|(k, v)| (*k, v.get())),
                    model.iter().next().map(|(k, v)| (*k, *v)),
                    "first mismatch: {}",
                    ctx(op)
                );
                assert_eq!(
                    tree.last().map(|(k, v)| (*k, v.get())),
                    model.iter().next_back().map(|(k, v)| (*k, *v)),
                    "last mismatch: {}",
                    ctx(op)
                );
                let got: Vec<(i64, i64)> = tree.items().map(|(k, v)| (*k, v.get())).collect();
                let exp: Vec<(i64, i64)> = model.iter().map(|(k, v)| (*k, *v)).collect();
                assert_eq!(got, exp, "full iteration mismatch: {}", ctx(op));
            }
            // clear (1%)
            _ => {
                tree.clear();
                model.clear();
                tree.check_invariants_detailed()
                    .unwrap_or_else(|e| panic!("invariants after clear: {}: {}", ctx(op), e));
            }
        }
        assert_eq!(tree.len(), model.len(), "len mismatch: {}", ctx(op));
        assert_eq!(
            tree.is_empty(),
            model.is_empty(),
            "is_empty mismatch: {}",
            ctx(op)
        );
        assert_eq!(
            live.load(Ordering::SeqCst),
            model.len(),
            "live-object count diverged (leak or double free): {}",
            ctx(op)
        );
    }

    drop(tree);
    assert_eq!(
        live.load(Ordering::SeqCst),
        0,
        "leak detected after final drop: seed={:#x} caps={}/{}",
        seed,
        leaf_cap,
        branch_cap
    );
}

#[test]
fn differential_fuzz_small_capacities() {
    for &cap in &[4usize, 5, 6, 7] {
        run_differential(0x5EED_0001 + cap as u64, cap, 6_000, 200);
    }
}

#[test]
fn differential_fuzz_medium_capacities() {
    for &cap in &[8usize, 12, 16, 32] {
        run_differential(0x5EED_0100 + cap as u64, cap, 6_000, 1_000);
    }
}

#[test]
fn differential_fuzz_asymmetric_caps() {
    // Decoupled leaf/branch capacities, skewed in both directions.
    for &(leaf, branch) in &[(4usize, 32usize), (32, 4), (8, 128), (128, 8), (64, 256)] {
        run_differential_caps(
            0x5EED_0300 ^ ((leaf as u64) << 16) ^ branch as u64,
            leaf,
            branch,
            6_000,
            500,
        );
    }
}

#[test]
fn differential_fuzz_large_capacity_dense_keys() {
    // Dense key space => heavy churn of updates and removes of present keys.
    run_differential(0x5EED_0200, 64, 8_000, 64);
    run_differential(0x5EED_0201, 128, 8_000, 5_000);
}

#[test]
#[ignore] // Long-running: cargo test --release --test differential_fuzz -- --ignored
fn differential_fuzz_extended() {
    for round in 0..20u64 {
        for &cap in &[4usize, 5, 7, 8, 16, 33, 64, 128] {
            run_differential(0xC0FFEE ^ (round << 8) ^ cap as u64, cap, 20_000, 500);
        }
    }
}
