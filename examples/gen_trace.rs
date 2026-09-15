//! Trace generator for the Lean replay harness (`lean/Replay`).
//!
//! Runs a deterministic sequence of inserts and removes against
//! `BPlusTreeMap` and writes each one to a file with its return value.
//! Every `check_every` operations it writes the FNV-1a digest of the tree's
//! shape (`# <hex>`), and at the end the full shape (`= <shape>`). The Lean
//! executable replays the operations through the model and checks its
//! return values, digests, and final shape at the same points.
//!
//! Usage:
//!   gen_trace <seed> <leaf_cap> <branch_cap> <ops> <key_space> <check_every>
//!             <remove_pct> <drain> <out> [shape_at]
//!
//! `remove_pct` of the operations are removes (the differential fuzz uses
//! 30 against 40 inserts, so 43 matches it). With `drain` set to 1, after
//! the `ops` mixed operations every remaining key is removed in random
//! order, which walks the tree back down through every rebalance and root
//! collapse to empty. With `shape_at N`, the full shape after operation N
//! is also printed to stdout: the fallback `lean/replay.sh` uses to show
//! the Rust side of a digest mismatch.
use bplustree::BPlusTreeMap;
use std::fs::File;
use std::io::{BufWriter, Write};

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64*, the same generator the differential fuzz uses.
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

fn opt(v: Option<i64>) -> String {
    match v {
        Some(v) => v.to_string(),
        None => "-".into(),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 9 && args.len() != 10 {
        eprintln!(
            "usage: gen_trace <seed> <leaf_cap> <branch_cap> <ops> <key_space> <check_every> \
             <remove_pct> <drain> <out> [shape_at]"
        );
        std::process::exit(2);
    }
    let seed: u64 = args[0].parse().expect("seed");
    let leaf_cap: usize = args[1].parse().expect("leaf_cap");
    let branch_cap: usize = args[2].parse().expect("branch_cap");
    let ops: usize = args[3].parse().expect("ops");
    let key_space: u64 = args[4].parse().expect("key_space");
    let check_every: usize = args[5].parse().expect("check_every");
    let remove_pct: u64 = args[6].parse().expect("remove_pct");
    let drain: bool = args[7] == "1";
    let out = &args[8];
    let shape_at: Option<usize> = args.get(9).map(|a| a.parse().expect("shape_at"));

    let mut rng = Rng(seed);
    let mut tree = BPlusTreeMap::<i64, i64>::with_caps(leaf_cap, branch_cap).unwrap();
    let mut w = BufWriter::new(File::create(out).expect("create trace file"));
    writeln!(w, "CAPS {} {}", leaf_cap, branch_cap).unwrap();

    let mut i = 0usize;
    let check =
        |tree: &BPlusTreeMap<i64, i64>, i: usize, last: bool, w: &mut BufWriter<File>| {
            if i % check_every == 0 || last {
                tree.check_invariants_detailed()
                    .unwrap_or_else(|why| panic!("invariants broken after op {}: {}", i, why));
                writeln!(w, "# {:016x}", tree.shape_hash()).unwrap();
            }
            if shape_at == Some(i) {
                println!("{}", tree.dump_shape());
            }
        };

    for _ in 0..ops {
        i += 1;
        let k = rng.below(key_space) as i64;
        if rng.below(100) < remove_pct {
            let got = tree.remove(&k);
            writeln!(w, "R {} {}", k, opt(got)).unwrap();
        } else {
            let v = i as i64;
            let old = tree.insert(k, v);
            writeln!(w, "I {} {} {}", k, v, opt(old)).unwrap();
        }
        check(&tree, i, !drain && i == ops, &mut w);
    }

    if drain {
        // Remove every remaining key in a random order.
        let mut keys: Vec<i64> = tree.keys().copied().collect();
        for j in (1..keys.len()).rev() {
            let r = rng.below(j as u64 + 1) as usize;
            keys.swap(j, r);
        }
        let n = keys.len();
        for (j, k) in keys.into_iter().enumerate() {
            i += 1;
            let got = tree.remove(&k);
            writeln!(w, "R {} {}", k, opt(got)).unwrap();
            check(&tree, i, j + 1 == n, &mut w);
        }
    }

    writeln!(w, "= {}", tree.dump_shape()).unwrap();
    w.flush().unwrap();

    // With `--features delete_profile`, report which repair paths the trace
    // exercised, so a passing replay is known to have covered them.
    #[cfg(feature = "delete_profile")]
    eprintln!("{}: {:?}", out, tree.delete_profile());
}
