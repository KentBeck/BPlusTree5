//! Trace generator for the Lean replay harness (`lean/Replay`).
//!
//! Runs a deterministic sequence of operations against `BPlusTreeMap` and
//! writes each one to a file. Every `check_every` operations it writes the
//! FNV-1a digest of the tree's shape (`# <hex>`), and at the end the full
//! shape (`= <shape>`). The Lean executable replays the operations through
//! the model and checks its own digest and shape at the same points.
//! Insert-only until the model grows `remove`.
//!
//! Usage:
//!   gen_trace <seed> <leaf_cap> <branch_cap> <ops> <key_space> <check_every> <out> [shape_at]
//!
//! With `shape_at N`, the full shape after operation N is also printed to
//! stdout: the fallback `lean/replay.sh` uses to show the Rust side of a
//! digest mismatch.
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

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 7 && args.len() != 8 {
        eprintln!(
            "usage: gen_trace <seed> <leaf_cap> <branch_cap> <ops> <key_space> <check_every> <out> [shape_at]"
        );
        std::process::exit(2);
    }
    let seed: u64 = args[0].parse().expect("seed");
    let leaf_cap: usize = args[1].parse().expect("leaf_cap");
    let branch_cap: usize = args[2].parse().expect("branch_cap");
    let ops: usize = args[3].parse().expect("ops");
    let key_space: u64 = args[4].parse().expect("key_space");
    let check_every: usize = args[5].parse().expect("check_every");
    let out = &args[6];
    let shape_at: Option<usize> = args.get(7).map(|a| a.parse().expect("shape_at"));

    let mut rng = Rng(seed);
    let mut tree = BPlusTreeMap::<i64, i64>::with_caps(leaf_cap, branch_cap).unwrap();
    let mut w = BufWriter::new(File::create(out).expect("create trace file"));
    writeln!(w, "CAPS {} {}", leaf_cap, branch_cap).unwrap();
    for i in 1..=ops {
        let k = rng.below(key_space) as i64;
        let v = i as i64;
        tree.insert(k, v);
        writeln!(w, "I {} {}", k, v).unwrap();
        if i % check_every == 0 || i == ops {
            tree.check_invariants_detailed()
                .unwrap_or_else(|why| panic!("invariants broken after op {}: {}", i, why));
            writeln!(w, "# {:016x}", tree.shape_hash()).unwrap();
        }
        if shape_at == Some(i) {
            println!("{}", tree.dump_shape());
        }
    }
    writeln!(w, "= {}", tree.dump_shape()).unwrap();
    w.flush().unwrap();
}
