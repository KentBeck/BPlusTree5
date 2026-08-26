use bplustree::BPlusTreeMap;
use std::hint::black_box;

// Cachegrind harness. Builds a tree of n hash-scattered keys, then optionally
// runs one query workload on it; isolate a workload's cost by subtracting the
// "build" run's counts from the "build+workload" run's.
// Usage: insert_only [leaf_cap=128] [branch_cap=leaf_cap] [n=200000] [phase=build]
//   phase: build | get | iter | range
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let leaf_cap: usize = args.first().map_or(128, |a| a.parse().expect("leaf_cap"));
    let branch_cap: usize = args
        .get(1)
        .map_or(leaf_cap, |a| a.parse().expect("branch_cap"));
    let n: usize = args.get(2).map_or(200_000, |a| a.parse().expect("n"));
    assert!(n > 0, "n must be greater than zero");
    let phase = args.get(3).map_or("build", |a| a.as_str());

    let key = |i: u64| i.wrapping_mul(0x9E3779B97F4A7C15);

    let mut m = BPlusTreeMap::with_caps(leaf_cap, branch_cap).unwrap();
    for i in 0..n as u64 {
        m.insert(key(i), i);
    }

    let mut sum = 0u64;
    match phase {
        "build" => {}
        "get" => {
            for i in 0..n as u64 {
                if let Some(v) = m.get(&key(i.wrapping_mul(7919) % n as u64)) {
                    sum = sum.wrapping_add(*v);
                }
            }
        }
        "iter" => {
            for _ in 0..10 {
                for (k, v) in m.items() {
                    sum = sum.wrapping_add(*k).wrapping_add(*v);
                }
            }
        }
        "range" => {
            for i in 0..20_000u64 {
                let s = key(i.wrapping_mul(31) % n as u64);
                for (k, v) in m.range(s..).take(100) {
                    sum = sum.wrapping_add(*k).wrapping_add(*v);
                }
            }
        }
        other => panic!("unknown phase {other}"),
    }
    black_box((sum, m.first()));
}
