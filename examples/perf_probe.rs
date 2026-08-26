//! Focused probe of the operations where BPlusTreeMap trails std::BTreeMap:
//! insert (by capacity), range seek, tiny cursor iterations, first/last, len.
use bplustree::BPlusTreeMap;
use std::collections::BTreeMap;
use std::hint::black_box;
use std::time::Instant;

fn pseudo_shuffle(n: usize) -> Vec<u64> {
    // Deterministic multiplicative-hash order (not sorted).
    (0..n as u64)
        .map(|i| i.wrapping_mul(0x9E3779B97F4A7C15))
        .collect()
}

fn main() {
    let n = 1_000_000usize;
    let keys = pseudo_shuffle(n);

    println!("== insert {} random u64 keys ==", n);
    for cap in [64usize, 128, 256, 512] {
        let t0 = Instant::now();
        let mut m = BPlusTreeMap::new(cap).unwrap();
        for &k in &keys {
            m.insert(k, k);
        }
        let dt = t0.elapsed().as_secs_f64();
        println!("  bplustree cap={:<4} {:.3}s ({:.2} Mops)", cap, dt, n as f64 / dt / 1e6);
        black_box(&m);
    }
    let t0 = Instant::now();
    let mut sm = BTreeMap::new();
    for &k in &keys {
        sm.insert(k, k);
    }
    let dt = t0.elapsed().as_secs_f64();
    println!("  std::BTreeMap    {:.3}s ({:.2} Mops)", dt, n as f64 / dt / 1e6);

    println!("== sequential insert (sorted keys) ==");
    for cap in [128usize, 256] {
        let t0 = Instant::now();
        let mut m = BPlusTreeMap::new(cap).unwrap();
        for i in 0..n as u64 {
            m.insert(i, i);
        }
        let dt = t0.elapsed().as_secs_f64();
        println!("  bplustree cap={:<4} {:.3}s ({:.2} Mops)", cap, dt, n as f64 / dt / 1e6);
        black_box(&m);
    }
    let t0 = Instant::now();
    let mut sm2 = BTreeMap::new();
    for i in 0..n as u64 {
        sm2.insert(i, i);
    }
    let dt = t0.elapsed().as_secs_f64();
    println!("  std::BTreeMap    {:.3}s ({:.2} Mops)", dt, n as f64 / dt / 1e6);

    // Build cap=128 tree of sorted keys for query probes.
    let mut m = BPlusTreeMap::new(128).unwrap();
    for i in 0..n as u64 {
        m.insert(i, i);
    }

    println!("== range seek: 100k queries of 100 items each, cap=128 ==");
    let q = 100_000u64;
    let t0 = Instant::now();
    let mut sum = 0u64;
    for i in 0..q {
        let s = (i * 7919) % (n as u64 - 200);
        for (k, v) in m.range(s..s + 100) {
            sum = sum.wrapping_add(*k + *v);
        }
    }
    let dt = t0.elapsed().as_secs_f64();
    println!("  bplustree     {:.3}s  (sum {})", dt, sum);
    let t0 = Instant::now();
    let mut sum2 = 0u64;
    for i in 0..q {
        let s = (i * 7919) % (n as u64 - 200);
        for (k, v) in sm2.range(s..s + 100) {
            sum2 = sum2.wrapping_add(*k + *v);
        }
    }
    let dt = t0.elapsed().as_secs_f64();
    println!("  std::BTreeMap {:.3}s  (sum {})", dt, sum2);

    println!("== range seek only: 1M queries of 1 item ==");
    let t0 = Instant::now();
    let mut sum = 0u64;
    for i in 0..n as u64 {
        let s = (i * 7919) % (n as u64 - 2);
        if let Some((k, _)) = m.range(s..s + 1).next() {
            sum = sum.wrapping_add(*k);
        }
    }
    let dt = t0.elapsed().as_secs_f64();
    println!("  bplustree     {:.3}s  (sum {})", dt, sum);
    let t0 = Instant::now();
    let mut sum2 = 0u64;
    for i in 0..n as u64 {
        let s = (i * 7919) % (n as u64 - 2);
        if let Some((k, _)) = sm2.range(s..s + 1).next() {
            sum2 = sum2.wrapping_add(*k);
        }
    }
    let dt = t0.elapsed().as_secs_f64();
    println!("  std::BTreeMap {:.3}s  (sum {})", dt, sum2);

    println!("== first()/last(): 10k calls on 1M-item map ==");
    let t0 = Instant::now();
    let mut sum = 0u64;
    for _ in 0..10_000 {
        sum = sum.wrapping_add(*black_box(m.first().unwrap().0));
        sum = sum.wrapping_add(*black_box(m.last().unwrap().0));
    }
    let dt = t0.elapsed().as_secs_f64();
    println!("  bplustree     {:.4}s (sum {})", dt, sum);
    let t0 = Instant::now();
    let mut sum2 = 0u64;
    for _ in 0..10_000 {
        sum2 = sum2.wrapping_add(*black_box(sm2.first_key_value().unwrap().0));
        sum2 = sum2.wrapping_add(*black_box(sm2.last_key_value().unwrap().0));
    }
    let dt = t0.elapsed().as_secs_f64();
    println!("  std::BTreeMap {:.4}s (sum {})", dt, sum2);

    println!("== len(): 10k calls on 1M-item map ==");
    let t0 = Instant::now();
    let mut acc = 0usize;
    for _ in 0..10_000 {
        acc = acc.wrapping_add(black_box(m.len()));
    }
    let dt = t0.elapsed().as_secs_f64();
    println!("  bplustree     {:.4}s (acc {})", dt, acc);
    let t0 = Instant::now();
    let mut acc2 = 0usize;
    for _ in 0..10_000 {
        acc2 = acc2.wrapping_add(black_box(sm2.len()));
    }
    let dt = t0.elapsed().as_secs_f64();
    println!("  std::BTreeMap {:.4}s (acc {})", dt, acc2);
}
