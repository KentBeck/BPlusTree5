use bplustree::BPlusTreeMap;
use std::collections::BTreeMap;
use std::env;
use std::hint::black_box;
use std::time::{Duration, Instant};

const DEFAULT_ITEMS: usize = 1_000_000;
const DEFAULT_CAPACITY: usize = 128;
const DEFAULT_SAMPLES: usize = 7;

fn parse_arg<T: std::str::FromStr>(index: usize, default: T) -> T {
    env::args()
        .nth(index)
        .and_then(|value| value.parse().ok())
        .unwrap_or(default)
}

#[derive(Clone, Copy)]
struct Timings {
    build: Duration,
    delete: Duration,
}

fn main() {
    // Usage: bench_delete [items=1000000] [leaf_cap=128]
    //                     [branch_cap=leaf_cap] [samples=7]
    let item_count = parse_arg(1, DEFAULT_ITEMS);
    let leaf_cap = parse_arg(2, DEFAULT_CAPACITY);
    let branch_cap = parse_arg(3, leaf_cap);
    let sample_count = parse_arg(4, DEFAULT_SAMPLES);
    assert!(item_count > 0, "items must be greater than zero");
    assert!(sample_count > 0, "samples must be greater than zero");

    let insertion_order = generate_keys(item_count);
    let deletion_order = shuffled(&insertion_order);
    let mut bplus_samples = Vec::with_capacity(sample_count);
    let mut std_samples = Vec::with_capacity(sample_count);

    // Warm both implementations before collecting samples.
    let warmup_len = item_count.min(10_000);
    let warmup_insertion_order = &insertion_order[..warmup_len];
    let warmup_deletion_order = shuffled(warmup_insertion_order);
    let _ = bench_bplustree(
        warmup_insertion_order,
        &warmup_deletion_order,
        leaf_cap,
        branch_cap,
    );
    let _ = bench_std(warmup_insertion_order, &warmup_deletion_order);

    // Alternate which implementation runs first to balance machine drift.
    for sample_index in 0..sample_count {
        if sample_index % 2 == 0 {
            bplus_samples.push(bench_bplustree(
                &insertion_order,
                &deletion_order,
                leaf_cap,
                branch_cap,
            ));
            std_samples.push(bench_std(&insertion_order, &deletion_order));
        } else {
            std_samples.push(bench_std(&insertion_order, &deletion_order));
            bplus_samples.push(bench_bplustree(
                &insertion_order,
                &deletion_order,
                leaf_cap,
                branch_cap,
            ));
        }
    }

    let bplus_build = summarize(&bplus_samples, |sample| sample.build);
    let bplus_delete = summarize(&bplus_samples, |sample| sample.delete);
    let std_build = summarize(&std_samples, |sample| sample.build);
    let std_delete = summarize(&std_samples, |sample| sample.delete);

    println!("Delete Performance Benchmark");
    println!("============================");
    println!(
        "items: {item_count} | leaf/branch capacity: {leaf_cap}/{branch_cap} | samples: {sample_count}\n"
    );
    print_summary("BPlusTree build", item_count, bplus_build);
    print_summary("std build", item_count, std_build);
    print_summary("BPlusTree delete", item_count, bplus_delete);
    print_summary("std delete", item_count, std_delete);

    let ratios = summarize_ratios(&bplus_samples, &std_samples, |sample| sample.delete);
    if ratios.median <= 1.0 {
        println!(
            "\nBPlusTree deletion: {:.3}x faster than std \
             (BPlusTree/std paired ratio {:.3}–{:.3})",
            1.0 / ratios.median,
            ratios.min,
            ratios.max
        );
    } else {
        println!(
            "\nBPlusTree deletion: {:.3}x slower than std \
             (BPlusTree/std paired ratio {:.3}–{:.3})",
            ratios.median, ratios.min, ratios.max
        );
    }
}

fn generate_keys(item_count: usize) -> Vec<u64> {
    let mut state = 0x1234_5678_9abc_def0_u64;
    (0..item_count)
        .map(|_| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            state
        })
        .collect()
}

fn shuffled(keys: &[u64]) -> Vec<u64> {
    let mut keys = keys.to_vec();
    let mut state = 0xfedc_ba98_7654_3210_u64;
    for index in 0..keys.len() {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        let swap_with = index + (state as usize) % (keys.len() - index);
        keys.swap(index, swap_with);
    }
    keys
}

fn bench_bplustree(
    insertion_order: &[u64],
    deletion_order: &[u64],
    leaf_cap: usize,
    branch_cap: usize,
) -> Timings {
    let mut map = BPlusTreeMap::with_caps(leaf_cap, branch_cap).expect("valid capacities");
    let build = time(|| {
        for (value, &key) in insertion_order.iter().enumerate() {
            black_box(map.insert(key, value));
        }
    });
    let delete = time(|| {
        for key in deletion_order {
            black_box(map.remove(key));
        }
    });
    assert!(map.is_empty());
    Timings { build, delete }
}

fn bench_std(insertion_order: &[u64], deletion_order: &[u64]) -> Timings {
    let mut map = BTreeMap::new();
    let build = time(|| {
        for (value, &key) in insertion_order.iter().enumerate() {
            black_box(map.insert(key, value));
        }
    });
    let delete = time(|| {
        for key in deletion_order {
            black_box(map.remove(key));
        }
    });
    assert!(map.is_empty());
    Timings { build, delete }
}

fn time(work: impl FnOnce()) -> Duration {
    let start = Instant::now();
    work();
    start.elapsed()
}

#[derive(Clone, Copy)]
struct Summary {
    median: Duration,
    min: Duration,
    max: Duration,
}

#[derive(Clone, Copy)]
struct RatioSummary {
    median: f64,
    min: f64,
    max: f64,
}

fn summarize(samples: &[Timings], select: impl Fn(&Timings) -> Duration) -> Summary {
    let mut durations: Vec<_> = samples.iter().map(select).collect();
    durations.sort_unstable();
    Summary {
        median: durations[durations.len() / 2],
        min: durations[0],
        max: durations[durations.len() - 1],
    }
}

fn summarize_ratios(
    bplus_samples: &[Timings],
    std_samples: &[Timings],
    select: impl Fn(&Timings) -> Duration,
) -> RatioSummary {
    let mut ratios: Vec<_> = bplus_samples
        .iter()
        .zip(std_samples)
        .map(|(bplus, std)| select(bplus).as_secs_f64() / select(std).as_secs_f64())
        .collect();
    ratios.sort_unstable_by(f64::total_cmp);
    RatioSummary {
        median: ratios[ratios.len() / 2],
        min: ratios[0],
        max: ratios[ratios.len() - 1],
    }
}

fn print_summary(label: &str, item_count: usize, summary: Summary) {
    let throughput = item_count as f64 / summary.median.as_secs_f64() / 1e6;
    println!(
        "{label:<18} {:>8.4}s ({throughput:>6.2} Mops/s), range {:>8.4}–{:>8.4}s",
        summary.median.as_secs_f64(),
        summary.min.as_secs_f64(),
        summary.max.as_secs_f64(),
    );
}
