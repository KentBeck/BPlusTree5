#[cfg(not(feature = "delete_profile"))]
fn main() {
    eprintln!(
        "enable deletion counters with: \
         cargo run --release --features delete_profile --bin profile_delete_detailed"
    );
}

#[cfg(feature = "delete_profile")]
fn main() {
    profile::run();
}

#[cfg(feature = "delete_profile")]
mod profile {
    use bplustree::{BPlusTreeMap, DeleteProfile};
    use std::env;
    use std::hint::black_box;
    use std::time::Instant;

    const DEFAULT_ITEMS: usize = 1_000_000;
    const DEFAULT_LEAF_CAP: usize = 32;
    const DEFAULT_BRANCH_CAP: usize = 256;

    pub fn run() {
        // Usage: profile_delete_detailed [items=1000000] [leaf_cap=32]
        //                                 [branch_cap=256]
        let item_count = parse_arg(1, DEFAULT_ITEMS);
        let leaf_cap = parse_arg(2, DEFAULT_LEAF_CAP);
        let branch_cap = parse_arg(3, DEFAULT_BRANCH_CAP);
        assert!(item_count > 0, "items must be greater than zero");

        let insertion_order = generate_keys(item_count);
        let deletion_order = shuffled(&insertion_order);
        let mut map = BPlusTreeMap::with_caps(leaf_cap, branch_cap).expect("valid capacities");
        for (value, &key) in insertion_order.iter().enumerate() {
            black_box(map.insert(key, value));
        }
        let initial_leaf_count = map.leaf_count();

        map.reset_delete_profile();
        let start = Instant::now();
        for key in &deletion_order {
            black_box(map.remove(key));
        }
        let elapsed = start.elapsed();
        let counters = map.delete_profile();

        assert!(map.is_empty());
        assert!(map.check_invariants());

        println!("Delete Structural Profile");
        println!("=========================");
        println!("items: {item_count}");
        println!("leaf/branch capacity: {leaf_cap}/{branch_cap}");
        println!("initial leaves: {initial_leaf_count}");
        println!(
            "delete time: {:.4}s ({:.2} Mops/s)\n",
            elapsed.as_secs_f64(),
            item_count as f64 / elapsed.as_secs_f64() / 1e6
        );
        print_counters(counters, item_count);

        black_box(map);
    }

    fn parse_arg<T: std::str::FromStr>(index: usize, default: T) -> T {
        env::args()
            .nth(index)
            .and_then(|value| value.parse().ok())
            .unwrap_or(default)
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

    fn print_counters(profile: DeleteProfile, item_count: usize) {
        println!("operation                  count       per removal");
        println!("---------------------------------------------------");
        print_counter(
            "leaf rebalance checks",
            profile.leaf_rebalance_checks,
            item_count,
        );
        print_counter("leaf borrows", profile.leaf_borrows, item_count);
        print_counter("leaf merges", profile.leaf_merges, item_count);
        print_counter(
            "branch rebalance checks",
            profile.branch_rebalance_checks,
            item_count,
        );
        print_counter("branch borrows", profile.branch_borrows, item_count);
        print_counter("branch merges", profile.branch_merges, item_count);
        print_counter("leaf deallocations", profile.leaf_deallocations, item_count);
        print_counter(
            "branch deallocations",
            profile.branch_deallocations,
            item_count,
        );
        print_counter("root collapses", profile.root_collapses, item_count);
    }

    fn print_counter(label: &str, count: usize, item_count: usize) {
        println!(
            "{label:<25} {count:>9} {:>17.6}",
            count as f64 / item_count as f64
        );
    }
}
