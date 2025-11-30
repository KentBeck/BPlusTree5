use bplustree::BPlusTreeMap;
use std::hint::black_box;
use std::time::Instant;

struct Lcg {
    state: u64,
}

impl Lcg {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.state
    }

    fn next_range(&mut self, max: u64) -> u64 {
        self.next() % max
    }
}

fn main() {
    let n_ops = 200_000_000;
    let max_key = 10_000_000;
    let mut tree = BPlusTreeMap::new(128).unwrap();
    let mut rng = Lcg::new(12345);

    println!("Running {} random operations...", n_ops);
    let start = Instant::now();

    for i in 0..n_ops {
        let op = rng.next_range(100);
        let key = rng.next_range(max_key);

        if op < 50 {
            // 50% Insert
            let val = key;
            black_box(tree.insert(key, val));
        } else if op < 90 {
            // 40% Get
            black_box(tree.get(&key));
        } else {
            // 10% Remove
            black_box(tree.remove(&key));
        }
    }

    let duration = start.elapsed();
    println!("Done in {:.3}s", duration.as_secs_f64());
    println!("Final size: {}", tree.len());
}
