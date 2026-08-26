use bplustree::BPlusTreeMap;
use std::hint::black_box;

fn main() {
    let n = 200_000usize;
    let mut m = BPlusTreeMap::new(128).unwrap();
    for i in 0..n as u64 {
        m.insert(i.wrapping_mul(0x9E3779B97F4A7C15), i);
    }
    black_box(m.first());
}
