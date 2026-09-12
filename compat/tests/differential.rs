//! Drives `bplustree_compat::BTreeMap` and `std::collections::BTreeMap`
//! with the same random operation stream and checks that every observable
//! result agrees.

use bplustree_compat::{BTreeMap, BTreeSet, Entry};
use std::collections::BTreeMap as StdMap;
use std::ops::Bound;

struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn check_same(ours: &BTreeMap<u32, String>, theirs: &StdMap<u32, String>) {
    assert_eq!(ours.len(), theirs.len());
    assert!(ours.iter().eq(theirs.iter()), "forward iteration differs");
    assert!(
        ours.iter().rev().eq(theirs.iter().rev()),
        "backward iteration differs"
    );
    assert_eq!(ours.first_key_value(), theirs.first_key_value());
    assert_eq!(ours.last_key_value(), theirs.last_key_value());
    assert!(ours.as_tree().check_invariants());
}

#[test]
fn random_ops_match_std() {
    for seed in 0..8u64 {
        let mut rng = Lcg(seed * 7919 + 1);
        let mut ours: BTreeMap<u32, String> =
            BTreeMap::with_node_capacity(4 + (seed as usize % 3) * 4);
        let mut theirs: StdMap<u32, String> = StdMap::new();
        let key_space = 200;
        for step in 0..4000 {
            let k = rng.below(key_space) as u32;
            match rng.below(12) {
                0..=3 => {
                    let v = format!("{step}");
                    assert_eq!(ours.insert(k, v.clone()), theirs.insert(k, v));
                }
                4..=5 => assert_eq!(ours.remove(&k), theirs.remove(&k)),
                6 => assert_eq!(ours.get(&k), theirs.get(&k)),
                7 => {
                    let lo = rng.below(key_space) as u32;
                    let hi = rng.below(key_space) as u32;
                    let (lo, hi) = (lo.min(hi), lo.max(hi));
                    assert!(ours.range(lo..hi).eq(theirs.range(lo..hi)));
                    assert!(ours.range(lo..=hi).rev().eq(theirs.range(lo..=hi).rev()));
                    assert!(ours
                        .range((Bound::Excluded(lo), Bound::Unbounded))
                        .eq(theirs.range((Bound::Excluded(lo), Bound::Unbounded))));
                }
                8 => match (ours.entry(k), theirs.entry(k)) {
                    (
                        Entry::Occupied(mut a),
                        std::collections::btree_map::Entry::Occupied(mut b),
                    ) => {
                        assert_eq!(a.get(), b.get());
                        a.get_mut().push('!');
                        b.get_mut().push('!');
                    }
                    (Entry::Vacant(a), std::collections::btree_map::Entry::Vacant(b)) => {
                        assert_eq!(a.insert("new".into()), b.insert("new".into()));
                    }
                    _ => panic!("entry kinds differ for {k}"),
                },
                9 => assert_eq!(ours.pop_first(), theirs.pop_first()),
                10 => assert_eq!(ours.pop_last(), theirs.pop_last()),
                _ => {
                    let keep = rng.below(3) as u32;
                    ours.retain(|k, _| k % 3 != keep);
                    theirs.retain(|k, _| k % 3 != keep);
                }
            }
            if step % 97 == 0 {
                check_same(&ours, &theirs);
            }
        }
        check_same(&ours, &theirs);

        for (_, v) in ours.iter_mut() {
            v.push('?');
        }
        for (_, v) in theirs.iter_mut() {
            v.push('?');
        }
        for (_, v) in ours.range_mut(50..150) {
            v.clear();
        }
        for (_, v) in theirs.range_mut(50..150) {
            v.clear();
        }
        check_same(&ours, &theirs);

        let split_at = 100;
        let tail_ours = ours.split_off(&split_at);
        let tail_theirs = theirs.split_off(&split_at);
        check_same(&ours, &theirs);
        check_same(&tail_ours, &tail_theirs);

        let cloned = ours.clone();
        assert_eq!(cloned, ours);
        assert_eq!(format!("{:?}", cloned), format!("{:?}", theirs));

        let mut merged = ours.clone();
        let mut tail = tail_ours.clone();
        merged.append(&mut tail);
        assert!(tail.is_empty());
        let mut merged_std = theirs.clone();
        let mut tail_std = tail_theirs.clone();
        merged_std.append(&mut tail_std);
        check_same(&merged, &merged_std);

        let owned: Vec<(u32, String)> = merged.into_iter().collect();
        let owned_std: Vec<(u32, String)> = merged_std.into_iter().collect();
        assert_eq!(owned, owned_std);
    }
}

#[test]
fn set_behaves_like_std() {
    let mut ours: BTreeSet<String> = BTreeSet::new();
    let mut theirs = std::collections::BTreeSet::new();
    for w in ["pear", "apple", "fig", "apple", "kiwi", "date"] {
        assert_eq!(ours.insert(w.to_string()), theirs.insert(w.to_string()));
    }
    assert!(ours.iter().eq(theirs.iter()));
    assert!(ours.contains("fig"));
    assert_eq!(ours.take("fig"), theirs.take("fig"));
    assert_eq!(ours.first(), theirs.first());
    assert_eq!(ours.pop_last(), theirs.pop_last());
    let r: Vec<&String> = ours
        .range::<str, _>((Bound::Included("b"), Bound::Unbounded))
        .collect();
    assert_eq!(r, ["date", "kiwi"]);
    assert_eq!(ours.len(), theirs.len());
    let collected: std::collections::BTreeSet<String> = ours.into_iter().collect();
    assert_eq!(collected, theirs);
}

#[test]
fn from_array_index_and_extend() {
    let mut m = BTreeMap::from([(3, "c"), (1, "a")]);
    m.extend([(2, "b")]);
    assert_eq!(m[&2], "b");
    assert_eq!(m.keys().copied().collect::<Vec<_>>(), [1, 2, 3]);
    assert_eq!(m.values().copied().collect::<Vec<_>>(), ["a", "b", "c"]);
    assert_eq!(m.into_values().collect::<Vec<_>>(), ["a", "b", "c"]);
}

#[cfg(feature = "serde")]
#[test]
fn serde_round_trip() {
    let m: BTreeMap<String, u32> = [("b".to_string(), 2), ("a".to_string(), 1)]
        .into_iter()
        .collect();
    let text = serde_json::to_string(&m).unwrap();
    assert_eq!(text, r#"{"a":1,"b":2}"#);
    let back: BTreeMap<String, u32> = serde_json::from_str(&text).unwrap();
    assert_eq!(back, m);
}
