//! Drives `BPlusTreeMap` and `std::collections::BTreeMap` through the same
//! operations and checks that every observable result agrees, and the same
//! for `BPlusTreeSet` against `std::collections::BTreeSet`.
//!
//! This is the test that says what "the API of the standard library's map"
//! means: if it compiles here against both types and the answers match, a
//! caller can swap one for the other.

use bplustree::{BPlusTreeMap, BPlusTreeSet, Entry};
use std::collections::btree_map::Entry as StdEntry;
use std::collections::{BTreeMap as StdMap, BTreeSet as StdSet};
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

fn agree(ours: &BPlusTreeMap<u32, String>, theirs: &StdMap<u32, String>) {
    assert_eq!(ours.len(), theirs.len());
    assert_eq!(ours.is_empty(), theirs.is_empty());
    assert!(ours.iter().eq(theirs.iter()), "forward iteration differs");
    assert!(
        ours.iter().rev().eq(theirs.iter().rev()),
        "backward iteration differs"
    );
    assert!(ours.keys().eq(theirs.keys()), "keys differ");
    assert!(ours.values().eq(theirs.values()), "values differ");
    assert_eq!(ours.first_key_value(), theirs.first_key_value());
    assert_eq!(ours.last_key_value(), theirs.last_key_value());
    assert_eq!(ours.iter().len(), theirs.iter().len());
    assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));
    assert!(ours.check_invariants(), "tree invariants broken");
}

/// Miri runs the same code a few thousand times slower, so the random walk
/// is shortened there. Everything it covers, it still covers.
#[cfg(miri)]
const SEEDS: u64 = 2;
#[cfg(not(miri))]
const SEEDS: u64 = 8;
#[cfg(miri)]
const STEPS: usize = 300;
#[cfg(not(miri))]
const STEPS: usize = 4000;

#[test]
fn random_operations_match_std() {
    for seed in 0..SEEDS {
        let mut rng = Lcg(seed * 7919 + 1);
        // Small nodes so splits, merges and borrows happen constantly.
        let mut ours: BPlusTreeMap<u32, String> =
            BPlusTreeMap::with_capacity(4 + (seed as usize % 3) * 4);
        let mut theirs: StdMap<u32, String> = StdMap::new();
        let key_space = 200;

        for step in 0..STEPS {
            let key = rng.below(key_space) as u32;
            match rng.below(14) {
                0..=3 => {
                    let value = format!("{step}");
                    assert_eq!(ours.insert(key, value.clone()), theirs.insert(key, value));
                }
                4..=5 => assert_eq!(ours.remove(&key), theirs.remove(&key)),
                6 => {
                    assert_eq!(ours.get(&key), theirs.get(&key));
                    assert_eq!(ours.get_key_value(&key), theirs.get_key_value(&key));
                    assert_eq!(ours.contains_key(&key), theirs.contains_key(&key));
                }
                7 => assert_eq!(ours.remove_entry(&key), theirs.remove_entry(&key)),
                8 => {
                    let lo = rng.below(key_space) as u32;
                    let hi = rng.below(key_space) as u32;
                    let (lo, hi) = (lo.min(hi), lo.max(hi));
                    assert!(ours.range(lo..hi).eq(theirs.range(lo..hi)));
                    assert!(ours.range(lo..=hi).rev().eq(theirs.range(lo..=hi).rev()));
                    assert!(ours
                        .range((Bound::Excluded(lo), Bound::Unbounded))
                        .eq(theirs.range((Bound::Excluded(lo), Bound::Unbounded))));
                }
                9 => match (ours.entry(key), theirs.entry(key)) {
                    (Entry::Occupied(mut a), StdEntry::Occupied(mut b)) => {
                        assert_eq!(a.key(), b.key());
                        assert_eq!(a.get(), b.get());
                        a.get_mut().push('!');
                        b.get_mut().push('!');
                        assert_eq!(a.insert("replaced".into()), b.insert("replaced".into()));
                    }
                    (Entry::Vacant(a), StdEntry::Vacant(b)) => {
                        assert_eq!(a.key(), b.key());
                        assert_eq!(a.insert("new".into()), b.insert("new".into()));
                    }
                    _ => panic!("entry was vacant on one side and occupied on the other"),
                },
                10 => {
                    let ours_v = ours.entry(key).or_insert_with(|| "or".into());
                    let theirs_v = theirs.entry(key).or_insert_with(|| "or".into());
                    assert_eq!(ours_v, theirs_v);
                    assert_eq!(
                        ours.entry(key).and_modify(|v| v.push('m')).or_default(),
                        theirs.entry(key).and_modify(|v| v.push('m')).or_default()
                    );
                }
                11 => assert_eq!(ours.pop_first(), theirs.pop_first()),
                12 => assert_eq!(ours.pop_last(), theirs.pop_last()),
                _ => {
                    let keep = rng.below(3) as u32;
                    ours.retain(|k, _| k % 3 != keep);
                    theirs.retain(|k, _| k % 3 != keep);
                }
            }
            if step % 97 == 0 {
                agree(&ours, &theirs);
            }
        }
        agree(&ours, &theirs);

        // Mutable iteration.
        for (_, v) in ours.iter_mut() {
            v.push('?');
        }
        for (_, v) in theirs.iter_mut() {
            v.push('?');
        }
        for v in ours.values_mut() {
            v.push('=');
        }
        for v in theirs.values_mut() {
            v.push('=');
        }
        for (_, v) in ours.range_mut(50..150) {
            v.clear();
        }
        for (_, v) in theirs.range_mut(50..150) {
            v.clear();
        }
        agree(&ours, &theirs);

        // First and last entries.
        if let (Some(mut a), Some(mut b)) = (ours.first_entry(), theirs.first_entry()) {
            assert_eq!(a.key(), b.key());
            assert_eq!(a.insert("first".into()), b.insert("first".into()));
        }
        if let (Some(a), Some(b)) = (ours.last_entry(), theirs.last_entry()) {
            assert_eq!(a.remove_entry(), b.remove_entry());
        }
        agree(&ours, &theirs);

        // Splitting and re-joining.
        let mut tail_ours = ours.split_off(&100);
        let mut tail_theirs = theirs.split_off(&100);
        agree(&ours, &theirs);
        agree(&tail_ours, &tail_theirs);

        // Traits: clone, equality, ordering, hashing.
        let cloned = ours.clone();
        assert_eq!(cloned, ours);
        assert_eq!(cloned.cmp(&ours), std::cmp::Ordering::Equal);
        assert_eq!(hash_of(&cloned), hash_of(&ours));
        agree(&cloned, &theirs);

        ours.append(&mut tail_ours);
        theirs.append(&mut tail_theirs);
        assert!(tail_ours.is_empty());
        assert!(tail_theirs.is_empty());
        agree(&ours, &theirs);

        // Owned iteration, both directions.
        let owned: Vec<(u32, String)> = ours.clone().into_iter().collect();
        let owned_std: Vec<(u32, String)> = theirs.clone().into_iter().collect();
        assert_eq!(owned, owned_std);
        let back: Vec<(u32, String)> = ours.clone().into_iter().rev().collect();
        let back_std: Vec<(u32, String)> = theirs.clone().into_iter().rev().collect();
        assert_eq!(back, back_std);
        assert_eq!(
            ours.clone().into_keys().collect::<Vec<_>>(),
            theirs.clone().into_keys().collect::<Vec<_>>()
        );
        assert_eq!(
            ours.into_values().collect::<Vec<_>>(),
            theirs.into_values().collect::<Vec<_>>()
        );
    }
}

fn hash_of<T: std::hash::Hash>(value: &T) -> u64 {
    use std::hash::{BuildHasher, BuildHasherDefault};
    BuildHasherDefault::<std::collections::hash_map::DefaultHasher>::default().hash_one(value)
}

#[test]
fn ordering_between_maps_matches_std() {
    let pairs: [&[(u32, &str)]; 5] = [
        &[],
        &[(1, "a")],
        &[(1, "a"), (2, "b")],
        &[(1, "b")],
        &[(2, "a")],
    ];
    for left in pairs {
        for right in pairs {
            let ours_l: BPlusTreeMap<u32, &str> = left.iter().copied().collect();
            let ours_r: BPlusTreeMap<u32, &str> = right.iter().copied().collect();
            let std_l: StdMap<u32, &str> = left.iter().copied().collect();
            let std_r: StdMap<u32, &str> = right.iter().copied().collect();
            assert_eq!(ours_l.cmp(&ours_r), std_l.cmp(&std_r));
            assert_eq!(ours_l == ours_r, std_l == std_r);
            assert_eq!(
                ours_l.partial_cmp(&ours_r),
                std_l.partial_cmp(&std_r),
                "{left:?} vs {right:?}"
            );
        }
    }
}

#[test]
fn borrowed_keys_work_like_std() {
    let words = ["apple", "banana", "cherry", "date", "elder"];
    let mut ours: BPlusTreeMap<String, usize> = BPlusTreeMap::with_capacity(4);
    let mut theirs: StdMap<String, usize> = StdMap::new();
    for (i, w) in words.iter().enumerate() {
        ours.insert(w.to_string(), i);
        theirs.insert(w.to_string(), i);
    }

    // A &str probe against String keys, as std allows.
    assert_eq!(ours.get("cherry"), theirs.get("cherry"));
    assert_eq!(ours.get_mut("date"), theirs.get_mut("date"));
    assert_eq!(ours.contains_key("fig"), theirs.contains_key("fig"));
    assert_eq!(ours.get_key_value("elder"), theirs.get_key_value("elder"));
    // `Range<&str>` is not `RangeBounds<str>`, so a borrowed-key range is
    // spelled with explicit bounds, the same way it is with std.
    let bounds = (Bound::Included("banana"), Bound::Excluded("elder"));
    assert!(ours
        .range::<str, _>(bounds)
        .eq(theirs.range::<str, _>(bounds)));
    assert_eq!(ours.remove("banana"), theirs.remove("banana"));
    assert_eq!(ours.remove_entry("apple"), theirs.remove_entry("apple"));
    assert_eq!(
        ours.split_off("date").into_keys().collect::<Vec<_>>(),
        theirs.split_off("date").into_keys().collect::<Vec<_>>()
    );
    assert!(ours.iter().eq(theirs.iter()));

    // Index, which panics on a missing key just as std does.
    let map: BPlusTreeMap<String, usize> = [("k".to_string(), 7)].into_iter().collect();
    assert_eq!(map["k"], 7);
    assert!(std::panic::catch_unwind(|| map["missing"]).is_err());
}

#[test]
fn constructors_and_conversions_match_std() {
    let ours = BPlusTreeMap::from([(3, "c"), (1, "a"), (2, "b")]);
    let theirs = StdMap::from([(3, "c"), (1, "a"), (2, "b")]);
    assert!(ours.iter().eq(theirs.iter()));

    let ours: BPlusTreeMap<i32, &str> = Default::default();
    let theirs: StdMap<i32, &str> = Default::default();
    assert_eq!(ours.len(), theirs.len());

    let mut ours = BPlusTreeMap::new();
    let mut theirs = StdMap::new();
    ours.extend([(1, 'a'), (2, 'b')]);
    theirs.extend([(1, 'a'), (2, 'b')]);
    ours.extend([(&3, &'c')]);
    theirs.extend([(&3, &'c')]);
    assert!(ours.iter().eq(theirs.iter()));

    // Iterating over references, by value, and by mutable reference.
    assert!((&ours).into_iter().eq((&theirs).into_iter()));
    for (_, v) in &mut ours {
        v.make_ascii_uppercase();
    }
    for (_, v) in &mut theirs {
        v.make_ascii_uppercase();
    }
    assert!(ours.clone().into_iter().eq(theirs.clone().into_iter()));

    ours.clear();
    theirs.clear();
    assert!(ours.is_empty() && theirs.is_empty());
}

#[test]
fn set_matches_std() {
    let mut rng = Lcg(42);
    let mut ours: BPlusTreeSet<u32> = BPlusTreeSet::new();
    let mut theirs: StdSet<u32> = StdSet::new();
    for _ in 0..(STEPS * 3 / 4) {
        let value = rng.below(150) as u32;
        match rng.below(6) {
            0..=2 => assert_eq!(ours.insert(value), theirs.insert(value)),
            3 => assert_eq!(ours.remove(&value), theirs.remove(&value)),
            4 => assert_eq!(ours.take(&value), theirs.take(&value)),
            _ => assert_eq!(ours.contains(&value), theirs.contains(&value)),
        }
    }
    assert_eq!(ours.len(), theirs.len());
    assert!(ours.iter().eq(theirs.iter()));
    assert!(ours.iter().rev().eq(theirs.iter().rev()));
    assert_eq!(ours.first(), theirs.first());
    assert_eq!(ours.last(), theirs.last());
    assert!(ours.range(20..80).eq(theirs.range(20..80)));
    assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));

    let ours_b: BPlusTreeSet<u32> = (0..100).filter(|n| n % 3 == 0).collect();
    let theirs_b: StdSet<u32> = (0..100).filter(|n| n % 3 == 0).collect();
    assert!(ours.union(&ours_b).eq(theirs.union(&theirs_b)));
    assert!(ours
        .intersection(&ours_b)
        .eq(theirs.intersection(&theirs_b)));
    assert!(ours.difference(&ours_b).eq(theirs.difference(&theirs_b)));
    assert!(ours
        .symmetric_difference(&ours_b)
        .eq(theirs.symmetric_difference(&theirs_b)));
    assert_eq!(ours.is_subset(&ours_b), theirs.is_subset(&theirs_b));
    assert_eq!(ours.is_superset(&ours_b), theirs.is_superset(&theirs_b));
    assert_eq!(ours.is_disjoint(&ours_b), theirs.is_disjoint(&theirs_b));
    assert!((&ours | &ours_b).iter().eq((&theirs | &theirs_b).iter()));
    assert!((&ours & &ours_b).iter().eq((&theirs & &theirs_b).iter()));
    assert!((&ours ^ &ours_b).iter().eq((&theirs ^ &theirs_b).iter()));
    assert!((&ours - &ours_b).iter().eq((&theirs - &theirs_b).iter()));

    assert_eq!(
        ours.clone().into_iter().collect::<Vec<_>>(),
        theirs.clone().into_iter().collect::<Vec<_>>()
    );

    // Borrowed lookups and the rest of the surface.
    let ours_s: BPlusTreeSet<String> = ["a", "b", "c"].iter().map(|s| s.to_string()).collect();
    let theirs_s: StdSet<String> = ["a", "b", "c"].iter().map(|s| s.to_string()).collect();
    assert_eq!(ours_s.contains("b"), theirs_s.contains("b"));
    assert_eq!(ours_s.get("c"), theirs_s.get("c"));
    assert_eq!(ours_s, ours_s.clone());

    let mut ours_m = ours.clone();
    let mut theirs_m = theirs.clone();
    let mut ours_tail = ours_m.split_off(&75);
    let mut theirs_tail = theirs_m.split_off(&75);
    assert!(ours_m.iter().eq(theirs_m.iter()));
    assert!(ours_tail.iter().eq(theirs_tail.iter()));
    ours_m.append(&mut ours_tail);
    theirs_m.append(&mut theirs_tail);
    assert!(ours_m.iter().eq(theirs_m.iter()));
    ours_m.retain(|v| v % 2 == 0);
    theirs_m.retain(|v| v % 2 == 0);
    assert!(ours_m.iter().eq(theirs_m.iter()));
    assert_eq!(ours_m.pop_first(), theirs_m.pop_first());
    assert_eq!(ours_m.pop_last(), theirs_m.pop_last());
    assert!(ours_m.iter().eq(theirs_m.iter()));
}

#[test]
fn iterator_traits_match_std() {
    let ours: BPlusTreeMap<u32, u32> = (0..50).map(|n| (n, n * 2)).collect();
    let theirs: StdMap<u32, u32> = (0..50).map(|n| (n, n * 2)).collect();

    // ExactSizeIterator on the same iterators std has it on.
    assert_eq!(ours.iter().len(), theirs.iter().len());
    assert_eq!(ours.keys().len(), theirs.keys().len());
    assert_eq!(ours.values().len(), theirs.values().len());
    assert_eq!(
        ours.clone().into_iter().len(),
        theirs.clone().into_iter().len()
    );
    assert_eq!(ours.iter().size_hint(), theirs.iter().size_hint());

    // Interleaving both ends yields each entry once.
    let mut ours_it = ours.iter();
    let mut theirs_it = theirs.iter();
    for _ in 0..25 {
        assert_eq!(ours_it.next(), theirs_it.next());
        assert_eq!(ours_it.next_back(), theirs_it.next_back());
        assert_eq!(ours_it.len(), theirs_it.len());
    }
    assert_eq!(ours_it.next(), None);
    assert_eq!(ours_it.next_back(), None);

    // Fused: a spent iterator keeps saying None.
    let mut spent = ours.iter();
    while spent.next().is_some() {}
    assert_eq!(spent.next(), None);
    assert_eq!(spent.next(), None);

    assert_eq!(ours.iter().last(), theirs.iter().last());
    assert_eq!(ours.range(10..20).last(), theirs.range(10..20).last());
    assert_eq!(ours.range(10..20).count(), theirs.range(10..20).count());
}

#[cfg(feature = "serde")]
#[test]
fn serde_matches_std() {
    let ours: BPlusTreeMap<String, u32> = [("b".to_string(), 2), ("a".to_string(), 1)]
        .into_iter()
        .collect();
    let theirs: StdMap<String, u32> = [("b".to_string(), 2), ("a".to_string(), 1)]
        .into_iter()
        .collect();
    assert_eq!(
        serde_json::to_string(&ours).unwrap(),
        serde_json::to_string(&theirs).unwrap()
    );
    let back: BPlusTreeMap<String, u32> =
        serde_json::from_str(&serde_json::to_string(&ours).unwrap()).unwrap();
    assert_eq!(back, ours);

    let ours_set: BPlusTreeSet<u32> = (0..10).collect();
    let theirs_set: StdSet<u32> = (0..10).collect();
    assert_eq!(
        serde_json::to_string(&ours_set).unwrap(),
        serde_json::to_string(&theirs_set).unwrap()
    );
    let back: BPlusTreeSet<u32> =
        serde_json::from_str(&serde_json::to_string(&ours_set).unwrap()).unwrap();
    assert_eq!(back, ours_set);
}
