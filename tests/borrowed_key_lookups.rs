//! Lookups, removals, and ranges accept any borrowed form of the key type,
//! matching `std::collections::BTreeMap`, and the map is `Send`/`Sync`
//! whenever its contents are.

use bplustree::BPlusTreeMap;
use std::ops::Bound;

fn sample() -> BPlusTreeMap<String, u32> {
    let mut map = BPlusTreeMap::new(4).unwrap();
    for (i, w) in ["apple", "banana", "cherry", "date", "elder", "fig", "grape"]
        .iter()
        .enumerate()
    {
        map.insert(w.to_string(), i as u32);
    }
    map
}

#[test]
fn get_and_contains_by_str() {
    let map = sample();
    assert_eq!(map.get("cherry"), Some(&2));
    assert!(map.contains_key("fig"));
    assert!(!map.contains_key("kiwi"));
    assert_eq!(map.get_item("kiwi").ok(), None);
}

#[test]
fn get_mut_and_remove_by_str() {
    let mut map = sample();
    *map.get_mut("date").unwrap() += 10;
    assert_eq!(map.get("date"), Some(&13));
    assert_eq!(map.remove("banana"), Some(1));
    assert_eq!(map.remove("banana"), None);
    assert_eq!(map.len(), 6);
    assert!(map.check_invariants());
}

#[test]
fn range_by_str_bounds() {
    use std::ops::Bound::{Excluded, Included, Unbounded};
    let map = sample();
    let by = |r: (Bound<&str>, Bound<&str>)| -> Vec<&str> {
        map.range::<str, _>(r).map(|(k, _)| k.as_str()).collect()
    };
    assert_eq!(
        by((Included("banana"), Excluded("elder"))),
        ["banana", "cherry", "date"]
    );
    assert_eq!(
        by((Unbounded, Included("cherry"))),
        ["apple", "banana", "cherry"]
    );
    assert_eq!(by((Included("fig"), Unbounded)), ["fig", "grape"]);
    assert_eq!(by((Excluded("fig"), Unbounded)), ["grape"]);
}

#[test]
fn owned_key_lookups_still_work() {
    let map = sample();
    assert_eq!(map.get(&"apple".to_string()), Some(&0));
    let keys: Vec<&String> = map
        .range("b".to_string().."d".to_string())
        .map(|(k, _)| k)
        .collect();
    assert_eq!(keys, [&"banana".to_string(), &"cherry".to_string()]);
}

#[test]
fn map_is_send_and_sync_when_contents_are() {
    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}
    assert_send::<BPlusTreeMap<u64, String>>();
    assert_sync::<BPlusTreeMap<u64, String>>();
    let map = sample();
    let total: u32 = std::thread::scope(|s| s.spawn(|| map.values().sum()).join().unwrap());
    assert_eq!(total, 21);
}

#[test]
fn mutable_iteration() {
    let mut map = BPlusTreeMap::new(4).unwrap();
    for i in 0..1000u32 {
        map.insert(i, i);
    }
    for (k, v) in map.items_mut() {
        *v += *k;
    }
    for v in map.values_mut().rev() {
        *v += 1;
    }
    for (_, v) in map.range_mut(100..200) {
        *v = 0;
    }
    assert_eq!(map.get(&5), Some(&11));
    assert_eq!(map.get(&150), Some(&0));
    assert_eq!(map.get(&999), Some(&1999));
    assert!(map.check_invariants());
}
