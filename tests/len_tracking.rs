use bplustree::BPlusTreeMap;

#[test]
fn len_tracks_cardinality_across_mutations() {
    let mut tree = BPlusTreeMap::new(4).unwrap();

    assert_eq!(tree.len(), 0);
    assert!(tree.is_empty());

    for key in 0..257 {
        assert_eq!(tree.insert(key, key), None);
    }
    assert_eq!(tree.len(), 257);
    assert!(!tree.is_empty());
    assert!(tree.check_invariants());

    for key in (0..257).step_by(3) {
        assert_eq!(tree.insert(key, -key), Some(key));
    }
    assert_eq!(tree.len(), 257, "replacing values must not change len");
    assert!(tree.check_invariants());

    for key in (0..257).step_by(2) {
        assert!(tree.remove(&key).is_some());
    }
    assert_eq!(tree.len(), 128);
    assert_eq!(tree.remove(&1_000), None);
    assert_eq!(
        tree.len(),
        128,
        "removing a missing key must not change len"
    );
    assert!(tree.check_invariants());

    tree.clear();
    assert_eq!(tree.len(), 0);
    assert!(tree.is_empty());
    assert!(tree.check_invariants());

    assert_eq!(tree.insert(7, 11), None);
    assert_eq!(tree.len(), 1, "len must keep working after clear and reuse");
    assert!(tree.check_invariants());
}
