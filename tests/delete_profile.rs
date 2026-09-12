#![cfg(feature = "delete_profile")]

use bplustree::{BPlusTreeMap, DeleteProfile};

#[test]
fn delete_profile_counts_repairs_and_can_be_reset() {
    const ITEM_COUNT: usize = 1_000;
    let mut tree = BPlusTreeMap::new(4).unwrap();
    for key in 0..ITEM_COUNT {
        tree.insert(key, key);
    }

    tree.reset_delete_profile();
    assert_eq!(tree.delete_profile(), DeleteProfile::default());
    assert_eq!(tree.remove(&ITEM_COUNT), None);
    assert_eq!(tree.delete_profile(), DeleteProfile::default());

    for index in 0..ITEM_COUNT {
        let key = index.wrapping_mul(919) % ITEM_COUNT;
        assert_eq!(tree.remove(&key), Some(key));
    }

    let profile = tree.delete_profile();
    assert!(profile.leaf_rebalance_checks > 0);
    assert!(profile.leaf_rebalance_checks < ITEM_COUNT);
    assert!(profile.leaf_merges > 0);
    assert!(profile.branch_rebalance_checks > 0);
    assert!(profile.branch_rebalance_checks < profile.leaf_rebalance_checks);
    assert!(profile.branch_merges > 0);
    assert!(profile.leaf_deallocations > 0);
    assert!(profile.branch_deallocations > 0);
    assert!(profile.root_collapses > 0);
    assert!(tree.is_empty());
    assert!(tree.check_invariants());

    tree.reset_delete_profile();
    assert_eq!(tree.delete_profile(), DeleteProfile::default());
}
