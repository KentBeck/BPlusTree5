use bplustree::{BPlusTreeMap, RECOMMENDED_BRANCH_PAYLOAD_BYTES, RECOMMENDED_LEAF_PAYLOAD_BYTES};
use core::mem::size_of;

#[test]
fn recommended_selects_capacities_from_u64_slot_sizes() {
    let tree = BPlusTreeMap::<u64, u64>::recommended().unwrap();

    assert_eq!(tree.leaf_layout().cap, 32);
    let expected_branch_cap =
        RECOMMENDED_BRANCH_PAYLOAD_BYTES / (size_of::<u64>() + size_of::<*mut u8>());
    assert_eq!(tree.branch_layout().cap as usize, expected_branch_cap);
}

#[test]
fn recommended_scales_down_for_wider_types() {
    type Wide = [u8; 64];
    let mut tree = BPlusTreeMap::<Wide, Wide>::recommended().unwrap();

    assert_eq!(tree.leaf_layout().cap, 4);
    let expected_branch_cap =
        RECOMMENDED_BRANCH_PAYLOAD_BYTES / (size_of::<Wide>() + size_of::<*mut u8>());
    assert_eq!(tree.branch_layout().cap as usize, expected_branch_cap);

    let wide = |number: u64| {
        let mut bytes = [0; 64];
        bytes[..8].copy_from_slice(&number.to_be_bytes());
        bytes
    };
    for number in 0..1_000 {
        assert_eq!(tree.insert(wide(number), wide(number * 2)), None);
    }
    for number in (0..1_000).step_by(2) {
        assert_eq!(tree.remove(&wide(number)), Some(wide(number * 2)));
    }
    assert!(tree.check_invariants());
}

#[test]
fn custom_targets_scale_each_node_kind_independently() {
    let tree = BPlusTreeMap::<u64, u64>::with_payload_targets(1_024, 2_048).unwrap();

    assert_eq!(tree.leaf_layout().cap, 64);
    let expected_branch_cap = 2_048 / (size_of::<u64>() + size_of::<*mut u8>());
    assert_eq!(tree.branch_layout().cap as usize, expected_branch_cap);
}

#[test]
fn targets_are_clamped_to_supported_capacities() {
    let tiny = BPlusTreeMap::<u64, u64>::with_payload_targets(1, 1).unwrap();
    assert_eq!(tiny.leaf_layout().cap, 4);
    assert_eq!(tiny.branch_layout().cap, 4);

    let huge = BPlusTreeMap::<u64, u64>::with_payload_targets(usize::MAX, usize::MAX).unwrap();
    assert_eq!(huge.leaf_layout().cap, u16::MAX);
    assert_eq!(huge.branch_layout().cap, u16::MAX);
}

#[test]
fn zero_sized_leaf_slots_do_not_divide_by_zero() {
    let tree = BPlusTreeMap::<(), ()>::recommended().unwrap();

    assert_eq!(tree.leaf_layout().cap, u16::MAX);
}

#[test]
fn recommended_tree_supports_normal_map_operations() {
    let mut tree = BPlusTreeMap::recommended().unwrap();
    for key in 0_u64..10_000 {
        assert_eq!(tree.insert(key, key * 2), None);
    }
    for key in (0_u64..10_000).step_by(3) {
        assert_eq!(tree.remove(&key), Some(key * 2));
    }

    assert_eq!(RECOMMENDED_LEAF_PAYLOAD_BYTES, 512);
    assert_eq!(RECOMMENDED_BRANCH_PAYLOAD_BYTES, 4_096);
    assert_eq!(tree.len(), 6_666);
    assert!(tree.check_invariants());
}
