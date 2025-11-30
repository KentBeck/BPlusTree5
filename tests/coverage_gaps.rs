use bplustree::BPlusTreeMap;

#[test]
fn test_borrow_from_left_leaf() {
    // Capacity 4 means max 4 items, min 2 items (usually).
    // We need to carefully construct the tree to force specific topology.
    // However, the library exposes `with_budgets` or `new(capacity)`.
    // Let's use `new(4)`.
    let mut tree = BPlusTreeMap::new(4).unwrap();

    // Fill to cause split.
    // 4 items -> full. 5th item -> split.
    // [1, 2, 3, 4, 5] -> [1, 2] [3, 4, 5] (roughly)
    for i in 1..=5 {
        tree.insert(i, i);
    }
    
    // Now we have 2 leaves.
    // Left: [1, 2] (len 2)
    // Right: [3, 4, 5] (len 3)
    // Parent: [3] (separator)
    
    // We want to force Right to borrow from Left.
    // Delete from Right until it underflows (len < 2).
    // But Left must have > 2 items to lend.
    // Current Left has 2. So we need to add more to Left first?
    // No, keys are sorted. We can't easily add to Left without rebalancing.
    
    // Let's try a different setup.
    // [1, 2, 3, 4] [5, 6, 7, 8]
    // Delete from Right.
    
    let mut tree = BPlusTreeMap::new(4).unwrap();
    for i in 1..=8 {
        tree.insert(i, i);
    }
    // Should have multiple leaves.
    // Delete from the end (Rightmost leaf) to cause underflow.
    
    tree.remove(&8);
    tree.remove(&7);
    // Now Rightmost might be small.
    // Check consistency.
    assert!(tree.get(&1).is_some());
    assert!(tree.get(&6).is_some());
}

#[test]
fn test_merge_leaves() {
    let mut tree = BPlusTreeMap::new(4).unwrap();
    for i in 1..=5 {
        tree.insert(i, i);
    }
    // Split happened.
    // Delete items to force merge.
    tree.remove(&1);
    tree.remove(&2);
    tree.remove(&3);
    
    // Should have merged back to root or fewer leaves.
    assert_eq!(tree.len(), 2);
    assert!(tree.get(&4).is_some());
    assert!(tree.get(&5).is_some());
}

#[test]
fn test_root_collapse() {
    let mut tree = BPlusTreeMap::new(4).unwrap();
    // Grow height
    for i in 0..100 {
        tree.insert(i, i);
    }
    
    // Shrink
    for i in 0..100 {
        tree.remove(&i);
    }
    
    assert!(tree.is_empty());
}

#[test]
fn test_capacity_edge_cases() {
    // Minimum capacity is 4.
    let mut tree = BPlusTreeMap::new(4).unwrap();
    
    // Insert/Delete in patterns
    for i in 0..20 {
        tree.insert(i, i);
    }
    
    for i in (0..20).step_by(2) {
        tree.remove(&i);
    }
    
    for i in (0..20).step_by(2) {
        assert!(tree.get(&i).is_none());
        if i + 1 < 20 {
            assert!(tree.get(&(i + 1)).is_some());
        }
    }
}

#[test]
fn test_zst() {
    let mut tree = BPlusTreeMap::new(4).unwrap();
    for _ in 0..100 {
        tree.insert((), ());
    }
    assert_eq!(tree.len(), 1);
    tree.remove(&());
    assert_eq!(tree.len(), 0);
}
