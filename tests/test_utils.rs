// Each integration test crate includes this file as a module and uses only
// a subset of the helpers, so the per-crate dead-code lint is not meaningful.
#![allow(dead_code)]

/// Comprehensive test utilities to eliminate massive test duplication
/// This module provides reusable patterns for adversarial testing and common operations
use bplustree::BPlusTreeMap;

// ============================================================================
// TREE CREATION UTILITIES - Replace 185 instances of BPlusTreeMap::new()
// ============================================================================

/// Standard tree with capacity 4 (most common pattern)
pub fn create_tree_4() -> BPlusTreeMap<i32, String> {
    BPlusTreeMap::new(4).expect("Failed to create tree with capacity 4")
}

/// Standard tree with capacity 5 (for odd capacity testing)
pub fn create_tree_5() -> BPlusTreeMap<i32, String> {
    BPlusTreeMap::new(5).expect("Failed to create tree with capacity 5")
}

/// Standard tree with capacity 6 (for specific testing scenarios)
pub fn create_tree_6() -> BPlusTreeMap<i32, String> {
    BPlusTreeMap::new(6).expect("Failed to create tree with capacity 6")
}

/// Generic tree creation with custom capacity
pub fn create_tree_capacity(capacity: usize) -> BPlusTreeMap<i32, String> {
    BPlusTreeMap::new(capacity).expect(&format!("Failed to create tree with capacity {}", capacity))
}

/// Generic integer tree creation with custom capacity
pub fn create_tree_capacity_int(capacity: usize) -> BPlusTreeMap<i32, i32> {
    BPlusTreeMap::new(capacity).expect(&format!(
        "Failed to create integer tree with capacity {}",
        capacity
    ))
}

// ============================================================================
// DATA POPULATION UTILITIES - Replace 176 for-loop patterns
// ============================================================================

/// Insert sequential data 0..count with string values
pub fn insert_sequential_range(tree: &mut BPlusTreeMap<i32, String>, count: usize) {
    for i in 0..count {
        tree.insert(i as i32, format!("value_{}", i));
    }
}

/// Insert sequential data 0..count with integer values
pub fn insert_sequential_range_int(tree: &mut BPlusTreeMap<i32, i32>, count: usize) {
    for i in 0..count {
        tree.insert(i as i32, i as i32);
    }
}

/// Insert data with custom key multiplier (common pattern: i * multiplier)
pub fn insert_with_multiplier(tree: &mut BPlusTreeMap<i32, String>, count: usize, multiplier: i32) {
    for i in 0..count {
        let key = (i as i32) * multiplier;
        tree.insert(key, format!("value_{}", i));
    }
}

/// Insert data with custom key multiplier for integer trees
pub fn insert_with_multiplier_int(
    tree: &mut BPlusTreeMap<i32, i32>,
    count: usize,
    multiplier: i32,
) {
    for i in 0..count {
        let key = (i as i32) * multiplier;
        tree.insert(key, i as i32);
    }
}

/// Insert data with offset and multiplier (key = offset + i * multiplier)
pub fn insert_with_offset_multiplier(
    tree: &mut BPlusTreeMap<i32, String>,
    count: usize,
    offset: i32,
    multiplier: i32,
) {
    for i in 0..count {
        let key = offset + (i as i32) * multiplier;
        tree.insert(key, format!("value_{}", i));
    }
}

/// Insert data with custom key and value functions
pub fn insert_with_custom_fn<F, G>(
    tree: &mut BPlusTreeMap<i32, String>,
    count: usize,
    key_fn: F,
    value_fn: G,
) where
    F: Fn(usize) -> i32,
    G: Fn(usize) -> String,
{
    for i in 0..count {
        let key = key_fn(i);
        let value = value_fn(i);
        tree.insert(key, value);
    }
}

/// Insert sequential data start..end with string values
pub fn insert_range(tree: &mut BPlusTreeMap<i32, String>, start: usize, end: usize) {
    for i in start..end {
        tree.insert(i as i32, format!("value_{}", i));
    }
}

// ============================================================================
// COMBINED TREE CREATION AND POPULATION - Most common patterns
// ============================================================================

/// Create tree with capacity 4 and insert 0..count sequential data
pub fn create_tree_4_with_data(count: usize) -> BPlusTreeMap<i32, String> {
    let mut tree = create_tree_4();
    insert_sequential_range(&mut tree, count);
    tree
}

/// Create tree with custom capacity and insert 0..count sequential data
pub fn create_tree_with_data(capacity: usize, count: usize) -> BPlusTreeMap<i32, String> {
    let mut tree = create_tree_capacity(capacity);
    insert_sequential_range(&mut tree, count);
    tree
}

// ============================================================================
// INVARIANT CHECKING UTILITIES - Replace 44 instances
// ============================================================================

/// Standard invariant check with panic on failure
pub fn assert_invariants(tree: &BPlusTreeMap<i32, String>, context: &str) {
    if let Err(e) = tree.check_invariants_detailed() {
        panic!("Invariant violation in {}: {}", context, e);
    }
}

// ============================================================================
// ADVERSARIAL ATTACK PATTERNS - Common deletion patterns
// ============================================================================

/// Execute deletion range attack (delete items from start to end)
pub fn deletion_range_attack(tree: &mut BPlusTreeMap<i32, String>, start: usize, end: usize) {
    for i in start..end {
        tree.remove(&(i as i32));
    }
}

// ============================================================================
// VERIFICATION UTILITIES
// ============================================================================

/// Verify tree ordering after operations
pub fn verify_ordering(tree: &BPlusTreeMap<i32, String>) {
    let items: Vec<_> = tree.items().collect();
    for i in 1..items.len() {
        if items[i - 1].0 >= items[i].0 {
            panic!("Items out of order after operations!");
        }
    }
}

/// Verify tree has expected number of items
pub fn verify_item_count(tree: &BPlusTreeMap<i32, String>, expected: usize, context: &str) {
    let actual = tree.len();
    if actual != expected {
        panic!(
            "Item count mismatch in {}: Expected {} items, got {}",
            context, expected, actual
        );
    }
}

// ============================================================================
// LEGACY COMPATIBILITY - Keep existing test function names working
// ============================================================================

/// Legacy compatibility - create attack tree
pub fn create_attack_tree(capacity: usize) -> BPlusTreeMap<i32, String> {
    create_tree_capacity(capacity)
}

/// Legacy compatibility - populate tree with sequential data
pub fn populate_sequential(tree: &mut BPlusTreeMap<i32, String>, count: usize) {
    insert_sequential_range(tree, count);
}

/// Legacy compatibility - verify attack failed
pub fn assert_attack_failed(tree: &BPlusTreeMap<i32, String>, context: &str) {
    assert_invariants(tree, context);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_utilities_basic_functionality() {
        let mut tree = create_tree_4();
        insert_sequential_range(&mut tree, 10);

        assert_eq!(tree.len(), 10);
        verify_ordering(&tree);
        assert_invariants(&tree, "basic functionality test");
    }

    #[test]
    fn test_combined_creation_utilities() {
        let tree = create_tree_4_with_data(20);
        assert_eq!(tree.len(), 20);
        assert_invariants(&tree, "combined creation test");
        verify_ordering(&tree);
    }

    #[test]
    fn test_attack_patterns() {
        let mut tree = create_tree_4_with_data(50);

        // Test deletion range attack
        deletion_range_attack(&mut tree, 10, 40);
        assert_eq!(tree.len(), 20);
        assert_invariants(&tree, "deletion range attack");
        verify_ordering(&tree);
    }
}
