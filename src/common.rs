#[cfg(any(test, feature = "internal"))]
use alloc::format;
#[cfg(any(test, feature = "internal"))]
use alloc::string::String;
use core::borrow::Borrow;
use core::ptr::NonNull;

use crate::layout::NodeTag;
use crate::node::{self, BranchRef, LeafRef};
use crate::BPlusTreeMap;

#[cfg(any(test, feature = "internal"))]
pub(crate) struct ValidationState<K> {
    pub(crate) total_items: usize,
    pub(crate) prev_leaf: Option<NonNull<u8>>,
    pub(crate) prev_key: Option<K>,
}

#[cfg(any(test, feature = "internal"))]
impl<K: Ord + Clone> ValidationState<K> {
    /// Check this leaf's keys against the leaf visited immediately before it,
    /// then make it the reference point for the next leaf in traversal order.
    #[inline(always)]
    fn observe_leaf(&mut self, leaf: NonNull<u8>, keys: &[K]) -> Result<(), String> {
        self.prev_leaf = Some(leaf);

        if let Some(prev_key) = &self.prev_key {
            if keys[0] <= *prev_key {
                return Err("Leaf keys not globally increasing".into());
            }
        }
        self.prev_key = Some(keys[keys.len() - 1].clone());
        self.total_items += keys.len();
        Ok(())
    }
}

impl<K, V> BPlusTreeMap<K, V> {
    /// View `node` as a leaf of this map.
    ///
    /// SAFETY: `node` must be a live leaf of this map; see [`LeafRef::new`].
    #[inline(always)]
    pub(crate) unsafe fn leaf(&self, node: NonNull<u8>) -> LeafRef<K, V> {
        LeafRef::new(node, &self.leaf_layout)
    }

    /// View `node` as a branch of this map.
    ///
    /// SAFETY: `node` must be a live branch of this map; see
    /// [`BranchRef::new`].
    #[inline(always)]
    pub(crate) unsafe fn branch(&self, node: NonNull<u8>) -> BranchRef<K> {
        BranchRef::new(node, &self.branch_layout)
    }

    /// Number of keys a node currently holds. The header is shared by both
    /// node kinds, so this works for leaves and branches alike.
    #[inline(always)]
    pub(crate) unsafe fn node_len(&self, node: NonNull<u8>) -> usize {
        node::len(node)
    }

    /// Centralized binary search for keys in a node.
    /// This function will be optimized for performance in future iterations.
    #[inline(always)]
    pub(crate) fn binary_search_keys<T, Q>(&self, keys: &[T], target: &Q) -> Result<usize, usize>
    where
        T: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        keys.binary_search_by(|k| k.borrow().cmp(target))
    }

    /// Splice `new_right` into the leaf chain immediately after `leaf`.
    /// Inverse of `unlink_leaf`; the two are the only places that edit the
    /// sibling chain, so the doubly-linked invariant is auditable here.
    #[inline]
    pub(crate) unsafe fn link_leaf_after(&self, leaf: NonNull<u8>, new_right: NonNull<u8>) {
        let l = self.leaf(leaf);
        let r = self.leaf(new_right);
        let old_next = l.next();

        l.set_next(Some(new_right));
        r.set_next(old_next);
        r.set_prev(Some(leaf));
        if let Some(old) = old_next {
            self.leaf(old).set_prev(Some(new_right));
        }
    }

    /// Splice `leaf` out of the leaf chain and clear its own links.
    /// Inverse of `link_leaf_after`.
    #[inline]
    pub(crate) unsafe fn unlink_leaf(&self, leaf: NonNull<u8>) {
        let l = self.leaf(leaf);
        let next = l.next();
        let prev = l.prev();

        if let Some(prev_leaf) = prev {
            self.leaf(prev_leaf).set_next(next);
        }
        if let Some(next_leaf) = next {
            self.leaf(next_leaf).set_prev(prev);
        }

        l.set_next(None);
        l.set_prev(None);
    }
}

impl<K: Ord, V> BPlusTreeMap<K, V> {
    /// The child after the separators `<= key`. Lean: `lastChild` of the
    /// `sepLE` prefix, the descent `insertRec`, `removeRec` and `leafForKey`
    /// share; `front_lt_of_route` (`Proofs/Tree.lean`) is what it guarantees.
    /// The slot is never null: a branch holds `len + 1` children and the
    /// index is at most `len`, and on the heap model the same descent never
    /// meets a missing node (`insertRecH_sim`, `removeRecH_sim`,
    /// `leafForKeyH_sim`).
    #[inline(always)]
    pub(crate) unsafe fn child_for_key<Q>(
        &self,
        branch: NonNull<u8>,
        key: &Q,
    ) -> (NonNull<u8>, usize)
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let b = self.branch(branch);
        let child_idx = match self.binary_search_keys(b.keys(), key) {
            Ok(i) => i + 1,
            Err(i) => i,
        };
        debug_assert!(child_idx <= b.len(), "child index out of range");
        (b.child(child_idx), child_idx)
    }

    /// Lean: `leafForKey_spec` (`Proofs/Read.lean`): the entries split into
    /// those before this leaf (all below `key`), the leaf, and those after
    /// (all above), so any entry with this key is in the leaf reached.
    /// Lean: `leafForKeyH_sim` (`Proofs/HeapRead.lean`): the leaf reached
    /// splits the sibling chain where `leafForKey` splits the entries.
    #[inline(always)]
    pub(crate) fn leaf_for_key<Q>(&self, key: &Q) -> Option<NonNull<u8>>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let mut cur = self.root?;
        unsafe {
            loop {
                match node::tag(cur) {
                    NodeTag::Leaf => return Some(cur),
                    NodeTag::Branch => cur = self.child_for_key(cur, key).0,
                }
            }
        }
    }

    /// Lean: `leftmostLeaf_spec` (`Proofs/Read.lean`): it starts the entry
    /// list and is nonempty unless it is the root.
    #[inline]
    pub(crate) fn leftmost_leaf(&self) -> Option<NonNull<u8>> {
        let mut cur = self.root?;
        unsafe {
            loop {
                match node::tag(cur) {
                    NodeTag::Leaf => return Some(cur),
                    NodeTag::Branch => cur = self.branch(cur).child_or_null(0)?,
                }
            }
        }
    }
}

impl<K: Ord + Clone, V> BPlusTreeMap<K, V> {
    /// Lean: `rightmostLeaf_spec` (`Proofs/Read.lean`), the mirror image.
    #[inline]
    pub(crate) fn rightmost_leaf(&self) -> Option<NonNull<u8>> {
        let mut cur = self.root?;
        unsafe {
            loop {
                match node::tag(cur) {
                    NodeTag::Leaf => return Some(cur),
                    NodeTag::Branch => {
                        let b = self.branch(cur);
                        cur = b.child_or_null(b.len())?;
                    }
                }
            }
        }
    }

    #[cfg(any(test, feature = "internal"))]
    #[doc(hidden)]
    pub fn is_leaf_root(&self) -> bool {
        match self.root {
            None => true,
            Some(p) => unsafe { node::tag(p) == NodeTag::Leaf },
        }
    }

    #[cfg(any(test, feature = "internal"))]
    #[doc(hidden)]
    pub fn leaf_count(&self) -> usize {
        let mut count = 0usize;
        let mut cur = self.leftmost_leaf();
        unsafe {
            while let Some(leaf) = cur {
                if node::tag(leaf) != NodeTag::Leaf {
                    break;
                }
                count += 1;
                cur = self.leaf(leaf).next();
            }
        }
        count
    }

    #[cfg(any(test, feature = "internal"))]
    #[doc(hidden)]
    pub fn check_invariants(&self) -> bool {
        self.check_invariants_detailed().is_ok()
    }

    /// Check the structural invariant: every node within capacity and, below
    /// the root, at or above minimum fill; keys strictly increasing in every
    /// node and inside the bounds the ancestors' separators impose; every
    /// leaf at the same depth; the leaf sibling chain in tree order; and the
    /// stored length equal to the number of entries. `checkInvariants` in
    /// `lean/BPlusTree/Model/Check.lean` mirrors it arm for arm (minus the
    /// pointer checks) and `checkInvariants_iff` proves it accepts exactly
    /// the trees the model's `WF` describes.
    #[cfg(any(test, feature = "internal"))]
    #[doc(hidden)]
    pub fn check_invariants_detailed(&self) -> Result<(), String> {
        let mut state = ValidationState {
            total_items: 0,
            prev_leaf: None,
            prev_key: None,
        };

        unsafe {
            if let Some(root) = self.root {
                self.validate_node(root, None, None, true, &mut state)?;

                if let Some(last_leaf) = state.prev_leaf {
                    if self.leaf(last_leaf).next().is_some() {
                        return Err("Tail leaf next pointer should be null".into());
                    }
                }
            }
        }

        if state.total_items != self.entry_count {
            return Err(format!(
                "Stored length is {}, but the leaf entry count is {}",
                self.entry_count, state.total_items
            ));
        }

        Ok(())
    }

    /// Validate a subtree and return its height: 0 for a leaf, one more than
    /// its children for a branch, all of whose children must agree.
    #[cfg(any(test, feature = "internal"))]
    pub(crate) unsafe fn validate_node(
        &self,
        node: NonNull<u8>,
        lower: Option<&K>,
        upper: Option<&K>,
        is_root: bool,
        state: &mut ValidationState<K>,
    ) -> Result<usize, String> {
        match node::tag(node) {
            NodeTag::Leaf => self.validate_leaf(node, lower, upper, is_root, state),
            NodeTag::Branch => self.validate_branch(node, lower, upper, is_root, state),
        }
    }

    #[cfg(any(test, feature = "internal"))]
    pub(crate) unsafe fn validate_leaf(
        &self,
        leaf: NonNull<u8>,
        lower: Option<&K>,
        upper: Option<&K>,
        is_root: bool,
        state: &mut ValidationState<K>,
    ) -> Result<usize, String> {
        let l = self.leaf(leaf);
        self.validate_leaf_occupancy(l.len(), is_root)?;
        if l.len() == 0 {
            return Ok(0);
        }

        let keys = l.keys();
        self.validate_leaf_key_order_and_bounds(keys, lower, upper)?;
        self.validate_leaf_chain_position(l, state.prev_leaf)?;
        state.observe_leaf(leaf, keys)?;
        Ok(0)
    }

    #[cfg(any(test, feature = "internal"))]
    fn validate_leaf_occupancy(&self, len: usize, is_root: bool) -> Result<(), String> {
        let cap = self.leaf_layout.cap as usize;
        if len > cap {
            return Err(format!("Leaf has {} keys but capacity is {}", len, cap));
        }
        if len == 0 && !is_root {
            return Err("Non-root leaf is empty".into());
        }

        let min_required = self.min_leaf_len();
        if !is_root && len < min_required {
            return Err(format!(
                "Leaf underfull: has {} keys, minimum is {}",
                len, min_required
            ));
        }
        Ok(())
    }

    #[cfg(any(test, feature = "internal"))]
    fn validate_leaf_key_order_and_bounds(
        &self,
        keys: &[K],
        lower: Option<&K>,
        upper: Option<&K>,
    ) -> Result<(), String> {
        for window in keys.windows(2) {
            if window[0] >= window[1] {
                return Err("Leaf keys not strictly increasing".into());
            }
        }

        if let Some(low) = lower {
            if keys[0] < *low {
                return Err("Leaf keys fall below lower bound".into());
            }
        }
        if let Some(high) = upper {
            if keys[keys.len() - 1] >= *high {
                return Err("Leaf keys exceed upper bound".into());
            }
        }
        Ok(())
    }

    #[cfg(any(test, feature = "internal"))]
    unsafe fn validate_leaf_chain_position(
        &self,
        leaf: LeafRef<K, V>,
        expected_prev: Option<NonNull<u8>>,
    ) -> Result<(), String> {
        if let Some(prev_leaf) = expected_prev {
            if self.leaf(prev_leaf).next() != Some(leaf.node()) {
                return Err("Leaf next pointer mismatch".into());
            }
        }

        if leaf.has_prev_link() {
            match expected_prev {
                Some(prev) => {
                    if leaf.prev() != Some(prev) {
                        return Err("Leaf prev pointer mismatch".into());
                    }
                }
                None => {
                    if leaf.prev().is_some() {
                        return Err("First leaf prev pointer should be null".into());
                    }
                }
            }
        }
        Ok(())
    }

    #[cfg(any(test, feature = "internal"))]
    pub(crate) unsafe fn validate_branch(
        &self,
        branch: NonNull<u8>,
        lower: Option<&K>,
        upper: Option<&K>,
        is_root: bool,
        state: &mut ValidationState<K>,
    ) -> Result<usize, String> {
        let b = self.branch(branch);
        let len = b.len();
        let cap = b.cap();

        if len > cap {
            return Err(format!("Branch has {} keys but capacity is {}", len, cap));
        }

        // A root branch always has a separator too: root collapse hands a
        // lone child over instead of keeping a one-child root.
        if len == 0 {
            return Err(if is_root {
                "Root branch has no keys".into()
            } else {
                "Non-root branch has no keys".into()
            });
        }

        let min_required = self.min_branch_len();
        if !is_root && len < min_required {
            return Err(format!(
                "Branch underfull: has {} keys, minimum is {}",
                len, min_required
            ));
        }

        let keys = b.keys();
        for window in keys.windows(2) {
            if window[0] >= window[1] {
                return Err("Branch keys not strictly increasing".into());
            }
        }

        if let Some(low) = lower {
            if keys[0] < *low {
                return Err("Branch keys fall below lower bound".into());
            }
        }
        if let Some(high) = upper {
            if keys[len - 1] >= *high {
                return Err("Branch keys exceed upper bound".into());
            }
        }

        // Every child sits at the same height, so every leaf is at the
        // same depth (the model's `WF` builds this in as its height index).
        let mut depth: Option<usize> = None;
        for i in 0..=len {
            let child = match b.child_or_null(i) {
                Some(child) => child,
                None => return Err("Branch child pointer is null".into()),
            };

            let lower_bound = if i == 0 { lower } else { Some(&keys[i - 1]) };
            let upper_bound = if i == len { upper } else { Some(&keys[i]) };

            let child_depth = self.validate_node(child, lower_bound, upper_bound, false, state)?;
            match depth {
                None => depth = Some(child_depth),
                Some(d) if d != child_depth => {
                    return Err("Leaves at different depths".into());
                }
                Some(_) => {}
            }
        }

        Ok(depth.map_or(0, |d| d + 1))
    }

    /// Lean: `minLeafLen`, the leaf fill `WF` requires below the root.
    #[inline(always)]
    pub(crate) fn min_leaf_len(&self) -> usize {
        let cap = self.leaf_layout.cap as usize;
        cap / 2
    }

    /// Lean: `minBranchLen_eq` (`Proofs/Delete.lean`): for `cap >= 3` this is
    /// `cap / 2`, the branch fill `WF` requires; `with_caps` enforces 4, so
    /// the `cap <= 2` arm is unreachable.
    #[inline(always)]
    pub(crate) fn min_branch_len(&self) -> usize {
        let cap = self.branch_layout.cap as usize;
        if cap <= 2 {
            1
        } else {
            cap / 2
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::BPlusTreeMap;

    #[test]
    fn validation_rejects_a_stale_entry_count() {
        let mut tree = BPlusTreeMap::with_capacity(4);
        tree.insert(1, 10);

        tree.entry_count += 1;

        assert_eq!(
            tree.check_invariants_detailed().unwrap_err(),
            "Stored length is 2, but the leaf entry count is 1"
        );
    }

    /// Replace the root's first child (a branch) with a leaf spliced into the
    /// sibling chain so that every other check passes: only the depth check
    /// can reject it.
    #[test]
    fn validation_rejects_leaves_at_different_depths() {
        use crate::layout::NodeTag;
        use crate::node;
        use crate::node_alloc::{alloc_leaf_block, free_leaf_block};

        let mut tree = BPlusTreeMap::<i64, i64>::with_capacities(4, 4);
        for k in 0..64 {
            tree.insert(k, k);
        }
        assert!(tree.check_invariants());

        unsafe {
            let root = tree.root.unwrap();
            assert_eq!(node::tag(root), NodeTag::Branch);
            let rb = tree.branch(root);
            let child0 = rb.child(0);
            assert_eq!(
                node::tag(child0),
                NodeTag::Branch,
                "the test needs a tree of height at least 2"
            );

            // The first leaf under the root's second child: the leaf that
            // will follow the fake one in traversal order.
            let mut cur = rb.child(1);
            while node::tag(cur) == NodeTag::Branch {
                cur = tree.branch(cur).child(0);
            }
            let next_leaf = tree.leaf(cur);
            let saved_prev = next_leaf.prev();

            // A leaf with two keys below every real key, at minimum fill,
            // linked ahead of `next_leaf`.
            let fake = alloc_leaf_block(&tree.leaf_layout).unwrap();
            let f = tree.leaf(fake);
            f.insert(0, -2, 0);
            f.insert(1, -1, 0);
            f.set_next(Some(cur));
            next_leaf.set_prev(Some(fake));
            rb.set_child(0, fake);

            let err = tree.check_invariants_detailed().unwrap_err();

            rb.set_child(0, child0);
            next_leaf.set_prev(saved_prev);
            free_leaf_block(fake, &tree.leaf_layout);

            assert_eq!(err, "Leaves at different depths");
        }
        assert!(tree.check_invariants());
    }
}

/// 64-bit FNV-1a over the bytes fed through `fmt::Write`. The Lean replay
/// computes the same function over the same rendering, so equal digests
/// mean equal shapes (up to a 2^-64 accidental collision); neither side
/// is adversarial, so a cryptographic hash would buy nothing here.
#[cfg(any(test, feature = "internal"))]
pub struct ShapeHasher(u64);

#[cfg(any(test, feature = "internal"))]
impl ShapeHasher {
    pub const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    pub const PRIME: u64 = 0x0000_0100_0000_01b3;

    pub fn new() -> Self {
        ShapeHasher(Self::OFFSET)
    }

    pub fn finish(&self) -> u64 {
        self.0
    }
}

#[cfg(any(test, feature = "internal"))]
impl Default for ShapeHasher {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(any(test, feature = "internal"))]
impl core::fmt::Write for ShapeHasher {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for b in s.bytes() {
            self.0 ^= b as u64;
            self.0 = self.0.wrapping_mul(Self::PRIME);
        }
        Ok(())
    }
}

#[cfg(any(test, feature = "internal"))]
impl<K: Ord + Clone + core::fmt::Debug, V: core::fmt::Debug> BPlusTreeMap<K, V> {
    /// Render the tree's shape for the Lean replay harness (`lean/Replay`).
    /// A leaf is `(k:v k:v ...)`; a branch is `[child sep child sep child]`
    /// with the children rendered recursively. The Lean model renders its
    /// tree the same way, so equal strings mean equal shapes.
    pub fn dump_shape(&self) -> String {
        let mut out = String::new();
        self.render_shape(&mut out);
        out
    }

    /// FNV-1a digest of `dump_shape()`, computed without building the string.
    pub fn shape_hash(&self) -> u64 {
        let mut h = ShapeHasher::new();
        self.render_shape(&mut h);
        h.finish()
    }

    fn render_shape<W: core::fmt::Write>(&self, out: &mut W) {
        match self.root {
            Some(root) => unsafe { self.dump_node(root, out) },
            None => {
                let _ = out.write_str("()");
            }
        }
    }

    unsafe fn dump_node<W: core::fmt::Write>(&self, node: NonNull<u8>, out: &mut W) {
        match node::tag(node) {
            NodeTag::Leaf => {
                let l = self.leaf(node);
                let _ = out.write_char('(');
                for i in 0..l.len() {
                    if i > 0 {
                        let _ = out.write_char(' ');
                    }
                    let _ = write!(out, "{:?}:{:?}", l.key(i), l.val(i));
                }
                let _ = out.write_char(')');
            }
            NodeTag::Branch => {
                let b = self.branch(node);
                let _ = out.write_char('[');
                for i in 0..=b.len() {
                    if i > 0 {
                        let _ = write!(out, " {:?} ", b.key(i - 1));
                    }
                    match b.child_or_null(i) {
                        Some(child) => self.dump_node(child, out),
                        None => {
                            let _ = out.write_str("null");
                        }
                    }
                }
                let _ = out.write_char(']');
            }
        }
    }
}
