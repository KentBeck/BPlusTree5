//! Typed views of a node's memory.
//!
//! A node is one raw allocation whose fields sit at the offsets its
//! [`LeafLayout`] or [`BranchLayout`] computed. [`LeafRef`] and
//! [`BranchRef`] are the only places that turn those offsets into
//! pointers: every operation reads and writes a node through them, so the
//! byte layout can change without the operations noticing.
//!
//! A view is a base pointer plus a copy of the layout. Creating one is
//! `unsafe`: the caller promises `base` is a live node of that layout and
//! that no other access to the node overlaps the view's. From then on the
//! methods are as unchecked as the raw pointers were, so indices are the
//! caller's responsibility; `debug_assert`s catch a bad one in test builds.
//!
//! Occupancy is defined solely by the header's `len`. A slot past `len`
//! may hold stale bytes from an entry that was moved out, and is never
//! read or dropped.

use core::marker::PhantomData;
use core::ptr::{self, NonNull};

use crate::layout::{BranchLayout, LeafLayout, NodeHdr, NodeTag};

/// Whether `node` is a leaf or a branch.
#[inline(always)]
pub(crate) unsafe fn tag(node: NonNull<u8>) -> NodeTag {
    (*(node.as_ptr() as *const NodeHdr)).tag
}

/// Number of keys `node` holds. The header is shared by both node kinds,
/// so this works for leaves and branches alike.
#[inline(always)]
pub(crate) unsafe fn len(node: NonNull<u8>) -> usize {
    (*(node.as_ptr() as *const NodeHdr)).len as usize
}

/// A leaf node: `len` key/value pairs in two parallel arrays, plus links
/// to the neighbouring leaves.
pub(crate) struct LeafRef<K, V> {
    base: NonNull<u8>,
    layout: LeafLayout,
    _marker: PhantomData<(K, V)>,
}

impl<K, V> Clone for LeafRef<K, V> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<K, V> Copy for LeafRef<K, V> {}

impl<K, V> LeafRef<K, V> {
    /// View the leaf at `base`.
    ///
    /// SAFETY: `base` must point to a leaf block allocated for `layout`
    /// that stays allocated, and unshared with any conflicting access, for
    /// as long as the view or anything derived from it is used.
    #[inline(always)]
    pub(crate) unsafe fn new(base: NonNull<u8>, layout: &LeafLayout) -> Self {
        LeafRef {
            base,
            layout: *layout,
            _marker: PhantomData,
        }
    }

    /// The node this view reads.
    #[inline(always)]
    pub(crate) fn node(self) -> NonNull<u8> {
        self.base
    }

    #[inline(always)]
    fn hdr(self) -> *mut NodeHdr {
        self.base.as_ptr() as *mut NodeHdr
    }

    /// Number of entries the leaf holds.
    #[inline(always)]
    pub(crate) fn len(self) -> usize {
        unsafe { (*self.hdr()).len as usize }
    }

    #[inline(always)]
    pub(crate) fn set_len(self, len: usize) {
        debug_assert!(len <= self.cap(), "leaf length exceeds capacity");
        unsafe { (*self.hdr()).len = len as u16 }
    }

    /// Entries the leaf can hold.
    #[inline(always)]
    pub(crate) fn cap(self) -> usize {
        self.layout.cap as usize
    }

    #[inline(always)]
    pub(crate) fn is_full(self) -> bool {
        self.len() == self.cap()
    }

    /// Pointer to key slot `i`. The slot need not be occupied.
    #[inline(always)]
    pub(crate) fn key_ptr(self, i: usize) -> *mut K {
        debug_assert!(i <= self.cap(), "key slot out of range");
        unsafe { (self.base.as_ptr().add(self.layout.keys_off) as *mut K).add(i) }
    }

    /// Pointer to value slot `i`. The slot need not be occupied.
    #[inline(always)]
    pub(crate) fn val_ptr(self, i: usize) -> *mut V {
        debug_assert!(i <= self.cap(), "value slot out of range");
        unsafe { (self.base.as_ptr().add(self.layout.vals_off) as *mut V).add(i) }
    }

    /// The occupied keys, in order.
    #[inline(always)]
    pub(crate) fn keys<'a>(self) -> &'a [K] {
        unsafe { core::slice::from_raw_parts(self.key_ptr(0), self.len()) }
    }

    #[inline(always)]
    pub(crate) fn key<'a>(self, i: usize) -> &'a K {
        debug_assert!(i < self.len(), "key index out of range");
        unsafe { &*self.key_ptr(i) }
    }

    #[inline(always)]
    pub(crate) fn val<'a>(self, i: usize) -> &'a V {
        debug_assert!(i < self.len(), "value index out of range");
        unsafe { &*self.val_ptr(i) }
    }

    /// Replace the value in occupied slot `i`, returning the old one.
    #[inline(always)]
    pub(crate) fn replace_val(self, i: usize, value: V) -> V {
        debug_assert!(i < self.len(), "value index out of range");
        unsafe { ptr::replace(self.val_ptr(i), value) }
    }

    /// Insert an entry at `i`, shifting `[i..len)` one slot right. The leaf
    /// must not be full. Returns the value's slot.
    #[inline(always)]
    pub(crate) fn insert(self, i: usize, key: K, value: V) -> *mut V {
        let len = self.len();
        debug_assert!(i <= len, "insert index out of range");
        debug_assert!(len < self.cap(), "insert into a full leaf");
        unsafe {
            if i < len {
                ptr::copy(self.key_ptr(i), self.key_ptr(i + 1), len - i);
                ptr::copy(self.val_ptr(i), self.val_ptr(i + 1), len - i);
            }
            ptr::write(self.key_ptr(i), key);
            ptr::write(self.val_ptr(i), value);
        }
        self.set_len(len + 1);
        self.val_ptr(i)
    }

    /// Take the entry at `i` out, shifting `[i+1..len)` one slot left.
    #[inline(always)]
    pub(crate) fn remove(self, i: usize) -> (K, V) {
        let len = self.len();
        debug_assert!(i < len, "remove index out of range");
        unsafe {
            let key = ptr::read(self.key_ptr(i));
            let value = ptr::read(self.val_ptr(i));
            if i + 1 < len {
                ptr::copy(self.key_ptr(i + 1), self.key_ptr(i), len - i - 1);
                ptr::copy(self.val_ptr(i + 1), self.val_ptr(i), len - i - 1);
            }
            self.set_len(len - 1);
            (key, value)
        }
    }

    /// Move `count` entries starting at `src` into `dst` starting at
    /// `dst_idx`, adjusting both lengths. The moved-out slots at the end of
    /// `self` become stale; `dst`'s slots `[dst_idx..dst_idx + count)` must
    /// be unoccupied and the two leaves distinct.
    #[inline(always)]
    pub(crate) fn move_tail_to(self, src: usize, dst: Self, dst_idx: usize, count: usize) {
        debug_assert!(src + count == self.len(), "move_tail_to moves a suffix");
        debug_assert!(dst_idx == dst.len(), "move_tail_to appends to dst");
        debug_assert!(dst_idx + count <= dst.cap(), "move would overflow dst");
        unsafe {
            ptr::copy_nonoverlapping(self.key_ptr(src), dst.key_ptr(dst_idx), count);
            ptr::copy_nonoverlapping(self.val_ptr(src), dst.val_ptr(dst_idx), count);
        }
        self.set_len(src);
        dst.set_len(dst_idx + count);
    }

    /// Drop every occupied key and value, leaving the leaf empty.
    pub(crate) fn drop_entries(self) {
        let len = self.len();
        unsafe {
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.key_ptr(0), len));
            ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.val_ptr(0), len));
        }
        self.set_len(0);
    }

    #[inline(always)]
    fn next_slot(self) -> *mut *mut u8 {
        unsafe { self.base.as_ptr().add(self.layout.next_off) as *mut *mut u8 }
    }

    #[inline(always)]
    fn prev_slot(self) -> Option<*mut *mut u8> {
        self.layout
            .prev_off
            .map(|off| unsafe { self.base.as_ptr().add(off) as *mut *mut u8 })
    }

    /// The leaf after this one in key order, if any.
    #[inline(always)]
    pub(crate) fn next(self) -> Option<NonNull<u8>> {
        unsafe { NonNull::new(*self.next_slot()) }
    }

    #[inline(always)]
    pub(crate) fn set_next(self, next: Option<NonNull<u8>>) {
        unsafe { *self.next_slot() = next.map_or(ptr::null_mut(), NonNull::as_ptr) }
    }

    /// The leaf before this one in key order, if any. Always `None` when
    /// the layout has no backward link.
    #[inline(always)]
    pub(crate) fn prev(self) -> Option<NonNull<u8>> {
        unsafe { NonNull::new(*self.prev_slot()?) }
    }

    /// Set the backward link. A no-op when the layout has none.
    #[inline(always)]
    pub(crate) fn set_prev(self, prev: Option<NonNull<u8>>) {
        if let Some(slot) = self.prev_slot() {
            unsafe { *slot = prev.map_or(ptr::null_mut(), NonNull::as_ptr) }
        }
    }

    /// Whether the layout stores a backward link at all.
    #[inline(always)]
    pub(crate) fn has_prev_link(self) -> bool {
        self.layout.prev_off.is_some()
    }
}

/// A branch node: `len` separator keys and `len + 1` child pointers,
/// child `i` holding the keys between separators `i - 1` and `i`.
pub(crate) struct BranchRef<K> {
    base: NonNull<u8>,
    layout: BranchLayout,
    _marker: PhantomData<K>,
}

impl<K> Clone for BranchRef<K> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<K> Copy for BranchRef<K> {}

impl<K> BranchRef<K> {
    /// View the branch at `base`.
    ///
    /// SAFETY: as for [`LeafRef::new`], with a branch block and layout.
    #[inline(always)]
    pub(crate) unsafe fn new(base: NonNull<u8>, layout: &BranchLayout) -> Self {
        BranchRef {
            base,
            layout: *layout,
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    fn hdr(self) -> *mut NodeHdr {
        self.base.as_ptr() as *mut NodeHdr
    }

    /// Number of separator keys. The branch holds one more child.
    #[inline(always)]
    pub(crate) fn len(self) -> usize {
        unsafe { (*self.hdr()).len as usize }
    }

    #[inline(always)]
    pub(crate) fn set_len(self, len: usize) {
        debug_assert!(len <= self.cap(), "branch length exceeds capacity");
        unsafe { (*self.hdr()).len = len as u16 }
    }

    /// Separators the branch can hold.
    #[inline(always)]
    pub(crate) fn cap(self) -> usize {
        self.layout.cap as usize
    }

    #[inline(always)]
    pub(crate) fn is_full(self) -> bool {
        self.len() == self.cap()
    }

    /// Pointer to key slot `i`. The slot need not be occupied.
    #[inline(always)]
    pub(crate) fn key_ptr(self, i: usize) -> *mut K {
        debug_assert!(i <= self.cap(), "key slot out of range");
        unsafe { (self.base.as_ptr().add(self.layout.keys_off) as *mut K).add(i) }
    }

    /// Pointer to child slot `i`. A branch has `cap + 1` child slots, and
    /// a shift may name the slot one past them as an empty range's end.
    #[inline(always)]
    fn child_slot(self, i: usize) -> *mut *mut u8 {
        debug_assert!(i <= self.cap() + 1, "child slot out of range");
        unsafe { (self.base.as_ptr().add(self.layout.children_off) as *mut *mut u8).add(i) }
    }

    /// The occupied separators, in order.
    #[inline(always)]
    pub(crate) fn keys<'a>(self) -> &'a [K] {
        unsafe { core::slice::from_raw_parts(self.key_ptr(0), self.len()) }
    }

    #[inline(always)]
    pub(crate) fn key<'a>(self, i: usize) -> &'a K {
        debug_assert!(i < self.len(), "key index out of range");
        unsafe { &*self.key_ptr(i) }
    }

    /// Replace separator `i`, returning the old one.
    #[inline(always)]
    pub(crate) fn replace_key(self, i: usize, key: K) -> K {
        debug_assert!(i < self.len(), "key index out of range");
        unsafe { ptr::replace(self.key_ptr(i), key) }
    }

    /// Child `i`, which a well-formed branch never leaves null.
    #[inline(always)]
    pub(crate) fn child(self, i: usize) -> NonNull<u8> {
        debug_assert!(i <= self.len(), "child index out of range");
        let p = unsafe { *self.child_slot(i) };
        debug_assert!(!p.is_null(), "branch child pointer is null");
        unsafe { NonNull::new_unchecked(p) }
    }

    /// Child `i`, or `None` if the slot is null. For walks that must not
    /// trust the tree's shape.
    #[inline(always)]
    pub(crate) fn child_or_null(self, i: usize) -> Option<NonNull<u8>> {
        debug_assert!(i <= self.len(), "child index out of range");
        unsafe { NonNull::new(*self.child_slot(i)) }
    }

    #[inline(always)]
    pub(crate) fn set_child(self, i: usize, child: NonNull<u8>) {
        debug_assert!(i <= self.len(), "child index out of range");
        unsafe { *self.child_slot(i) = child.as_ptr() }
    }

    /// Insert separator `key` at `i` with `right` as the child after it,
    /// shifting keys `[i..len)` and children `[i+1..=len)` one slot right.
    /// The branch must not be full. Inverse of [`BranchRef::remove_entry`].
    #[inline(always)]
    pub(crate) fn insert_entry(self, i: usize, key: K, right: NonNull<u8>) {
        let len = self.len();
        debug_assert!(i <= len, "insert index out of range");
        debug_assert!(len < self.cap(), "insert into a full branch");
        unsafe {
            ptr::copy(self.key_ptr(i), self.key_ptr(i + 1), len - i);
            ptr::copy(self.child_slot(i + 1), self.child_slot(i + 2), len - i);
            ptr::write(self.key_ptr(i), key);
            *self.child_slot(i + 1) = right.as_ptr();
        }
        self.set_len(len + 1);
    }

    /// Remove separator `i` and the child after it, shifting keys
    /// `[i+1..len)` and children `[i+2..=len)` one slot left. Returns the
    /// separator; the caller owns the removed child's node.
    #[inline(always)]
    pub(crate) fn remove_entry(self, i: usize) -> K {
        let len = self.len();
        debug_assert!(i < len, "separator index out of range");
        unsafe {
            let key = ptr::read(self.key_ptr(i));
            ptr::copy(self.key_ptr(i + 1), self.key_ptr(i), len - i - 1);
            ptr::copy(self.child_slot(i + 2), self.child_slot(i + 1), len - i - 1);
            self.set_len(len - 1);
            key
        }
    }

    /// Append separator `key` and the child after it.
    #[inline(always)]
    pub(crate) fn push_entry(self, key: K, right: NonNull<u8>) {
        let len = self.len();
        debug_assert!(len < self.cap(), "push into a full branch");
        unsafe {
            ptr::write(self.key_ptr(len), key);
            *self.child_slot(len + 1) = right.as_ptr();
        }
        self.set_len(len + 1);
    }

    /// Make `key` the first separator and `left` the first child, shifting
    /// every key and child one slot right. Inverse of
    /// [`BranchRef::pop_front`].
    #[inline(always)]
    pub(crate) fn push_front(self, key: K, left: NonNull<u8>) {
        let len = self.len();
        debug_assert!(len < self.cap(), "push into a full branch");
        unsafe {
            ptr::copy(self.key_ptr(0), self.key_ptr(1), len);
            ptr::copy(self.child_slot(0), self.child_slot(1), len + 1);
            ptr::write(self.key_ptr(0), key);
            *self.child_slot(0) = left.as_ptr();
        }
        self.set_len(len + 1);
    }

    /// Take the first separator and the first child out, shifting every
    /// remaining key and child one slot left. Inverse of
    /// [`BranchRef::push_front`].
    #[inline(always)]
    pub(crate) fn pop_front(self) -> (K, NonNull<u8>) {
        let child = self.child(0);
        (self.pop_front_key(), child)
    }

    /// Take the first separator out and shift every remaining key and
    /// child one slot left, so the child after the separator becomes the
    /// first child. Whatever child slot 0 held is overwritten unread: for
    /// a slot the caller never filled, or has already taken.
    #[inline(always)]
    pub(crate) fn pop_front_key(self) -> K {
        let len = self.len();
        debug_assert!(len > 0, "pop from an empty branch");
        unsafe {
            let key = ptr::read(self.key_ptr(0));
            ptr::copy(self.key_ptr(1), self.key_ptr(0), len - 1);
            ptr::copy(self.child_slot(1), self.child_slot(0), len);
            self.set_len(len - 1);
            key
        }
    }

    /// Append `separator`, then every entry of `src`, leaving `src` empty:
    /// `src`'s keys follow the separator and its `len + 1` children follow
    /// `self`'s last child. The two branches must be distinct and the
    /// result must fit.
    #[inline(always)]
    pub(crate) fn absorb(self, separator: K, src: Self) {
        let len = self.len();
        let src_len = src.len();
        debug_assert!(len + 1 + src_len <= self.cap(), "absorb would overflow");
        unsafe {
            ptr::write(self.key_ptr(len), separator);
            ptr::copy_nonoverlapping(src.key_ptr(0), self.key_ptr(len + 1), src_len);
            ptr::copy_nonoverlapping(src.child_slot(0), self.child_slot(len + 1), src_len + 1);
        }
        self.set_len(len + 1 + src_len);
        src.set_len(0);
    }

    /// Move keys `[from..len)` into the empty branch `dst` as its keys
    /// `[0..)`, and the children after them, `[from+1..=len)`, as its
    /// children `[1..)`. `self` keeps keys `[0..from)` and children
    /// `[0..=from)`. `dst`'s child slot 0 is left for the caller to fill.
    #[inline(always)]
    pub(crate) fn split_tail_to(self, from: usize, dst: Self) {
        let len = self.len();
        debug_assert!(from <= len, "split index out of range");
        debug_assert!(dst.len() == 0, "split_tail_to needs an empty destination");
        let count = len - from;
        unsafe {
            ptr::copy_nonoverlapping(self.key_ptr(from), dst.key_ptr(0), count);
            ptr::copy_nonoverlapping(self.child_slot(from + 1), dst.child_slot(1), count);
        }
        self.set_len(from);
        dst.set_len(count);
    }

    /// Drop every separator, leaving the branch empty. The children are
    /// untouched: the caller decides their fate.
    pub(crate) fn drop_keys(self) {
        let len = self.len();
        unsafe { ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.key_ptr(0), len)) }
        self.set_len(0);
    }
}
