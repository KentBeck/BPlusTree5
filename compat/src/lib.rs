//! `std::collections::BTreeMap` and `BTreeSet` look-alikes backed by
//! [`bplustree::BPlusTreeMap`].
//!
//! The point of this crate is to let a real project swap its `use
//! std::collections::BTreeMap;` for `use bplustree_compat::BTreeMap;` and
//! keep compiling. Method names, signatures, trait impls, and iteration
//! order follow std. Where the underlying tree lacks a primitive (the entry
//! API, `retain`, `append`, `split_off`, owned iteration) the operation is
//! composed from lookups, inserts, and removals; each such method notes its
//! cost.
//!
//! Every map needs `K: Ord + Clone`: the tree copies keys up into branch
//! separators.

#![forbid(unsafe_code)]

mod map;
mod set;

pub use map::{
    BTreeMap, Entry, IntoIter, IntoKeys, IntoValues, Iter, IterMut, Keys, OccupiedEntry, Range,
    RangeMut, VacantEntry, Values, ValuesMut,
};
pub use set::{BTreeSet, SetIntoIter, SetIter, SetRange};
