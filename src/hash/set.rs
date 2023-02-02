//! An ordered [`HashSet`] which supports indexing by cardinality.
//!
//! By default this is ordered by insertion, but it allows reordering by swapping.
//!
//! If you need an map ordered by keys which supports cardinality indexing, use
//! [`BTreeMap`](`crate::btree_map::BTreeMap`) in this crate.
//!
//! If you do not need reordering or cardinality indexing, use
//! [`im::hashset::HashSet`](https://docs.rs/im/latest/im/struct.HashSet.html).

use std::collections::hash_set::HashSet as Inner;
use std::sync::Arc;

/// An ordered set which supports indexing by cardinality
pub struct HashSet<K, V> {
    inner: Inner<Arc<K>, V>,
}
