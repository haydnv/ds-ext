//! An ordered [`HashSet`] which supports indexing by cardinality.
//!
//! By default this is ordered by insertion, but it allows reordering by swapping.
//!
//! If you need a set ordered by keys which supports cardinality indexing, use
//! [`BTreeMap`](`crate::btree::set::BTreeSet`) from this crate.
//!
//! If you do not need reordering or cardinality indexing, use
//! [`im::hashset::HashSet`](https://docs.rs/im/latest/im/struct.HashSet.html).

use std::collections::hash_set::HashSet as Inner;
use std::sync::Arc;

use crate::ord::List;

/// An ordered set which supports indexing by cardinality
pub struct HashSet<K, V> {
    inner: Inner<Arc<K>, V>,
    order: List<Arc<K>>,
}
