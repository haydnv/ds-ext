//! A [`BTreeMap`] which supports indexing by key *or* by cardinality

use std::collections::btree_map::BTreeMap as Inner;
use std::sync::Arc;

/// An ordered map which supports indexing by key *or* by cardinality
pub struct BTreeMap<K, V> {
    inner: Inner<Arc<K>, V>,
}
