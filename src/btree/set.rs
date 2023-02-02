//! A [`BTreeSet`] which supports indexing by key *or* by cardinality

use std::collections::btree_set::BTreeSet as Inner;
use std::sync::Arc;

/// An ordered set which supports indexing by key *or* by cardinality
pub struct BTreeSet<K> {
    inner: Inner<Arc<K>>,
}
