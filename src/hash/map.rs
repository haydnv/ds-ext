//! An ordered [`HashMap`] which supports indexing by cardinality.
//!
//! By default this is ordered by insertion, but it allows reordering by swapping.
//!
//! If you need an map ordered by keys which supports cardinality indexing, use
//! [`BTreeMap`](`crate::btree_map::BTreeMap`) in this crate.
//!
//! If you do not need reordering or cardinality indexing, use
//! [`im::hashmap::HashMap`](https://docs.rs/im/latest/im/struct.HashMap.html).

use std::collections::hash_map::HashMap as Inner;
use std::sync::Arc;

/// An ordered map which supports indexing by cardinality
pub struct HashMap<K, V> {
    inner: Inner<Arc<K>, V>,
}
