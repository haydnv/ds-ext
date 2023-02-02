//! A [`Collection`] with no trait boundaries, i.e. a [`BTreeMap`] which generates its own keys.

use super::map::BTreeMap;

/// A generic collection with no trait boundaries, i.e. a [`BTreeMap`] which generates its own keys.
pub struct Collection<T> {
    inner: BTreeMap<usize, T>,
}
