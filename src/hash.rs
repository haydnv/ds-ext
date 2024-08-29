use async_hash::{default_hash, Digest, Hash, Output};

use super::{LinkedHashMap, OrdHashMap, OrdHashSet};

impl<D, K, V> Hash<D> for LinkedHashMap<K, V>
where
    D: Digest,
    K: Eq + std::hash::Hash,
    (K, V): Hash<D>,
    Self: IntoIterator<Item = (K, V)>,
{
    fn hash(self) -> Output<D> {
        if self.is_empty() {
            return default_hash::<D>();
        }

        let mut hasher = D::new();
        for item in self {
            hasher.update(item.hash());
        }
        hasher.finalize()
    }
}

impl<'a, D, K, V> Hash<D> for &'a LinkedHashMap<K, V>
where
    D: Digest,
    K: Eq + std::hash::Hash,
    (&'a K, &'a V): Hash<D>,
    Self: IntoIterator<Item = (&'a K, &'a V)>,
{
    fn hash(self) -> Output<D> {
        if self.is_empty() {
            return default_hash::<D>();
        }

        let mut hasher = D::new();
        for item in self {
            hasher.update(item.hash());
        }
        hasher.finalize()
    }
}

impl<D, K, V> Hash<D> for OrdHashMap<K, V>
where
    D: Digest,
    K: Eq + std::hash::Hash + Ord,
    (K, V): Hash<D>,
    Self: IntoIterator<Item = (K, V)>,
{
    fn hash(self) -> Output<D> {
        if self.is_empty() {
            return default_hash::<D>();
        }

        let mut hasher = D::new();
        for item in self {
            hasher.update(item.hash());
        }
        hasher.finalize()
    }
}

impl<'a, D, K, V> Hash<D> for &'a OrdHashMap<K, V>
where
    D: Digest,
    K: Eq + std::hash::Hash + Ord,
    (&'a K, &'a V): Hash<D>,
    Self: IntoIterator<Item = (&'a K, &'a V)>,
{
    fn hash(self) -> Output<D> {
        if self.is_empty() {
            return default_hash::<D>();
        }

        let mut hasher = D::new();
        for item in self {
            hasher.update(item.hash());
        }
        hasher.finalize()
    }
}

impl<D: Digest, T> Hash<D> for OrdHashSet<T>
where
    for<'a> &'a T: Hash<D>,
{
    fn hash(self) -> Output<D> {
        if self.is_empty() {
            return default_hash::<D>();
        }

        let mut hasher = D::new();
        for item in self.iter() {
            hasher.update(item.hash());
        }
        hasher.finalize()
    }
}

impl<'a, D: Digest, T> Hash<D> for &'a OrdHashSet<T>
where
    &'a T: Hash<D>,
{
    fn hash(self) -> Output<D> {
        if self.is_empty() {
            return default_hash::<D>();
        }

        let mut hasher = D::new();
        for item in self {
            hasher.update(item.hash());
        }
        hasher.finalize()
    }
}
