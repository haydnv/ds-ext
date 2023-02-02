pub mod collection;
pub mod map;
pub mod set;

pub use collection::Collection;
pub use map::BTreeMap;
pub use set::BTreeSet;

/// A type which can be used to look up a key of type `K` in a [`BTreeMap`] or [`BTreeSet`]
pub trait Key<K> {}
