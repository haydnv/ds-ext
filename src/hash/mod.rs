pub mod collection;
pub mod map;
pub mod set;

pub use collection::Collection;
pub use map::HashMap;
pub use set::HashSet;

/// A type which can be used to look up a key of type `K` in a [`HashMap`] or [`HashSet`]
pub trait Key<K> {}
