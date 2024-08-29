//! This crate repackages standard data structures with additional capabilities,
//! like fast ordered maps and sets.
//!
//! [`OrdHashSet`] uses a [`Vec`] internally for ordering.
//! [`OrdHashSet`] and [`OrdHashMap`] both implement a `bisect` method
//! which allows looking up a key by comparison,
//! potentially avoiding the need for a heap allocation to construct a search key..
//!
//! Features:
//!  - `all`: enables all features
//!  - `serialize`: enables support for [`serde`](https://docs.rs/serde/).
//!  - `stream`: enables support for [`destream`](https://docs.rs/destream/).
//!  - `hash`: enables support for [`async-hash`](https://docs.rs/async-hash/).
//!
//!
//! Example usage:
//! ```
//! use ds_ext::*;
//!
//! let mut set = OrdHashSet::new();
//! assert!(set.is_empty());
//!
//! set.insert(1);
//! assert!(set.contains(&1));
//! assert_eq!(set.len(), 1);
//!
//! let mut map = OrdHashMap::from_iter(set.into_iter().map(|i| (i, i)));
//! assert_eq!(map.len(), 1);
//!
//! assert_eq!(map.get(&1), map.bisect(|i| i.partial_cmp(&1)));
//! ```

#[cfg(feature = "hash")]
mod hash;
#[cfg(feature = "serialize")]
mod serial;
#[cfg(feature = "stream")]
mod stream;

pub mod map;
pub mod queue;
pub mod set;

pub use map::OrdHashMap;
pub use queue::LinkedHashMap;
pub use set::OrdHashSet;
