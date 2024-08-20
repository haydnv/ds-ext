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
