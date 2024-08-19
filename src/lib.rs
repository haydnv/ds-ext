//! This crate repackages standard data structures with additional capabilities,
//! like fast ordered maps and sets.
//!
//! The ordered collection types use a [`Vec`] internally for ordering.
//!
//! The map and set types support a `Key` trait to allow using arbitrary type `T: Key<K>`
//! to look up an entry with key type `K`.
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
