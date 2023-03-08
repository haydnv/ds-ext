//! This crate repackages data structures from the Rust standard library
//! with additional capabilities like fast ordered maps and sets, segmented URL-safe paths,
//! and `Collection` types with no trait boundaries.
//!
//! The ordered collection types use a [`List`] internally for ordering.
//!
//! The map and set types support a `Key` trait to allow using arbitrary type `T: Key<K>`
//! to look up an entry with key type `K`.
//!
//! Use the "stream" feature to enable support for [`destream`](https://docs.rs/destream/latest/destream/).

extern crate core;

pub mod link;
pub mod ord;

pub use link::{Id, Link, Path, PathBuf, PathSegment};
pub use ord::{LinkedHashMap, List, OrdHashMap, OrdHashSet};
