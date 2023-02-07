//! This crate repackages data structures from the Rust standard library
//! with additional capabilities like fast ordered maps and sets, segmented URL-safe paths,
//! and `Collection` types with no trait boundaries.
//!
//! The ordered collection types use a [`List`] internally for ordering.
//!
//! The map and set types support a `Key` trait to allow using arbitrary type `T: Key<K>`
//! to look up an entry with key type `K`.

pub mod ord;
pub mod path;

pub use ord::{LinkedHashMap, List, OrdHashMap, OrdHashSet};
pub use path::{Host, Id, Link, Path, PathBuf, PathSegment};
