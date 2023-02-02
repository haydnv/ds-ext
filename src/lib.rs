//! This crate repackages data structures from the Rust standard library
//! with additional capabilities like ordered maps and sets, segmented URL-safe paths,
//! and a `Collection` types with no trait boundaries.
//!
//! The map and set types support a [`Key`] trait to allow using arbitrary type `T: Key<K>`
//! to look up an entry with key type `K`.

pub mod btree;
pub mod hash;
pub mod path;

pub use btree::{BTreeMap, BTreeSet};
pub use hash::{HashMap, HashSet};
pub use path::{Host, Id, Link, Path, PathBuf, PathSegment};
