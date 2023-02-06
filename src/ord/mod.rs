//! Data structures with ordering provided by a [`List`].
//!
//! [`List`] itself is ordered using a [`Tree`].

pub mod list;
pub mod map;
mod tree;

pub use list::List;
pub use map::LinkedHashMap;
pub use tree::Tree;
