//! Data structures with ordering provided by a [`List`].
//!
//! [`List`] itself is ordered using a [`Tree`].

pub mod list;
pub mod map;
pub mod queue;
pub mod set;
mod tree;

pub use list::List;
pub use map::LinkedHashMap;
pub use set::LinkedHashSet;
pub use tree::Tree;
