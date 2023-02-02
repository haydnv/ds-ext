//! A human-readable ID which is safe to use as a component in a [`Path`](`crate::path::Path`) and supports constants.

/// A human-readable ID
pub struct Id {
    inner: String,
}
