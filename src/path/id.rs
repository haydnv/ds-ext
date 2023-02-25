//! A human-readable ID which is safe to use as a component in a [`Path`](`crate::path::Path`)
//! and supports constants.

use std::borrow::Borrow;

/// A human-readable ID
pub struct Id {
    inner: String,
}

impl Borrow<str> for Id {
    fn borrow(&self) -> &str {
        &self.inner
    }
}

impl Borrow<String> for Id {
    fn borrow(&self) -> &String {
        &self.inner
    }
}
