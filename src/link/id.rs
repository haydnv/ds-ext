//! A human-readable ID which is safe to use as a component in a [`Path`](`crate::link::Path`)
//! and supports constants.
//!
//! Example:
//! ```
//! # use std::str::FromStr;
//! use ds_ext::link::{label, Id, Label};
//!
//! const HELLO: Label = label("hello"); // unchecked!
//! let world: Id = "world".parse().expect("id");
//!
//! assert_eq!(format!("{}, {}!", HELLO, world), "hello, world!");
//! assert_eq!(Id::from(HELLO), "hello");
//! assert!(Id::from_str("this string has whitespace").is_err());
//! ```

use std::borrow::Borrow;
use std::fmt;
use std::ops::Deref;
use std::str::FromStr;

use get_size::GetSize;
use get_size_derive::*;
use regex::Regex;
use safecast::TryCastFrom;

use super::ParseError;

pub const RESERVED_CHARS: [&str; 21] = [
    "/", "..", "~", "$", "`", "&", "|", "=", "^", "{", "}", "<", ">", "'", "\"", "?", ":", "@",
    "#", "(", ")",
];

/// A static label which implements `Into<Id>`.
pub struct Label {
    id: &'static str,
}

impl Deref for Label {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.id
    }
}

impl From<Label> for Id {
    fn from(l: Label) -> Id {
        Id {
            inner: l.id.to_string(),
        }
    }
}

impl PartialEq<Id> for Label {
    fn eq(&self, other: &Id) -> bool {
        self.id == other.as_str()
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(self.id)
    }
}

/// Return a [`Label`] with the given static `str`.
pub const fn label(id: &'static str) -> Label {
    Label { id }
}

/// A human-readable ID
#[derive(Clone, Eq, Hash, GetSize, PartialEq, Ord, PartialOrd)]
pub struct Id {
    inner: String,
}

impl Id {
    /// Borrows the String underlying this `Id`.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.inner.as_str()
    }

    /// Return true if this `Id` begins with the specified string.
    pub fn starts_with(&self, prefix: &str) -> bool {
        self.inner.starts_with(prefix)
    }
}

#[cfg(feature = "hash")]
impl<D: async_hash::Digest> async_hash::Hash<D> for Id {
    fn hash(self) -> async_hash::Output<D> {
        async_hash::Hash::<D>::hash(self.as_str())
    }
}

#[cfg(feature = "hash")]
impl<'a, D: async_hash::Digest> async_hash::Hash<D> for &'a Id {
    fn hash(self) -> async_hash::Output<D> {
        async_hash::Hash::<D>::hash(self.as_str())
    }
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

impl PartialEq<str> for Id {
    fn eq(&self, other: &str) -> bool {
        self.inner == other
    }
}

impl<'a> PartialEq<&'a str> for Id {
    fn eq(&self, other: &&'a str) -> bool {
        self.inner == *other
    }
}

impl PartialEq<Label> for Id {
    fn eq(&self, other: &Label) -> bool {
        self.inner == other.id
    }
}

impl PartialEq<Id> for &str {
    fn eq(&self, other: &Id) -> bool {
        self == &other.inner
    }
}

impl From<usize> for Id {
    fn from(u: usize) -> Id {
        u.to_string().parse().expect("usize")
    }
}

impl From<u64> for Id {
    fn from(i: u64) -> Id {
        i.to_string().parse().expect("64-bit unsigned int")
    }
}

impl FromStr for Id {
    type Err = ParseError;

    fn from_str(id: &str) -> Result<Self, Self::Err> {
        validate_id(id)?;

        Ok(Id {
            inner: id.to_string(),
        })
    }
}

impl TryCastFrom<String> for Id {
    fn can_cast_from(id: &String) -> bool {
        validate_id(id).is_ok()
    }

    fn opt_cast_from(id: String) -> Option<Id> {
        id.parse().ok()
    }
}

impl TryCastFrom<Id> for usize {
    fn can_cast_from(id: &Id) -> bool {
        id.as_str().parse::<usize>().is_ok()
    }

    fn opt_cast_from(id: Id) -> Option<usize> {
        id.as_str().parse::<usize>().ok()
    }
}

impl fmt::Debug for Id {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.inner)
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(&self.inner)
    }
}

fn validate_id(id: &str) -> Result<(), ParseError> {
    if id.is_empty() {
        return Err("cannot construct an empty Id".into());
    }

    let mut invalid_chars = id.chars().filter(|c| (*c as u8) < 32u8);
    if let Some(invalid) = invalid_chars.next() {
        return Err(format!(
            "Id {} contains ASCII control characters {}",
            id, invalid as u8,
        )
        .into());
    }

    for pattern in &RESERVED_CHARS {
        if id.contains(pattern) {
            return Err(format!("Id {} contains disallowed pattern {}", id, pattern).into());
        }
    }

    if let Some(w) = Regex::new(r"\s").expect("whitespace regex").find(id) {
        return Err(format!("Id {} is not allowed to contain whitespace {:?}", id, w).into());
    }

    Ok(())
}
