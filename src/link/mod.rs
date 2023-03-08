//! A URI which supports IPv4, IPv6, domain names, and segmented [`Path`](`crate::link::Path`)s.

mod id;
mod path;
#[cfg(feature = "serialize")]
mod serial;
#[cfg(feature = "stream")]
mod stream;

pub use id::*;
pub use path::*;
use std::fmt;

use derive_more::*;

/// The host component of a [`Link`]
#[derive(Eq, PartialEq)]
pub enum Host {
    // TODO: IPv4
    // TODO: IPv6
    // TODO: international domain names with IDNA: https://docs.rs/idna/0.3.0/idna/
}

impl fmt::Debug for Host {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        todo!()
    }
}

impl fmt::Display for Host {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        todo!()
    }
}

/// An HTTP Link with an optional [`Host`] and [`PathBuf`]
#[derive(Default, Eq, PartialEq)]
pub struct Link {
    host: Option<Host>,
    path: PathBuf,
}

impl fmt::Debug for Link {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(host) = &self.host {
            write!(f, "{:?}{:?}", host, self.path)
        } else {
            fmt::Debug::fmt(&self.path, f)
        }
    }
}

impl fmt::Display for Link {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(host) = &self.host {
            write!(f, "{}{}", host, self.path)
        } else {
            fmt::Display::fmt(&self.path, f)
        }
    }
}

#[cfg(feature = "hash")]
impl<D: async_hash::Digest> async_hash::Hash<D> for Link {
    fn hash(self) -> async_hash::Output<D> {
        async_hash::Hash::<D>::hash(&self)
    }
}

#[cfg(feature = "hash")]
impl<'a, D: async_hash::Digest> async_hash::Hash<D> for &'a Link {
    fn hash(self) -> async_hash::Output<D> {
        if self == &Link::default() {
            async_hash::default_hash::<D>()
        } else {
            async_hash::Hash::<D>::hash(self.to_string())
        }
    }
}

#[derive(Debug, Display, Error)]
#[display(fmt = "{}", msg)]
pub struct ParseError {
    msg: String,
}

impl From<String> for ParseError {
    fn from(msg: String) -> Self {
        Self { msg }
    }
}

impl From<&str> for ParseError {
    fn from(msg: &str) -> Self {
        Self {
            msg: msg.to_string(),
        }
    }
}
