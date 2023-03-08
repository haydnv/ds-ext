//! A URI which supports IPv4, IPv6, domain names, and segmented [`Path`](`crate::link::Path`)s.

mod id;
mod path;
#[cfg(feature = "stream")]
mod stream;

pub use id::*;
pub use path::*;

use derive_more::*;

/// The host component of a [`Link`]
pub enum Host {
    // TODO: IPv4
    // TODO: IPv6
    // TODO: international domain names with IDNA: https://docs.rs/idna/0.3.0/idna/
}

/// An HTTP Link with an optional [`Host`] and [`PathBuf`]
pub struct Link {
    host: Option<Host>,
    path: PathBuf,
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
