//! A URI which supports IPv4, IPv6, domain names, and segmented [`Path`](`crate::link::Path`)s.

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use std::str::FromStr;
use std::{fmt, iter};

use derive_more::*;
use get_size::GetSize;
use get_size_derive::*;

mod id;
mod path;
#[cfg(feature = "serialize")]
mod serial;
#[cfg(feature = "stream")]
mod stream;

pub use id::*;
pub use path::*;

/// A port number
pub type Port = u16;

/// The protocol portion of a [`Link`] (e.g. "http")
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, GetSize)]
pub enum Protocol {
    HTTP,
}

impl PartialOrd for Protocol {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Protocol {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::HTTP, Self::HTTP) => Ordering::Equal,
        }
    }
}

impl Default for Protocol {
    fn default() -> Protocol {
        Protocol::HTTP
    }
}

impl fmt::Display for Protocol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Self::HTTP => "http",
        })
    }
}

/// The address of a remove host
#[derive(Clone, Debug, Display, Eq, PartialEq, Hash)]
pub enum Address {
    IPv4(Ipv4Addr),
    IPv6(Ipv6Addr),
    // TODO: international domain names with IDNA: https://docs.rs/idna/0.3.0/idna/
}

impl PartialOrd for Address {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Address {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::IPv4(this), Self::IPv4(that)) => this.cmp(that),
            (Self::IPv6(this), Self::IPv6(that)) => this.cmp(that),
            (Self::IPv4(_this), _) => Ordering::Less,
            (Self::IPv6(_this), _) => Ordering::Greater,
        }
    }
}

impl GetSize for Address {
    fn get_size(&self) -> usize {
        match self {
            Self::IPv4(_) => 4,
            Self::IPv6(_) => 16,
        }
    }
}

impl From<Ipv4Addr> for Address {
    fn from(addr: Ipv4Addr) -> Address {
        Self::IPv4(addr)
    }
}

impl From<Ipv6Addr> for Address {
    fn from(addr: Ipv6Addr) -> Address {
        Self::IPv6(addr)
    }
}

impl From<IpAddr> for Address {
    fn from(addr: IpAddr) -> Address {
        match addr {
            IpAddr::V4(addr) => Self::IPv4(addr),
            IpAddr::V6(addr) => Self::IPv6(addr),
        }
    }
}

impl PartialEq<Ipv4Addr> for Address {
    fn eq(&self, other: &Ipv4Addr) -> bool {
        match self {
            Self::IPv4(addr) => addr == other,
            _ => false,
        }
    }
}

impl PartialEq<Ipv6Addr> for Address {
    fn eq(&self, other: &Ipv6Addr) -> bool {
        match self {
            Self::IPv6(addr) => addr == other,
            _ => false,
        }
    }
}

impl PartialEq<IpAddr> for Address {
    fn eq(&self, other: &IpAddr) -> bool {
        use IpAddr::*;

        match other {
            V4(addr) => self == addr,
            V6(addr) => self == addr,
        }
    }
}

/// The host component of a [`Link`] (e.g. "http://127.0.0.1:8702")
#[derive(Clone, Debug, Hash, Eq, PartialEq, GetSize)]
pub struct Host {
    protocol: Protocol,
    address: Address,
    port: Option<Port>,
}

impl FromStr for Host {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Host, ParseError> {
        if !s.starts_with("http://") {
            return Err(format!("invalid protocol: {}", s).into());
        }

        let protocol = Protocol::HTTP;

        let s = &s[7..];

        let (address, port): (Address, Option<u16>) = if s.contains("::") {
            let mut segments: Vec<&str> = s.split("::").collect();
            let port: Option<u16> = if segments.last().unwrap().contains(':') {
                let last_segment: Vec<&str> = segments.pop().unwrap().split(':').collect();
                if last_segment.len() == 2 {
                    segments.push(last_segment[0]);

                    let port = last_segment[1].parse().map_err(|cause| {
                        format!("{} is not a valid port number: {}", last_segment[1], cause)
                    })?;

                    Some(port)
                } else {
                    return Err(format!("invalid IPv6 address: {}", s).into());
                }
            } else {
                None
            };

            let address = segments.join("::");
            let address: Ipv6Addr = address.parse().map_err(|cause| {
                ParseError::from(format!(
                    "{} is not a valid IPv6 address: {}",
                    address, cause
                ))
            })?;

            (address.into(), port)
        } else {
            let (address, port) = if s.contains(':') {
                let segments: Vec<&str> = s.split(':').collect();
                if segments.len() == 2 {
                    let port: u16 = segments[1].parse().map_err(|cause| {
                        ParseError::from(format!(
                            "{} is not a valid port number: {}",
                            segments[1], cause
                        ))
                    })?;

                    (segments[0], Some(port))
                } else {
                    return Err(format!("invalid network address: {}", s).into());
                }
            } else {
                (s, None)
            };

            let address: Ipv4Addr = address.parse().map_err(|cause| {
                ParseError::from(format!(
                    "{} is not a valid IPv4 address: {}",
                    address, cause
                ))
            })?;

            (address.into(), port)
        };

        Ok(Host {
            protocol,
            address,
            port,
        })
    }
}

impl PartialOrd for Host {
    fn partial_cmp(&self, other: &Host) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Host {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.protocol.cmp(&other.protocol) {
            Ordering::Equal => match self.address.cmp(&other.address) {
                Ordering::Equal => self.port.cmp(&other.port),
                ordering => ordering,
            },
            ordering => ordering,
        }
    }
}

impl From<(Protocol, Address)> for Host {
    fn from(components: (Protocol, Address)) -> Self {
        let (protocol, address) = components;
        Self {
            protocol,
            address,
            port: None,
        }
    }
}

impl From<(Protocol, Address, Port)> for Host {
    fn from(components: (Protocol, Address, Port)) -> Self {
        let (protocol, address, port) = components;
        Self {
            protocol,
            address,
            port: Some(port),
        }
    }
}

impl From<(Protocol, Address, Option<Port>)> for Host {
    fn from(components: (Protocol, Address, Option<Port>)) -> Self {
        let (protocol, address, port) = components;
        Self {
            protocol,
            address,
            port,
        }
    }
}

impl fmt::Display for Host {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(port) = self.port {
            write!(f, "{}://{}:{}", self.protocol, self.address, port)
        } else {
            write!(f, "{}://{}", self.protocol, self.address)
        }
    }
}

/// An HTTP Link with an optional [`Address`] and [`PathBuf`]
#[derive(Clone, Default, Eq, Hash, PartialEq, GetSize)]
pub struct Link {
    host: Option<Host>,
    path: PathBuf,
}

impl Link {
    /// Create a new [`Link`] with the given [`Host`] and [`PathBuf`].
    pub fn new(host: Host, path: PathBuf) -> Self {
        Self {
            host: Some(host),
            path,
        }
    }

    /// Consume this [`Link`] and return its [`Host`] and [`PathBuf`].
    pub fn into_inner(self) -> (Option<Host>, PathBuf) {
        (self.host, self.path)
    }

    /// Consume this [`Link`] and return its [`Host`].
    pub fn into_host(self) -> Option<Host> {
        self.host
    }

    /// Consume this [`Link`] and return its [`PathBuf`].
    pub fn into_path(self) -> PathBuf {
        self.path
    }

    /// Borrow this [`Link`]'s [`Host`], if it has one.
    pub fn host(&self) -> Option<&Host> {
        self.host.as_ref()
    }

    /// Borrow this [`Link`]'s path.
    pub fn path(&self) -> &PathBuf {
        &self.path
    }

    /// Borrow this [`Link`]'s path mutably.
    pub fn path_mut(&mut self) -> &mut PathBuf {
        &mut self.path
    }

    /// Append the given [`PathSegment`] to this [`Link`] and return it.
    pub fn append<S: Into<PathSegment>>(mut self, segment: S) -> Self {
        self.path = self.path.append(segment);
        self
    }
}

impl Extend<PathSegment> for Link {
    fn extend<I: IntoIterator<Item = PathSegment>>(&mut self, iter: I) {
        self.path.extend(iter)
    }
}

impl PartialEq<[PathSegment]> for Link {
    fn eq(&self, other: &[PathSegment]) -> bool {
        if self.host.is_some() {
            return false;
        }

        &self.path == other
    }
}

impl PartialEq<String> for Link {
    fn eq(&self, other: &String) -> bool {
        self == other.as_str()
    }
}

impl PartialEq<str> for Link {
    fn eq(&self, other: &str) -> bool {
        let other = other.borrow();

        if other.is_empty() {
            false
        } else if other.starts_with('/') {
            self.host.is_none() && &self.path == other
        } else if other.ends_with('/') {
            self.to_string() == other[..other.len() - 1]
        } else {
            self.to_string() == other
        }
    }
}

impl From<Host> for Link {
    fn from(host: Host) -> Link {
        Link {
            host: Some(host),
            path: PathBuf::default(),
        }
    }
}

impl From<PathLabel> for Link {
    fn from(path: PathLabel) -> Self {
        PathBuf::from(path).into()
    }
}

impl From<PathBuf> for Link {
    fn from(path: PathBuf) -> Link {
        Link { host: None, path }
    }
}

impl From<(Host, PathBuf)> for Link {
    fn from(tuple: (Host, PathBuf)) -> Link {
        let (host, path) = tuple;
        Link {
            host: Some(host),
            path,
        }
    }
}

impl From<(Option<Host>, PathBuf)> for Link {
    fn from(tuple: (Option<Host>, PathBuf)) -> Link {
        let (host, path) = tuple;
        Link { host, path }
    }
}

impl FromStr for Link {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Link, ParseError> {
        if s.starts_with('/') {
            return Ok(Link {
                host: None,
                path: s.parse()?,
            });
        } else if !s.starts_with("http://") {
            return Err(format!("cannot parse {} as a Link: invalid protocol", s).into());
        }

        let s = if s.ends_with('/') {
            &s[..s.len() - 1]
        } else {
            s
        };

        let segments: Vec<&str> = s.split('/').collect();
        if segments.is_empty() {
            return Err(format!("invalid Link: {}", s).into());
        }

        let host: Host = segments[..3].join("/").parse()?;

        let segments = &segments[3..];

        let segments = segments
            .iter()
            .map(|s| s.parse())
            .collect::<Result<Vec<PathSegment>, ParseError>>()?;

        Ok(Link {
            host: Some(host),
            path: iter::FromIterator::from_iter(segments),
        })
    }
}

impl PartialOrd for Link {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Link {
    fn cmp(&self, other: &Self) -> Ordering {
        match (&self.host, &other.host) {
            (None, None) => self.path.cmp(&other.path),
            (Some(this), Some(that)) => match this.cmp(&that) {
                Ordering::Equal => self.path.cmp(&other.path),
                ordering => ordering,
            },
            (Some(_), _) => Ordering::Less,
            (_, Some(_)) => Ordering::Greater,
        }
    }
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
