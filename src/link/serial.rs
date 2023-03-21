use serde::{Deserialize, Deserializer, Serialize, Serializer};

use super::{Host, Link, PathBuf};

impl<'de> Deserialize<'de> for Host {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let inner: &str = Deserialize::deserialize(deserializer)?;
        inner.parse().map_err(serde::de::Error::custom)
    }
}

impl Serialize for Host {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.to_string().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Link {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let inner: &str = Deserialize::deserialize(deserializer)?;
        inner.parse().map_err(serde::de::Error::custom)
    }
}

impl Serialize for Link {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.to_string().serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for PathBuf {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let inner: &str = Deserialize::deserialize(deserializer)?;
        inner.parse().map_err(serde::de::Error::custom)
    }
}

impl Serialize for PathBuf {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.to_string().serialize(serializer)
    }
}
