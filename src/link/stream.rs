use std::str::FromStr;

use async_trait::async_trait;
use destream::{de, en};

use super::{Id, PathBuf};

#[async_trait]
impl de::FromStream for Id {
    type Context = ();

    async fn from_stream<D: de::Decoder>(cxt: (), decoder: &mut D) -> Result<Self, D::Error> {
        let s = String::from_stream(cxt, decoder).await?;
        Id::from_str(&s).map_err(de::Error::custom)
    }
}

impl<'en> en::ToStream<'en> for Id {
    fn to_stream<E: en::Encoder<'en>>(&'en self, e: E) -> Result<E::Ok, E::Error> {
        e.encode_str(self.as_str())
    }
}

impl<'en> en::IntoStream<'en> for Id {
    fn into_stream<E: en::Encoder<'en>>(self, e: E) -> Result<E::Ok, E::Error> {
        e.encode_str(self.as_str())
    }
}

#[async_trait]
impl de::FromStream for PathBuf {
    type Context = ();

    async fn from_stream<D: de::Decoder>(
        context: (),
        decoder: &mut D,
    ) -> Result<PathBuf, D::Error> {
        let s = String::from_stream(context, decoder).await?;
        s.parse().map_err(de::Error::custom)
    }
}

impl<'en> en::IntoStream<'en> for PathBuf {
    fn into_stream<E: en::Encoder<'en>>(self, e: E) -> Result<E::Ok, E::Error> {
        e.encode_str(&self.to_string())
    }
}

impl<'en> en::ToStream<'en> for PathBuf {
    fn to_stream<E: en::Encoder<'en>>(&'en self, e: E) -> Result<E::Ok, E::Error> {
        e.encode_str(&self.to_string())
    }
}
