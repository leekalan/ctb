use std::{borrow::Borrow, ops::Deref};

use crate::clone_on_extract::CloneOnExtract;

/// Converts to an owned [`CloneOnExtract`]
pub trait IntoCloneOnExtract: Clone {
    fn coe(self) -> CloneOnExtract<'static, Self, Self> {
        CloneOnExtract::Owned(self)
    }
}

impl<T: Clone> IntoCloneOnExtract for T {}

/// Converts to an owned [`CloneOnExtract`] for types that implement [`Deref`]
pub trait IntoDerefCloneOnExtract: Sized + Deref + Borrow<Self::Target>
where
    Self::Target: ToOwned<Owned = Self>,
{
    fn coe_deref(self) -> CloneOnExtract<'static, Self, Self::Target> {
        CloneOnExtract::Owned(self)
    }
}

impl<T: Deref + Borrow<Self::Target>> IntoDerefCloneOnExtract for T where T::Target: ToOwned<Owned = T> {}

/// Converts to a borrowed [`CloneOnExtract`]
pub trait AsCloneOnExtract: ToOwned {
    fn as_coe(&self) -> CloneOnExtract<Self::Owned, Self> {
        CloneOnExtract::Borrowed(self)
    }
}

impl<T: ?Sized + ToOwned> AsCloneOnExtract for T {}
