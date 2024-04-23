use std::{borrow::Borrow, ops::Deref};

use crate::ctb::Ctb;

/// Converts to an owned [`Ctb`]
pub trait IntoCtb: Clone {
    fn ctb(self) -> Ctb<'static, Self, Self> {
        Ctb::Owned(self)
    }
}

impl<T: Clone> IntoCtb for T {}

/// Converts to an owned [`Ctb`] for types that implement [`Deref`]
pub trait IntoDerefCtb: Sized + Deref + Borrow<Self::Target>
where
    Self::Target: ToOwned<Owned = Self>,
{
    fn ctb_deref(self) -> Ctb<'static, Self, Self::Target> {
        Ctb::Owned(self)
    }
}

impl<T: Deref + Borrow<Self::Target>> IntoDerefCtb for T where T::Target: ToOwned<Owned = T> {}

/// Converts to a borrowed [`Ctb`]
pub trait AsCtb: ToOwned {
    fn as_ctb(&self) -> Ctb<Self::Owned, Self> {
        Ctb::Borrowed(self)
    }
}

impl<T: ?Sized + ToOwned> AsCtb for T {}
