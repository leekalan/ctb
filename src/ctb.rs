use std::{
    borrow::{Borrow, BorrowMut},
    fmt::Display,
    ops::{Deref, DerefMut},
};

/// A smart pointer that unifies borrowed and owned values into a type that
/// is internally borrowed to retain ownership.
/// 
/// # Structure
///
/// The type takes two generics, one for the owned value and one for the
/// borrowed value.
/// - The lifetime, `'a` is the lifetime attached `U`
/// - The owned value, `T` must implement [`Sized`] and [`Borrow<U>`]
/// - The borrowed value, `U` must implement [`ToOwned<Owned = T>`][`ToOwned`]
/// 
/// # Methods
/// 
/// ## as_owned
/// 
/// [`Ctb::as_owned()`] - Converts the [`Ctb`] into a new [`Ctb`] that contains
/// an owned value
/// 
/// ### Cases
/// - Owned: the owned value will be moved into the new [`Ctb`]
/// - Borrowed: the borrowed value will be converted to an owned
/// value by calling [`ToOwned::to_owned()`], and moved into the new
/// [`Ctb`]
/// 
/// ## as_borrowed
/// 
/// [`Ctb::as_borrowed()`] Creates a new [`Ctb`] that contains a reference to the
/// owned or borrowed value
/// 
/// ## into_owned
/// 
/// [`Ctb::into_owned()`] Converts the [`Ctb`] into an owned value
/// 
/// ### Cases
/// - Owned: the owned value will be extracted
/// - Borrowed: the borrowed value will be converted to an owned
/// value by calling [`ToOwned::to_owned()`]
/// 
/// ## is_owned
/// 
/// [`Ctb::is_owned()`] Returns `true` if the [`Ctb`] contains an owned value
/// 
/// ## is_borrowed
/// 
/// [`Ctb::is_borrowed()`] Returns `true` if the [`Ctb`] contains a borrowed
/// value
/// 
/// ## from_owned
/// 
/// [`Ctb::from_owned()`] Creates a new [`Ctb`] that contains an owned value
/// 
/// ## from_deref_owned
/// 
/// [`Ctb::from_deref_owned()`] Creates a new [`Ctb`] that contains an owned
/// value for types that implement [`Deref`]
/// 
/// ## from_ref
/// 
/// [`Ctb::from_ref()`] Creates a new [`Ctb`] that contains a borrowed value
/// 

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ctb<'a, T: Borrow<U>, U: ?Sized + ToOwned<Owned = T>> {
    /// The owned value of type `T`
    Owned(T),
    /// The borrowed value of type `U` with the lifetime bound `'a`
    Borrowed(&'a U),
}

/// Some useful methods available for all instances of [`Ctb`]
impl<'a, T: Borrow<U>, U: ?Sized + ToOwned<Owned = T>> Ctb<'a, T, U> {
    /// Converts the `Ctb` into a new `Ctb` that contains an owned value
    /// 
    /// # Cases
    /// - Owned: the owned value will be moved into the new `Ctb`
    /// - Borrowed: the borrowed value will be converted to an owned
    /// value by calling [`ToOwned::to_owned()`] and moved into the new
    /// `Ctb`
    pub fn as_owned(self) -> Self {
        match self {
            Self::Owned(t) => Ctb::Owned(t),
            Self::Borrowed(t) => Ctb::Owned(t.to_owned()),
        }
    }

    /// Creates a new `Ctb` that contains a reference to the
    /// owned or borrowed value
    pub fn as_borrowed(&'a self) -> Self {
        match self {
            Self::Owned(t) => Ctb::Borrowed(t.borrow()),
            Self::Borrowed(t) => Ctb::Borrowed(t),
        }
    }

    /// Converts the `Ctb` into an owned value
    /// 
    /// # Cases
    /// - Owned: the owned value will be extracted
    /// - Borrowed: the borrowed value will be converted to an owned
    /// value by calling [`ToOwned::to_owned()`]
    pub fn into_owned(self) -> T {
        match self {
            Ctb::Owned(t) => t,
            Ctb::Borrowed(t) => t.to_owned(),
        }
    }

    /// Returns true if the underlying value is owned, else false
    pub fn is_owned(&self) -> bool {
        matches!(self, Ctb::Owned(_))
    }

    /// Returns true if the underlying value is borrowed, else false
    pub fn is_borrowed(&self) -> bool {
        matches!(self, Ctb::Borrowed(_))
    }
}

/// Constructor for owned objects with a deref target
impl<'a, T: Deref + Borrow<T::Target>> Ctb<'a, T, T::Target>
where
    T::Target: ToOwned<Owned = T>,
{
    pub fn from_deref_owned(owned: T) -> Self {
        Ctb::Owned(owned)
    }
}

/// Constructor for borrowed objects
impl<'a, U: ?Sized + ToOwned> Ctb<'a, U::Owned, U> {
    pub fn from_ref(borrowed: &'a U) -> Self {
        Ctb::Borrowed(borrowed)
    }
}

/// Constructor for owned objects
impl<'a, T: Clone> Ctb<'a, T, T> {
    pub fn from_owned(owned: T) -> Self {
        Ctb::Owned(owned)
    }
}

impl<T: Borrow<U>, U: ?Sized + ToOwned<Owned = T>> Deref for Ctb<'_, T, U> {
    type Target = U;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Owned(t) => t.borrow(),
            Self::Borrowed(t) => t,
        }
    }
}
impl<T: BorrowMut<U>, U: ?Sized + ToOwned<Owned = T>> DerefMut for Ctb<'_, T, U> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            Self::Owned(t) => t.borrow_mut(),
            Self::Borrowed(t) => {
                *self = Self::Owned(t.to_owned());
                self.deref_mut()
            }
        }
    }
}

impl<T: Borrow<U>, U: ?Sized + ToOwned<Owned = T>> Borrow<U> for Ctb<'_, T, U> {
    fn borrow(&self) -> &U {
        self
    }
}
impl<T: BorrowMut<U>, U: ?Sized + ToOwned<Owned = T>> BorrowMut<U> for Ctb<'_, T, U> {
    fn borrow_mut(&mut self) -> &mut U {
        self
    }
}

impl<T: Borrow<U>, U: ?Sized + ToOwned<Owned = T>> AsRef<U> for Ctb<'_, T, U> {
    fn as_ref(&self) -> &U {
        self
    }
}
impl<T: BorrowMut<U>, U: ?Sized + ToOwned<Owned = T>> AsMut<U> for Ctb<'_, T, U> {
    fn as_mut(&mut self) -> &mut U {
        self
    }
}

/// Creates a default `T` that is owned
impl<T: Borrow<U> + Default, U: ?Sized + ToOwned<Owned = T>> Default for Ctb<'_, T, U> {
    fn default() -> Self {
        Self::Owned(T::default())
    }
}

/// Calls [`Borrow::borrow()`] on the `Ctb` and displays the resulting `&'a U`
impl<T: Borrow<U>, U: ?Sized + ToOwned<Owned = T> + Display> Display for Ctb<'_, T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Owned(t) => t.borrow().fmt(f),
            Self::Borrowed(t) => t.fmt(f),
        }
    }
}
