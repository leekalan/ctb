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
/// [`CloneOnExtract::into_owned()`] - Converts the [`CloneOnExtract`] into a new [`CloneOnExtract`] that contains
/// an owned value
/// 
/// ### Cases
/// - Owned: the owned value will be moved into the new [`CloneOnExtract`]
/// - Borrowed: the borrowed value will be converted to an owned
/// value by calling [`ToOwned::to_owned()`], and moved into the new
/// [`CloneOnExtract`]
/// 
/// ## as_borrowed
/// 
/// [`CloneOnExtract::as_borrowed()`] Creates a new [`CloneOnExtract`] that contains a reference to the
/// owned or borrowed value
/// 
/// ## into_owned
/// 
/// [`CloneOnExtract::extract()`] Converts the [`CloneOnExtract`] into an owned value
/// 
/// ### Cases
/// - Owned: the owned value will be extracted
/// - Borrowed: the borrowed value will be converted to an owned
/// value by calling [`ToOwned::to_owned()`]
/// 
/// ## is_owned
/// 
/// [`CloneOnExtract::is_owned()`] Returns `true` if the [`CloneOnExtract`] contains an owned value
/// 
/// ## is_borrowed
/// 
/// [`CloneOnExtract::is_borrowed()`] Returns `true` if the [`CloneOnExtract`] contains a borrowed
/// value
/// 
/// ## from_owned
/// 
/// [`CloneOnExtract::from_owned()`] Creates a new [`CloneOnExtract`] that contains an owned value
/// 
/// ## from_deref_owned
/// 
/// [`CloneOnExtract::from_deref_owned()`] Creates a new [`CloneOnExtract`] that contains an owned
/// value for types that implement [`Deref`]
/// 
/// ## from_ref
/// 
/// [`CloneOnExtract::from_ref()`] Creates a new [`CloneOnExtract`] that contains a borrowed value
/// 

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CloneOnExtract<'a, T: Borrow<U>, U: ?Sized + ToOwned<Owned = T>> {
    /// The owned value of type `T`
    Owned(T),
    /// The borrowed value of type `U` with the lifetime bound `'a`
    Borrowed(&'a U),
}

/// Some useful methods available for all instances of [`CloneOnExtract`]
impl<'a, T: Borrow<U>, U: ?Sized + ToOwned<Owned = T>> CloneOnExtract<'a, T, U> {
    /// Converts the `CloneOnExtract` into a new `CloneOnExtract` that contains an owned value
    /// 
    /// # Cases
    /// - Owned: the owned value will be moved into the new `CloneOnExtract`
    /// - Borrowed: the borrowed value will be converted to an owned
    /// value by calling [`ToOwned::to_owned()`] and moved into the new
    /// `CloneOnExtract`
    pub fn into_owned(self) -> Self {
        match self {
            Self::Owned(t) => CloneOnExtract::Owned(t),
            Self::Borrowed(t) => CloneOnExtract::Owned(t.to_owned()),
        }
    }

    /// Creates a new `CloneOnExtract` that contains a reference to the
    /// owned or borrowed value
    pub fn as_borrowed(&'a self) -> Self {
        match self {
            Self::Owned(t) => CloneOnExtract::Borrowed(t.borrow()),
            Self::Borrowed(t) => CloneOnExtract::Borrowed(t),
        }
    }

    /// Converts the `CloneOnExtract` into an owned value
    /// 
    /// # Cases
    /// - Owned: the owned value will be extracted
    /// - Borrowed: the borrowed value will be converted to an owned
    /// value by calling [`ToOwned::to_owned()`]
    pub fn extract(self) -> T {
        match self {
            CloneOnExtract::Owned(t) => t,
            CloneOnExtract::Borrowed(t) => t.to_owned(),
        }
    }

    /// Returns true if the underlying value is owned, else false
    pub fn is_owned(&self) -> bool {
        matches!(self, CloneOnExtract::Owned(_))
    }

    /// Returns true if the underlying value is borrowed, else false
    pub fn is_borrowed(&self) -> bool {
        matches!(self, CloneOnExtract::Borrowed(_))
    }
}

/// Constructor for owned objects with a deref target
impl<'a, T: Deref + Borrow<T::Target>> CloneOnExtract<'a, T, T::Target>
where
    T::Target: ToOwned<Owned = T>,
{
    pub fn from_deref_owned(owned: T) -> Self {
        CloneOnExtract::Owned(owned)
    }
}

/// Constructor for borrowed objects
impl<'a, U: ?Sized + ToOwned> CloneOnExtract<'a, U::Owned, U> {
    pub fn from_ref(borrowed: &'a U) -> Self {
        CloneOnExtract::Borrowed(borrowed)
    }
}

/// Constructor for owned objects
impl<'a, T: Clone> CloneOnExtract<'a, T, T> {
    pub fn from_owned(owned: T) -> Self {
        CloneOnExtract::Owned(owned)
    }
}

impl<T: Borrow<U>, U: ?Sized + ToOwned<Owned = T>> Deref for CloneOnExtract<'_, T, U> {
    type Target = U;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Owned(t) => t.borrow(),
            Self::Borrowed(t) => t,
        }
    }
}
impl<T: BorrowMut<U>, U: ?Sized + ToOwned<Owned = T>> DerefMut for CloneOnExtract<'_, T, U> {
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

impl<T: Borrow<U>, U: ?Sized + ToOwned<Owned = T>> Borrow<U> for CloneOnExtract<'_, T, U> {
    fn borrow(&self) -> &U {
        self
    }
}
impl<T: BorrowMut<U>, U: ?Sized + ToOwned<Owned = T>> BorrowMut<U> for CloneOnExtract<'_, T, U> {
    fn borrow_mut(&mut self) -> &mut U {
        self
    }
}

impl<T: Borrow<U>, U: ?Sized + ToOwned<Owned = T>> AsRef<U> for CloneOnExtract<'_, T, U> {
    fn as_ref(&self) -> &U {
        self
    }
}
impl<T: BorrowMut<U>, U: ?Sized + ToOwned<Owned = T>> AsMut<U> for CloneOnExtract<'_, T, U> {
    fn as_mut(&mut self) -> &mut U {
        self
    }
}

/// Creates a default `T` that is owned
impl<T: Borrow<U> + Default, U: ?Sized + ToOwned<Owned = T>> Default for CloneOnExtract<'_, T, U> {
    fn default() -> Self {
        Self::Owned(T::default())
    }
}

/// Calls [`Borrow::borrow()`] on the `CloneOnExtract` and displays the resulting `&'a U`
impl<T: Borrow<U>, U: ?Sized + ToOwned<Owned = T> + Display> Display for CloneOnExtract<'_, T, U> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Owned(t) => t.borrow().fmt(f),
            Self::Borrowed(t) => t.fmt(f),
        }
    }
}
