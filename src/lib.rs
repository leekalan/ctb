//! Introduces a type that unifies borrowed and owned values into a smart
//! pointer that is internally borrowed to retain ownership.
//!
//! ## Overview
//!
//! This library provides the [`Ctb`] type, which is a smart pointer that
//! can hold either a borrowed or owned value. This allows you to create an
//! interface for the modules your libary that can work with both borrowed and
//! owned values by delegating the complexity of ownership to simple low level
//! concretions.
//! 
//! ## Acronym
//! 
//! - **Ctb** - `C`ow `T`o `B`orrowed. This is due to the similar functionality
//! to `Cow`, yet is not the same as `Cow` and has different use cases and functions
//! that expand on the limitations of `Cow` in a more useful manner.
//!
//! ## Structure
//!
//! The [`Ctb`] type is generic over the owned value and borrowed value, and
//! can be used with any two types that follow a "borrowed and owned" heirachy.
//!
//! ## Traits
//!
//! The `Ctb` type also implements the [`Deref`][std::ops::Deref],
//! [`DerefMut`][std::ops::DerefMut], [`Borrow`][std::borrow::Borrow],
//! [`BorrowMut`][std::borrow::BorrowMut], [`AsRef`][std::convert::AsRef],
//! and [`AsMut`][std::convert::AsMut] traits, which allows maximum
//! flexibility in treating the type as if it were an owned value.
//!
//! This library also provides three traits, [`IntoCtb`],
//! [`IntoDerefCtb`], and [`AsCtb`], which add
//! convenient methods all types that fit the requirements of the [`Ctb`] type.
//! These types are automatically implemented so there is no need implement them
//! yourself.
//!
//! ## Methods
//!
//! The [`Ctb`] type also provides a number of convenient methods for working
//! with the value it is holding, such as [`as_owned`][Ctb::as_owned],
//! [`as_borrowed`][Ctb::as_borrowed], [`is_owned`][Ctb::is_owned], and
//! [`is_borrowed`][Ctb::is_borrowed].
//!
//! ## Examples
//!
//! ### Unifying 'by value' and 'by reference' trait implementations
//!
//! ```rust
//! use ctb::{Ctb, AsCtb, IntoCtb};
//! 
//! pub trait AddTogether<T> {
//!     fn add_together(self, other: T) -> i32;
//! }
//! 
//! impl AddTogether<u8> for u8 {
//!     fn add_together(self, other: u8) -> i32 {
//!         (self + other) as i32
//!     }
//! }
//! 
//! impl AddTogether<&i32> for i32 {
//!     fn add_together(self, other: &i32) -> i32 {
//!         self + other
//!     }
//! }
//! 
//! // The complication is seen in the following function, it is possible to bypass
//! // by cloning or implementing 2 different functions but this may not be possible
//! // in more complex situations that involve multiple levels of indirection.
//! 
//! // pub fn add_together_and_double<T: AddTogether<T / &T ???>>(lhs: T, rhs: ???)
//! 
//! // However, by using `Ctb`, this is possible with only a small runtime overhead
//! // that the compiler should optimize away if possible.
//! 
//! impl AddTogether<Ctb<'_, u8, u8>> for Ctb<'_, u8, u8> {
//!     fn add_together(self, other: Ctb<u8, u8>) -> i32 {
//!         self.into_owned().add_together(other.into_owned())
//!     }
//! }
//! 
//! impl AddTogether<Ctb<'_, i32, i32>> for Ctb<'_, i32, i32> {
//!     fn add_together(self, other: Ctb<i32, i32>) -> i32 {
//!         self.into_owned().add_together(other.as_ref())
//!     }
//! }
//! 
//! // Despite the complexity of the bounds for this function, in much more complex
//! // use cases it can dramatically decreases complexity and redundancy. The main
//! // point though, is that the function is extremely simple to call and can easily
//! // be composed in further functions using `Ctb` and is completely generic over
//! // value or reference arguments.
//! pub fn add_together_and_double<T: Clone>(lhs: Ctb<T, T>, rhs: Ctb<T, T>) -> i32
//! where
//!     for<'a, 'b> Ctb<'a, T, T>: AddTogether<Ctb<'b, T, T>>,
//! {
//!     lhs.as_borrowed().add_together(rhs.as_borrowed()) + lhs.as_borrowed().add_together(rhs)
//! }
//! 
//! // Note: ctb() converts to an owned value but if we only had a reference we could
//! // use as_ctb() insead. If our type implemented Deref then we also could use
//! // ctb_deref() instead of cbt().
//! fn test() {
//!     assert_eq!(add_together_and_double(1u8.ctb(), 2u8.ctb()), 6);
//!     assert_eq!(add_together_and_double(1i32.ctb(), 2i32.ctb()), 6);
//! }
//!
//! ```

pub mod ctb;
pub mod into_ctb;

pub use ctb::Ctb;
pub use into_ctb::AsCtb;
pub use into_ctb::IntoCtb;
pub use into_ctb::IntoDerefCtb;

#[cfg(test)]
mod tests {
    use std::{borrow::Borrow, ops::*};

    use self::{
        ctb::Ctb,
        into_ctb::{AsCtb, IntoCtb, IntoDerefCtb},
    };

    use super::*;

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub struct A {
        pub a: i32,
    }

    impl Add<&A> for A {
        type Output = i32;
        fn add(self, rhs: &Self) -> Self::Output {
            self.a + rhs.a
        }
    }

    impl Add for Ctb<'_, A, A> {
        type Output = i32;

        fn add(self, rhs: Self) -> Self::Output {
            self.into_owned() + rhs.borrow()
        }
    }

    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
    pub struct B {
        pub b: i32,
    }

    impl Add<B> for &B {
        type Output = i32;
        fn add(self, rhs: B) -> Self::Output {
            self.b + rhs.b
        }
    }

    impl Add for Ctb<'_, B, B> {
        type Output = i32;

        fn add(self, rhs: Self) -> Self::Output {
            self.borrow() + rhs.into_owned()
        }
    }

    // Unifies the `add_then_double` function regardless of whether T is by reference or value when adding
    pub fn add_then_double<T: Add<T, Output = i32>>(lhs: T, rhs: T) -> i32 {
        (lhs + rhs) * 2
    }

    #[test]
    pub fn test() {
        let a1 = A { a: 1 }.ctb();
        let a2 = A { a: 2 }.as_ctb();

        let _a_works = add_then_double(a1, a2);

        let b1 = B { b: 1 }.ctb();
        let b2 = B { b: 2 }.as_ctb();

        let _b_works = add_then_double(b1, b2);
    }

    #[test]
    pub fn test_constructors() {
        // Constructed without enforcing that `String` implements deref which leads to a `&String` deref
        let ctb = Ctb::from_owned("balls".to_string());
        let _borrow = ctb.deref();
        let _owned = ctb.into_owned();

        // Constructed while enforcing that `String` implements deref which leads to a `&str` deref
        let ctb = Ctb::from_deref_owned("balls".to_string());
        let _borrow = ctb.deref();
        let _owned = ctb.into_owned();

        // Constructed using `str::ToOwned` which leads to a `String` into_owned
        let ctb = Ctb::from_ref("balls");
        let _borrow = ctb.deref();
        let _owned = ctb.into_owned();
    }

    #[test]
    pub fn test_converters() {
        // Constructed without enforcing that `String` implements deref which leads to a `&String` deref
        let ctb = "balls".to_string().ctb();
        let _borrow = ctb.deref();
        let _owned = ctb.into_owned();

        // Constructed while enforcing that `String` implements deref which leads to a `&str` deref
        let ctb = "balls".to_string().ctb_deref();
        let _borrow = ctb.deref();
        let _owned = ctb.into_owned();

        // Constructed using `str::ToOwned` which leads to a `String` into_owned
        let ctb = "balls".as_ctb();
        let _borrow = ctb.deref();
        let _owned = ctb.into_owned();
    }
}

mod doc_tests {
    #[allow(unused)]
    use crate::{AsCtb, IntoCtb};

    use super::Ctb;

    pub trait AddTogether<T> {
        fn add_together(self, other: T) -> i32;
    }

    impl AddTogether<u8> for u8 {
        fn add_together(self, other: u8) -> i32 {
            (self + other) as i32
        }
    }

    impl AddTogether<&i32> for i32 {
        fn add_together(self, other: &i32) -> i32 {
            self + other
        }
    }

    // The complication is seen in the following function, it is possible to bypass
    // by cloning or implementing 2 different functions but this may not be possible
    // in more complex situations that involve multiple levels of indirection.

    // pub fn add_together_and_double<T: AddTogether<T / &T ???>>(lhs: T, rhs: ???)

    // However, by using `Ctb`, this is possible with only a small runtime overhead
    // that the compiler should optimize away if possible.

    impl AddTogether<Ctb<'_, u8, u8>> for Ctb<'_, u8, u8> {
        fn add_together(self, other: Ctb<u8, u8>) -> i32 {
            self.into_owned().add_together(other.into_owned())
        }
    }

    impl AddTogether<Ctb<'_, i32, i32>> for Ctb<'_, i32, i32> {
        fn add_together(self, other: Ctb<i32, i32>) -> i32 {
            self.into_owned().add_together(other.as_ref())
        }
    }

    // Despite the complexity of the bounds for this function, in much more complex
    // use cases it can dramatically decreases complexity and redundancy. The main
    // point though, is that the function is extremely simple to call and can easily
    // be composed in further functions using `Ctb` and is completely generic over
    // value or reference arguments.
    #[allow(unused)]
    pub fn add_together_and_double<T: Clone>(lhs: Ctb<T, T>, rhs: Ctb<T, T>) -> i32
    where
        for<'a, 'b> Ctb<'a, T, T>: AddTogether<Ctb<'b, T, T>>,
    {
        lhs.as_borrowed().add_together(rhs.as_borrowed()) + lhs.as_borrowed().add_together(rhs)
    }

    // Note: ctb() converts to an owned value but if we only had a reference we could
    // use as_ctb() insead. If our type implemented Deref then we also could use
    // ctb_deref() instead of cbt().
    #[test]
    fn test() {
        assert_eq!(add_together_and_double(1u8.ctb(), 2u8.ctb()), 6);
        assert_eq!(add_together_and_double(1i32.ctb(), 2i32.ctb()), 6);
    }
}
