//! Introduces a type that unifies borrowed and owned values into a smart
//! pointer that is internally borrowed to retain ownership.
//!
//! ## Overview
//!
//! This library provides the [`CloneOnExtract`] type, which is a smart pointer that
//! can hold either a borrowed or owned value. This allows you to create an
//! interface for the modules your libary that can work with both borrowed and
//! owned values by delegating the complexity of ownership to simple low level
//! concretions.
//! 
//! ## Acronym
//! 
//! - **CloneOnExtract** - `C`ow `T`o `B`orrowed. This is due to the similar functionality
//! to `Cow`, yet is not the same as `Cow` and has different use cases and functions
//! that expand on the limitations of `Cow` in a more useful manner.
//!
//! ## Structure
//!
//! The [`CloneOnExtract`] type is generic over the owned value and borrowed value, and
//! can be used with any two types that follow a "borrowed and owned" heirachy.
//!
//! ## Traits
//!
//! The `CloneOnExtract` type also implements the [`Deref`][std::ops::Deref],
//! [`DerefMut`][std::ops::DerefMut], [`Borrow`][std::borrow::Borrow],
//! [`BorrowMut`][std::borrow::BorrowMut], [`AsRef`][std::convert::AsRef],
//! and [`AsMut`][std::convert::AsMut] traits, which allows maximum
//! flexibility in treating the type as if it were an owned value.
//!
//! This library also provides three traits, [`IntoCloneOnExtract`],
//! [`IntoDerefCloneOnExtract`], and [`AsCloneOnExtract`], which add
//! convenient methods all types that fit the requirements of the [`CloneOnExtract`] type.
//! These types are automatically implemented so there is no need implement them
//! yourself.
//!
//! ## Methods
//!
//! The [`CloneOnExtract`] type also provides a number of convenient methods for working
//! with the value it is holding, such as [`as_owned`][CloneOnExtract::into_owned],
//! [`as_borrowed`][CloneOnExtract::as_borrowed], [`is_owned`][CloneOnExtract::extract], and
//! [`is_borrowed`][CloneOnExtract::is_borrowed].
//!
//! ## Examples
//!
//! ### Unifying 'by value' and 'by reference' trait implementations
//!
//! ```rust
//! use CloneOnExtract::{CloneOnExtract, AsCloneOnExtract, IntoCloneOnExtract};
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
//! // However, by using `CloneOnExtract`, this is possible with only a small runtime overhead
//! // that the compiler should optimize away if possible.
//! 
//! impl AddTogether<CloneOnExtract<'_, u8, u8>> for CloneOnExtract<'_, u8, u8> {
//!     fn add_together(self, other: CloneOnExtract<u8, u8>) -> i32 {
//!         self.into_owned().add_together(other.into_owned())
//!     }
//! }
//! 
//! impl AddTogether<CloneOnExtract<'_, i32, i32>> for CloneOnExtract<'_, i32, i32> {
//!     fn add_together(self, other: CloneOnExtract<i32, i32>) -> i32 {
//!         self.into_owned().add_together(other.as_ref())
//!     }
//! }
//! 
//! // Despite the complexity of the bounds for this function, in much more complex
//! // use cases it can dramatically decreases complexity and redundancy. The main
//! // point though, is that the function is extremely simple to call and can easily
//! // be composed in further functions using `CloneOnExtract` and is completely generic over
//! // value or reference arguments.
//! pub fn add_together_and_double<T: Clone>(lhs: CloneOnExtract<T, T>, rhs: CloneOnExtract<T, T>) -> i32
//! where
//!     for<'a, 'b> CloneOnExtract<'a, T, T>: AddTogether<CloneOnExtract<'b, T, T>>,
//! {
//!     lhs.as_borrowed().add_together(rhs.as_borrowed()) + lhs.as_borrowed().add_together(rhs)
//! }
//! 
//! // Note: CloneOnExtract() converts to an owned value but if we only had a reference we could
//! // use as_CloneOnExtract() insead. If our type implemented Deref then we also could use
//! // CloneOnExtract_deref() instead of cbt().
//! fn test() {
//!     assert_eq!(add_together_and_double(1u8.CloneOnExtract(), 2u8.CloneOnExtract()), 6);
//!     assert_eq!(add_together_and_double(1i32.CloneOnExtract(), 2i32.CloneOnExtract()), 6);
//! }
//!
//! ```

pub mod clone_on_extract;
pub mod into_clone_on_extract;

pub use clone_on_extract::CloneOnExtract;
pub use into_clone_on_extract::AsCloneOnExtract;
pub use into_clone_on_extract::IntoCloneOnExtract;
pub use into_clone_on_extract::IntoDerefCloneOnExtract;

#[cfg(test)]
mod tests {
    use std::{borrow::Borrow, ops::*};

    use self::{
        clone_on_extract::CloneOnExtract,
        into_clone_on_extract::{AsCloneOnExtract, IntoCloneOnExtract, IntoDerefCloneOnExtract},
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

    impl Add for CloneOnExtract<'_, A, A> {
        type Output = i32;

        fn add(self, rhs: Self) -> Self::Output {
            self.extract() + rhs.borrow()
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

    impl Add for CloneOnExtract<'_, B, B> {
        type Output = i32;

        fn add(self, rhs: Self) -> Self::Output {
            self.borrow() + rhs.extract()
        }
    }

    // Unifies the `add_then_double` function regardless of whether T is by reference or value when adding
    pub fn add_then_double<T: Add<T, Output = i32>>(lhs: T, rhs: T) -> i32 {
        (lhs + rhs) * 2
    }

    #[test]
    pub fn test() {
        let a1 = A { a: 1 }.coe();
        let a2 = A { a: 2 }.as_coe();

        let _a_works = add_then_double(a1, a2);

        let b1 = B { b: 1 }.coe();
        let b2 = B { b: 2 }.as_coe();

        let _b_works = add_then_double(b1, b2);
    }

    #[test]
    pub fn test_constructors() {
        // Constructed without enforcing that `String` implements deref which leads to a `&String` deref
        let coe = CloneOnExtract::from_owned("balls".to_string());
        let _borrow = coe.deref();
        let _owned = coe.into_owned();

        // Constructed while enforcing that `String` implements deref which leads to a `&str` deref
        let coe = CloneOnExtract::from_deref_owned("balls".to_string());
        let _borrow = coe.deref();
        let _owned = coe.into_owned();

        // Constructed using `str::ToOwned` which leads to a `String` into_owned
        let coe = CloneOnExtract::from_ref("balls");
        let _borrow = coe.deref();
        let _owned = coe.into_owned();
    }

    #[test]
    pub fn test_converters() {
        // Constructed without enforcing that `String` implements deref which leads to a `&String` deref
        let coe = "balls".to_string().coe();
        let _borrow = coe.deref();
        let _owned = coe.into_owned();

        // Constructed while enforcing that `String` implements deref which leads to a `&str` deref
        let coe = "balls".to_string().coe_deref();
        let _borrow = coe.deref();
        let _owned = coe.into_owned();

        // Constructed using `str::ToOwned` which leads to a `String` into_owned
        let coe = "balls".as_coe();
        let _borrow = coe.deref();
        let _owned = coe.into_owned();
    }
}

mod doc_tests {
    #[allow(unused)]
    use crate::{AsCloneOnExtract, IntoCloneOnExtract};

    use super::CloneOnExtract;

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

    // However, by using `CloneOnExtract`, this is possible with only a small runtime overhead
    // that the compiler should optimize away if possible.

    impl AddTogether<CloneOnExtract<'_, u8, u8>> for CloneOnExtract<'_, u8, u8> {
        fn add_together(self, other: CloneOnExtract<u8, u8>) -> i32 {
            self.extract().add_together(other.extract())
        }
    }

    impl AddTogether<CloneOnExtract<'_, i32, i32>> for CloneOnExtract<'_, i32, i32> {
        fn add_together(self, other: CloneOnExtract<i32, i32>) -> i32 {
            self.extract().add_together(other.as_ref())
        }
    }

    // Despite the complexity of the bounds for this function, in much more complex
    // use cases it can dramatically decreases complexity and redundancy. The main
    // point though, is that the function is extremely simple to call and can easily
    // be composed in further functions using `CloneOnExtract` and is completely generic over
    // value or reference arguments.
    #[allow(unused)]
    pub fn add_together_and_double<T: Clone>(lhs: CloneOnExtract<T, T>, rhs: CloneOnExtract<T, T>) -> i32
    where
        for<'a, 'b> CloneOnExtract<'a, T, T>: AddTogether<CloneOnExtract<'b, T, T>>,
    {
        lhs.as_borrowed().add_together(rhs.as_borrowed()) + lhs.as_borrowed().add_together(rhs)
    }

    // Note: CloneOnExtract() converts to an owned value but if we only had a reference we could
    // use as_CloneOnExtract() insead. If our type implemented Deref then we also could use
    // CloneOnExtract_deref() instead of cbt().
    #[test]
    fn test() {
        assert_eq!(add_together_and_double(1u8.coe(), 2u8.coe()), 6);
        assert_eq!(add_together_and_double(1i32.coe(), 2i32.coe()), 6);
    }
}
