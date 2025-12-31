use ::core::ops::Sub;
use core::num::Wrapping;
use core::ops::Neg;

use crate::__non_backwards_compatible_required_reexports::NumConstShim;
use crate::float::{Float, FloatCore};
use crate::{Num, Zero};

/// Useful functions for signed numbers (i.e. numbers that can be negative).
pub const trait Signed:
    Sized + Num + [const] NumConstShim + [const] Neg<Output = Self>
{
    /// Computes the absolute value.
    ///
    /// For `f32` and `f64`, `NaN` will be returned if the number is `NaN`.
    ///
    /// For signed integers, `::MIN` will be returned if the number is `::MIN`.
    fn abs(&self) -> Self;

    /// The positive difference of two numbers.
    ///
    /// Returns `zero` if the number is less than or equal to `other`, otherwise the difference
    /// between `self` and `other` is returned.
    fn abs_sub(&self, other: &Self) -> Self;

    /// Returns the sign of the number.
    ///
    /// For `f32` and `f64`:
    ///
    /// * `1.0` if the number is positive, `+0.0` or `INFINITY`
    /// * `-1.0` if the number is negative, `-0.0` or `NEG_INFINITY`
    /// * `NaN` if the number is `NaN`
    ///
    /// For signed integers:
    ///
    /// * `0` if the number is zero
    /// * `1` if the number is positive
    /// * `-1` if the number is negative
    fn signum(&self) -> Self;

    /// Returns true if the number is positive and false if the number is zero or negative.
    fn is_positive(&self) -> bool;

    /// Returns true if the number is negative and false if the number is zero or positive.
    fn is_negative(&self) -> bool;
}
#[inline]
const fn abs_sub_default<T>(a: T, b: T) -> T
where
    T: [const] PartialOrd + [const] Sub<T, Output = T> + [const] Zero,
{
    if a <= b { T::zero() } else { a - b }
}

macro_rules! signed_impl {
    ($($t:ty)*) => ($(
        impl const Signed for $t {
            #[inline]
            fn abs(&self) -> $t {
                <$t>::abs(*self)
            }

            #[inline]
            fn abs_sub(&self, other: &$t) -> $t {
                abs_sub_default(*self, *other)
            }

            #[inline]
            fn signum(&self) -> $t {
                <$t>::signum(*self)
            }

            #[inline]
            fn is_positive(&self) -> bool {
                <$t>::is_positive(*self)
            }

            #[inline]
            fn is_negative(&self) -> bool {
                <$t>::is_negative(*self)
            }
        }
    )*)
}

signed_impl!(isize i8 i16 i32 i64 i128);

impl<T: [const] Signed> const Signed for Wrapping<T>
where
    Wrapping<T>: Num + [const] NumConstShim + [const] Neg<Output = Wrapping<T>>,
{
    #[inline]
    fn abs(&self) -> Self {
        Wrapping(self.0.abs())
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
        Wrapping(self.0.abs_sub(&other.0))
    }

    #[inline]
    fn signum(&self) -> Self {
        Wrapping(self.0.signum())
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.0.is_positive()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.0.is_negative()
    }
}

macro_rules! signed_float_impl {
    ($t:ty) => {
        impl const Signed for $t {
            /// Computes the absolute value. Returns `NAN` if the number is `NAN`.
            #[inline]
            fn abs(&self) -> $t {
                FloatCore::abs(*self)
            }

            /// The positive difference of two numbers. Returns `0.0` if the number is
            /// less than or equal to `other`, otherwise the difference between`self`
            /// and `other` is returned.
            #[inline]
            fn abs_sub(&self, other: &$t) -> $t {
                #[cfg(any(feature = "libm", feature = "std"))]
                return Float::abs_sub(*self, *other);

                #[cfg(not(any(feature = "libm", feature = "std")))]
                return abs_sub_default(*self, *other);
            }

            /// # Returns
            ///
            /// - `1.0` if the number is positive, `+0.0` or `INFINITY`
            /// - `-1.0` if the number is negative, `-0.0` or `NEG_INFINITY`
            /// - `NAN` if the number is NaN
            #[inline]
            fn signum(&self) -> $t {
                FloatCore::signum(*self)
            }

            /// Returns `true` if the number is positive, including `+0.0` and `INFINITY`
            #[inline]
            fn is_positive(&self) -> bool {
                FloatCore::is_sign_positive(*self)
            }

            /// Returns `true` if the number is negative, including `-0.0` and `NEG_INFINITY`
            #[inline]
            fn is_negative(&self) -> bool {
                FloatCore::is_sign_negative(*self)
            }
        }
    };
}

signed_float_impl!(f32);
signed_float_impl!(f64);

/// Computes the absolute value.
///
/// For `f32` and `f64`, `NaN` will be returned if the number is `NaN`
///
/// For signed integers, `::MIN` will be returned if the number is `::MIN`.
#[inline(always)]
pub fn abs<T: Signed>(value: T) -> T {
    value.abs()
}

/// The positive difference of two numbers.
///
/// Returns zero if `x` is less than or equal to `y`, otherwise the difference
/// between `x` and `y` is returned.
#[inline(always)]
pub fn abs_sub<T: Signed>(x: T, y: T) -> T {
    x.abs_sub(&y)
}

/// Returns the sign of the number.
///
/// For `f32` and `f64`:
///
/// * `1.0` if the number is positive, `+0.0` or `INFINITY`
/// * `-1.0` if the number is negative, `-0.0` or `NEG_INFINITY`
/// * `NaN` if the number is `NaN`
///
/// For signed integers:
///
/// * `0` if the number is zero
/// * `1` if the number is positive
/// * `-1` if the number is negative
#[inline(always)]
pub fn signum<T: Signed>(value: T) -> T {
    value.signum()
}

/// A trait for values which cannot be negative
pub trait Unsigned: Num {}

macro_rules! empty_trait_impl {
    ($name:ident for $($t:ty)*) => ($(
        impl $name for $t {}
    )*)
}

empty_trait_impl!(Unsigned for usize u8 u16 u32 u64 u128);

impl<T: Unsigned> Unsigned for Wrapping<T> where Wrapping<T>: Num {}

#[test]
fn unsigned_wrapping_is_unsigned() {
    fn require_unsigned<T: Unsigned>(_: &T) {}
    require_unsigned(&Wrapping(42_u32));
}

#[test]
fn signed_wrapping_is_signed() {
    fn require_signed<T: Signed>(_: &T) {}
    require_signed(&Wrapping(-42));
}
