use ::core::intrinsics::const_eval_select;
use ::core::marker::Destruct;
use core::ops::{Div, Rem};

use crate::float::FloatCore;

pub const trait Euclid:
    Sized + [const] Div<Self, Output = Self> + [const] Rem<Self, Output = Self>
{
    /// Calculates Euclidean division, the matching method for `rem_euclid`.
    ///
    /// This computes the integer `n` such that
    /// `self = n * v + self.rem_euclid(v)`.
    /// In other words, the result is `self / v` rounded to the integer `n`
    /// such that `self >= n * v`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::Euclid;
    ///
    /// let a: i32 = 7;
    /// let b: i32 = 4;
    /// assert_eq!(Euclid::div_euclid(&a, &b), 1); // 7 > 4 * 1
    /// assert_eq!(Euclid::div_euclid(&-a, &b), -2); // -7 >= 4 * -2
    /// assert_eq!(Euclid::div_euclid(&a, &-b), -1); // 7 >= -4 * -1
    /// assert_eq!(Euclid::div_euclid(&-a, &-b), 2); // -7 >= -4 * 2
    /// ```
    fn div_euclid(&self, v: &Self) -> Self;

    /// Calculates the least nonnegative remainder of `self (mod v)`.
    ///
    /// In particular, the return value `r` satisfies `0.0 <= r < v.abs()` in
    /// most cases. However, due to a floating point round-off error it can
    /// result in `r == v.abs()`, violating the mathematical definition, if
    /// `self` is much smaller than `v.abs()` in magnitude and `self < 0.0`.
    /// This result is not an element of the function's codomain, but it is the
    /// closest floating point number in the real numbers and thus fulfills the
    /// property `self == self.div_euclid(v) * v + self.rem_euclid(v)`
    /// approximatively.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_traits::Euclid;
    ///
    /// let a: i32 = 7;
    /// let b: i32 = 4;
    /// assert_eq!(Euclid::rem_euclid(&a, &b), 3);
    /// assert_eq!(Euclid::rem_euclid(&-a, &b), 1);
    /// assert_eq!(Euclid::rem_euclid(&a, &-b), 3);
    /// assert_eq!(Euclid::rem_euclid(&-a, &-b), 1);
    /// ```
    fn rem_euclid(&self, v: &Self) -> Self;

    /// Returns both the quotient and remainder from Euclidean division.
    ///
    /// By default, it internally calls both `Euclid::div_euclid` and `Euclid::rem_euclid`,
    /// but it can be overridden in order to implement some optimization.
    ///
    /// # Examples
    ///
    /// ```
    /// # use num_traits::Euclid;
    /// let x = 5u8;
    /// let y = 3u8;
    ///
    /// let div = Euclid::div_euclid(&x, &y);
    /// let rem = Euclid::rem_euclid(&x, &y);
    ///
    /// assert_eq!((div, rem), Euclid::div_rem_euclid(&x, &y));
    /// ```
    fn div_rem_euclid(&self, v: &Self) -> (Self, Self) {
        (self.div_euclid(v), self.rem_euclid(v))
    }
}

macro_rules! euclid_forward_impl {
    ($($t:ty)*) => {$(
        impl const Euclid for $t {
            #[inline]
            fn div_euclid(&self, v: &$t) -> Self {
                <$t>::div_euclid(*self, *v)
            }

            #[inline]
            fn rem_euclid(&self, v: &$t) -> Self {
                <$t>::rem_euclid(*self, *v)
            }
        }
    )*}
}

euclid_forward_impl!(isize i8 i16 i32 i64 i128);
euclid_forward_impl!(usize u8 u16 u32 u64 u128);

const fn div_euclid_in_const<F: const FloatCore>(s: F, v: F) -> F {
    let q = (s / v).trunc();
    if s % v >= F::zero() {
        q
    } else if v > F::zero() {
        q - F::one()
    } else {
        q + F::one()
    }
}
const fn rem_euclid_in_const<F: const FloatCore>(s: F, v: F) -> F {
    let r = s % v;
    if r < F::zero() {
        r + v.abs()
    } else {
        r
    }
}

#[cfg(not(feature = "std"))]
use ::core::{f32::math as emathf, f64::math as emathd};
#[cfg(feature = "std")]
use ::std::primitive::{f32 as emathf, f64 as emathd};

impl const Euclid for f32 {
    fn div_euclid(&self, v: &Self) -> Self {
        const_eval_select((*self, *v), div_euclid_in_const, emathf::div_euclid)
    }
    fn rem_euclid(&self, v: &Self) -> Self {
        const_eval_select((*self, *v), rem_euclid_in_const, emathf::rem_euclid)
    }
}
impl const Euclid for f64 {
    fn div_euclid(&self, v: &Self) -> Self {
        const_eval_select((*self, *v), div_euclid_in_const, emathd::div_euclid)
    }
    fn rem_euclid(&self, v: &Self) -> Self {
        const_eval_select((*self, *v), rem_euclid_in_const, emathd::rem_euclid)
    }
}

pub const trait CheckedEuclid: [const] Euclid {
    /// Performs euclid division, returning `None` on division by zero or if
    /// overflow occurred.
    fn checked_div_euclid(&self, v: &Self) -> Option<Self>;

    /// Finds the euclid remainder of dividing two numbers, returning `None` on
    /// division by zero or if overflow occurred.
    fn checked_rem_euclid(&self, v: &Self) -> Option<Self>;

    /// Returns both the quotient and remainder from checked Euclidean division,
    /// returning `None` on division by zero or if overflow occurred.
    ///
    /// By default, it internally calls both `CheckedEuclid::checked_div_euclid` and `CheckedEuclid::checked_rem_euclid`,
    /// but it can be overridden in order to implement some optimization.
    /// # Examples
    ///
    /// ```
    /// # use num_traits::CheckedEuclid;
    /// let x = 5u8;
    /// let y = 3u8;
    ///
    /// let div = CheckedEuclid::checked_div_euclid(&x, &y);
    /// let rem = CheckedEuclid::checked_rem_euclid(&x, &y);
    ///
    /// assert_eq!(Some((div.unwrap(), rem.unwrap())), CheckedEuclid::checked_div_rem_euclid(&x, &y));
    /// ```
    fn checked_div_rem_euclid(&self, v: &Self) -> Option<(Self, Self)>
    where
        Option<Self>: [const] Destruct,
    {
        let Some(d) = self.checked_div_euclid(v) else {
            return None;
        };
        let Some(r) = self.checked_rem_euclid(v) else {
            return None;
        };
        Some((d, r))
    }
}

macro_rules! checked_euclid_forward_impl {
    ($($t:ty)*) => {$(
        impl const CheckedEuclid for $t {
            #[inline]
            fn checked_div_euclid(&self, v: &$t) -> Option<Self> {
                <$t>::checked_div_euclid(*self, *v)
            }

            #[inline]
            fn checked_rem_euclid(&self, v: &$t) -> Option<Self> {
                <$t>::checked_rem_euclid(*self, *v)
            }
        }
    )*}
}

checked_euclid_forward_impl!(isize i8 i16 i32 i64 i128);
checked_euclid_forward_impl!(usize u8 u16 u32 u64 u128);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn euclid_unsigned() {
        macro_rules! test_euclid {
            ($($t:ident)+) => {
                $(
                    {
                        let x: $t = 10;
                        let y: $t = 3;
                        let div = Euclid::div_euclid(&x, &y);
                        let rem = Euclid::rem_euclid(&x, &y);
                        assert_eq!(div, 3);
                        assert_eq!(rem, 1);
                        assert_eq!((div, rem), Euclid::div_rem_euclid(&x, &y));
                    }
                )+
            };
        }

        test_euclid!(usize u8 u16 u32 u64);
    }

    #[test]
    fn euclid_signed() {
        macro_rules! test_euclid {
            ($($t:ident)+) => {
                $(
                    {
                        let x: $t = 10;
                        let y: $t = -3;
                        assert_eq!(Euclid::div_euclid(&x, &y), -3);
                        assert_eq!(Euclid::div_euclid(&-x, &y), 4);
                        assert_eq!(Euclid::rem_euclid(&x, &y), 1);
                        assert_eq!(Euclid::rem_euclid(&-x, &y), 2);
                        assert_eq!((Euclid::div_euclid(&x, &y), Euclid::rem_euclid(&x, &y)), Euclid::div_rem_euclid(&x, &y));
                        let x: $t = $t::min_value() + 1;
                        let y: $t = -1;
                        assert_eq!(Euclid::div_euclid(&x, &y), $t::max_value());
                    }
                )+
            };
        }

        test_euclid!(isize i8 i16 i32 i64 i128);
    }

    #[test]
    fn euclid_float() {
        macro_rules! test_euclid {
            ($($t:ident)+) => {
                $(
                    {
                        let x: $t = 12.1;
                        let y: $t = 3.2;
                        assert!(Euclid::div_euclid(&x, &y) * y + Euclid::rem_euclid(&x, &y) - x
                        <= 46.4 * <$t as crate::float::FloatCore>::epsilon());
                        assert!(Euclid::div_euclid(&x, &-y) * -y + Euclid::rem_euclid(&x, &-y) - x
                        <= 46.4 * <$t as crate::float::FloatCore>::epsilon());
                        assert!(Euclid::div_euclid(&-x, &y) * y + Euclid::rem_euclid(&-x, &y) + x
                        <= 46.4 * <$t as crate::float::FloatCore>::epsilon());
                        assert!(Euclid::div_euclid(&-x, &-y) * -y + Euclid::rem_euclid(&-x, &-y) + x
                        <= 46.4 * <$t as crate::float::FloatCore>::epsilon());
                        assert_eq!((Euclid::div_euclid(&x, &y), Euclid::rem_euclid(&x, &y)), Euclid::div_rem_euclid(&x, &y));
                    }
                )+
            };
        }

        test_euclid!(f32 f64);
    }

    #[test]
    fn euclid_checked() {
        macro_rules! test_euclid_checked {
            ($($t:ident)+) => {
                $(
                    {
                        assert_eq!(CheckedEuclid::checked_div_euclid(&$t::min_value(), &-1), None);
                        assert_eq!(CheckedEuclid::checked_rem_euclid(&$t::min_value(), &-1), None);
                        assert_eq!(CheckedEuclid::checked_div_euclid(&1, &0), None);
                        assert_eq!(CheckedEuclid::checked_rem_euclid(&1, &0), None);
                    }
                )+
            };
        }

        test_euclid_checked!(isize i8 i16 i32 i64 i128);
    }
}
