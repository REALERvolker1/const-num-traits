use ::core::marker::Destruct;
use core::num::Wrapping;
use core::ops::{Add, Mul};

#[cfg(has_num_saturating)]
use core::num::Saturating;

/// Defines an additive identity element for `Self`.
///
/// # Laws
///
/// ```text
/// a + 0 = a       ∀ a ∈ Self
/// 0 + a = a       ∀ a ∈ Self
/// ```
pub const trait Zero: Sized + [const] Add<Self, Output = Self> + [const] Destruct {
    /// Returns the additive identity element of `Self`, `0`.
    /// # Purity
    ///
    /// This function should return the same result at all times regardless of
    /// external mutable state, for example values stored in TLS or in
    /// `static mut`s.
    // This cannot be an associated constant, because of bignums.
    fn zero() -> Self;

    /// Sets `self` to the additive identity element of `Self`, `0`.
    #[inline]
    fn set_zero(&mut self) {
        *self = Zero::zero();
    }

    /// Returns `true` if `self` is equal to the additive identity.
    fn is_zero(&self) -> bool;
}

/// Defines an associated constant representing the additive identity element
/// for `Self`.
pub trait ConstZero: Zero {
    /// The additive identity element of `Self`, `0`.
    const ZERO: Self;
}

macro_rules! zero_impl {
    ($t:ty, $v:expr) => {
        impl const Zero for $t {
            #[inline]
            fn zero() -> $t {
                $v
            }
            #[inline]
            fn is_zero(&self) -> bool {
                *self == $v
            }
        }

        impl ConstZero for $t {
            const ZERO: Self = $v;
        }
    };
}

zero_impl!(usize, 0);
zero_impl!(u8, 0);
zero_impl!(u16, 0);
zero_impl!(u32, 0);
zero_impl!(u64, 0);
zero_impl!(u128, 0);

zero_impl!(isize, 0);
zero_impl!(i8, 0);
zero_impl!(i16, 0);
zero_impl!(i32, 0);
zero_impl!(i64, 0);
zero_impl!(i128, 0);

zero_impl!(f32, 0.0);
zero_impl!(f64, 0.0);

impl<T: [const] Zero> const Zero for Wrapping<T>
where
    Wrapping<T>: [const] Add<Output = Wrapping<T>>,
{
    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
    #[inline]
    fn set_zero(&mut self) {
        self.0.set_zero();
    }
    #[inline]
    fn zero() -> Self {
        Wrapping(T::zero())
    }
}

impl<T: ConstZero> ConstZero for Wrapping<T>
where
    Wrapping<T>: Add<Output = Wrapping<T>>,
{
    const ZERO: Self = Wrapping(T::ZERO);
}

#[cfg(has_num_saturating)]
impl<T: [const] Zero> const Zero for Saturating<T>
where
    Saturating<T>: [const] Add<Output = Saturating<T>>,
{
    #[inline]
    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
    #[inline]
    fn set_zero(&mut self) {
        self.0.set_zero();
    }
    #[inline]
    fn zero() -> Self {
        Saturating(T::zero())
    }
}

#[cfg(has_num_saturating)]
impl<T: ConstZero> ConstZero for Saturating<T>
where
    Saturating<T>: Add<Output = Saturating<T>>,
{
    const ZERO: Self = Saturating(T::ZERO);
}

/// Defines a multiplicative identity element for `Self`.
///
/// # Laws
///
/// ```text
/// a * 1 = a       ∀ a ∈ Self
/// 1 * a = a       ∀ a ∈ Self
/// ```
pub const trait One: Sized + [const] Mul<Self, Output = Self> + [const] Destruct {
    /// Returns the multiplicative identity element of `Self`, `1`.
    ///
    /// # Purity
    ///
    /// This function should return the same result at all times regardless of
    /// external mutable state, for example values stored in TLS or in
    /// `static mut`s.
    // This cannot be an associated constant, because of bignums.
    fn one() -> Self;

    /// Sets `self` to the multiplicative identity element of `Self`, `1`.
    #[inline]
    fn set_one(&mut self) {
        *self = One::one();
    }

    /// Returns `true` if `self` is equal to the multiplicative identity.
    ///
    /// For performance reasons, it's best to implement this manually.
    /// After a semver bump, this method will be required, and the
    /// `where Self: PartialEq` bound will be removed.
    #[inline]
    fn is_one(&self) -> bool
    where
        Self: [const] PartialEq,
    {
        *self == Self::one()
    }
}

/// Defines an associated constant representing the multiplicative identity
/// element for `Self`.
pub trait ConstOne: One {
    /// The multiplicative identity element of `Self`, `1`.
    const ONE: Self;
}

macro_rules! one_impl {
    ($t:ty, $v:expr) => {
        impl const One for $t {
            #[inline]
            fn one() -> $t {
                $v
            }
            #[inline]
            fn is_one(&self) -> bool {
                *self == $v
            }
        }

        impl ConstOne for $t {
            const ONE: Self = $v;
        }
    };
}

one_impl!(usize, 1);
one_impl!(u8, 1);
one_impl!(u16, 1);
one_impl!(u32, 1);
one_impl!(u64, 1);
one_impl!(u128, 1);

one_impl!(isize, 1);
one_impl!(i8, 1);
one_impl!(i16, 1);
one_impl!(i32, 1);
one_impl!(i64, 1);
one_impl!(i128, 1);

one_impl!(f32, 1.0);
one_impl!(f64, 1.0);

impl<T: [const] One> const One for Wrapping<T>
where
    Wrapping<T>: [const] Mul<Output = Wrapping<T>>,
{
    #[inline]
    fn set_one(&mut self) {
        self.0.set_one();
    }
    #[inline]
    fn one() -> Self {
        Wrapping(T::one())
    }
}

impl<T: ConstOne> ConstOne for Wrapping<T>
where
    Wrapping<T>: Mul<Output = Wrapping<T>>,
{
    const ONE: Self = Wrapping(T::ONE);
}

#[cfg(has_num_saturating)]
impl<T: [const] One> const One for Saturating<T>
where
    Saturating<T>: [const] Mul<Output = Saturating<T>>,
{
    #[inline]
    fn set_one(&mut self) {
        self.0.set_one();
    }
    #[inline]
    fn one() -> Self {
        Saturating(T::one())
    }
}

#[cfg(has_num_saturating)]
impl<T: ConstOne> ConstOne for Saturating<T>
where
    Saturating<T>: Mul<Output = Saturating<T>>,
{
    const ONE: Self = Saturating(T::ONE);
}

// Some helper functions provided for backwards compatibility.

/// Returns the additive identity, `0`.
#[inline(always)]
pub fn zero<T: Zero>() -> T {
    Zero::zero()
}

/// Returns the multiplicative identity, `1`.
#[inline(always)]
pub fn one<T: One>() -> T {
    One::one()
}

#[test]
fn wrapping_identities() {
    macro_rules! test_wrapping_identities {
        ($($t:ty)+) => {
            $(
                assert_eq!(zero::<$t>(), zero::<Wrapping<$t>>().0);
                assert_eq!(one::<$t>(), one::<Wrapping<$t>>().0);
                assert_eq!((0 as $t).is_zero(), Wrapping(0 as $t).is_zero());
                assert_eq!((1 as $t).is_zero(), Wrapping(1 as $t).is_zero());
            )+
        };
    }

    test_wrapping_identities!(isize i8 i16 i32 i64 usize u8 u16 u32 u64);
}

#[test]
fn wrapping_is_zero() {
    fn require_zero<T: Zero>(_: &T) {}
    require_zero(&Wrapping(42));
}
#[test]
fn wrapping_is_one() {
    fn require_one<T: One>(_: &T) {}
    require_one(&Wrapping(42));
}

#[test]
#[cfg(has_num_saturating)]
fn saturating_identities() {
    macro_rules! test_saturating_identities {
        ($($t:ty)+) => {
            $(
                assert_eq!(zero::<$t>(), zero::<Saturating<$t>>().0);
                assert_eq!(one::<$t>(), one::<Saturating<$t>>().0);
                assert_eq!((0 as $t).is_zero(), Saturating(0 as $t).is_zero());
                assert_eq!((1 as $t).is_zero(), Saturating(1 as $t).is_zero());
            )+
        };
    }

    test_saturating_identities!(isize i8 i16 i32 i64 usize u8 u16 u32 u64);
}

#[test]
#[cfg(has_num_saturating)]
fn saturating_is_zero() {
    fn require_zero<T: Zero>(_: &T) {}
    require_zero(&Saturating(42));
}
#[test]
#[cfg(has_num_saturating)]
fn saturating_is_one() {
    fn require_one<T: One>(_: &T) {}
    require_one(&Saturating(42));
}
