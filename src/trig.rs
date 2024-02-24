// Copyright (c) 2024 Ken Barker

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

//! The `trig` module contains the `UnitNegRange` newtype struct and
//! trigonometric functions which use it.

#![allow(clippy::float_cmp)]
#![allow(clippy::suboptimal_flops)]

use crate::Validate;
use core::ops::Neg;
use num_traits::{Num, NumCast};

/// The `UnitNegRange` newtype.  
/// A valid `UnitNegRange` value lies between -1.0 and +1.0 inclusive.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct UnitNegRange<T>(pub T);

impl<T: Num + NumCast + PartialOrd> UnitNegRange<T> {
    /// Clamp value into the valid range: -1.0 to +1.0 inclusive.
    /// # Examples
    /// ```
    /// use angle_sc::trig::UnitNegRange;
    /// use core::f64::EPSILON;
    ///
    /// assert_eq!(-1.0, UnitNegRange::clamp(-1.0 - EPSILON).0);
    /// assert_eq!(-1.0, UnitNegRange::clamp(-1.0).0);
    /// assert_eq!(-0.5, UnitNegRange::clamp(-0.5).0);
    /// assert_eq!(1.0, UnitNegRange::clamp(1.0).0);
    /// assert_eq!(1.0, UnitNegRange::clamp(1.0 + EPSILON).0);
    /// ```
    #[must_use]
    pub fn clamp(value: T) -> Self
    where
        T: NumCast + PartialOrd,
    {
        let m_one: T = num_traits::cast(-1).unwrap();
        let one: T = num_traits::cast(1).unwrap();
        Self(num_traits::clamp(value, m_one, one))
    }
}

impl<T: Num + NumCast + PartialOrd> Validate for UnitNegRange<T> {
    /// Test whether a `UnitNegRange` is valid.  
    /// I.e. whether it lies in the range: -1.0 <= value <= 1.0
    /// # Examples
    /// ```
    /// use angle_sc::trig::UnitNegRange;
    /// use angle_sc::Validate;
    /// use core::f64::EPSILON;
    ///
    /// assert!(!UnitNegRange(-1.0 - EPSILON).is_valid());
    /// assert!(UnitNegRange(-1.0).is_valid());
    /// assert!(UnitNegRange(1.0).is_valid());
    /// assert!(!(UnitNegRange(1.0 + EPSILON).is_valid()));
    /// ```
    #[must_use]
    fn is_valid(&self) -> bool
    where
        T: NumCast + PartialOrd,
    {
        let one: T = num_traits::cast(1).unwrap();
        let m_one: T = num_traits::cast(-1).unwrap();
        (m_one..=one).contains(&self.0)
    }
}

impl<T: Num + NumCast + Copy> Neg for UnitNegRange<T> {
    type Output = Self;

    /// An implementation of Neg for `UnitNegRange`.  
    /// Negates the value.
    #[must_use]
    fn neg(self) -> Self {
        let zero: T = num_traits::cast(0).unwrap();
        Self(zero - self.0)
    }
}

/// Swap the sine into the cosine of an Angle and vice versa.  
/// Uses the identity sin<sup>2</sup> + cos<sup>2</sup> = 1.
/// See:
/// [Pythagorean identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Pythagorean_identities)  
/// # Examples
/// ```
/// use angle_sc::trig::swap_sin_cos;
///
/// assert_eq!(0.0, swap_sin_cos(-1.0));
/// assert_eq!(1.0, swap_sin_cos(0.0));
/// ```
#[must_use]
pub fn swap_sin_cos(a: f64) -> f64 {
    num_traits::clamp(libm::sqrt((1.0 - a) * (1.0 + a)), -1.0, 1.0)
}

/// Calculate the cosine of an Angle from it's sine and the sign of the cosine.
/// See: `swap_sin_cos`.
/// * `a` the sine of the angle.
/// * `sign` the sign of the cosine of the angle.
///
/// return the cosine of the Angle.
/// # Examples
/// ```
/// use angle_sc::trig::{UnitNegRange, cosine_from_sine};
///
/// assert_eq!(1.0, cosine_from_sine(0.0, 1.0));
/// assert_eq!(-1.0, cosine_from_sine(0.0, -1.0));
/// ```
#[must_use]
pub fn cosine_from_sine(a: f64, sign: f64) -> f64 {
    libm::copysign(swap_sin_cos(a), sign)
}

/// Calculate the sine of the difference of two angles: a - b.
/// See:
/// [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).
/// * `sin_a`, `cos_a` the sine and cosine of angle a.
/// * `sin_b`, `cos_b` the sine and cosine of angle b.
///
/// return sin(a - b)
#[must_use]
pub fn sine_diff<T>(
    sin_a: UnitNegRange<T>,
    cos_a: UnitNegRange<T>,
    sin_b: UnitNegRange<T>,
    cos_b: UnitNegRange<T>,
) -> UnitNegRange<T>
where
    T: Num + NumCast + PartialOrd,
{
    UnitNegRange::clamp(sin_a.0 * cos_b.0 - sin_b.0 * cos_a.0)
}

/// Calculate the sine of the sum of two angles: a + b.
/// See:
/// [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).
/// * `sin_a`, `cos_a` the sine and cosine of angle a.
/// * `sin_b`, `cos_b` the sine and cosine of angle b.
///
/// return sin(a + b)
#[must_use]
pub fn sine_sum<T>(
    sin_a: UnitNegRange<T>,
    cos_a: UnitNegRange<T>,
    sin_b: UnitNegRange<T>,
    cos_b: UnitNegRange<T>,
) -> UnitNegRange<T>
where
    T: Num + NumCast + PartialOrd + Copy + Neg,
{
    sine_diff(sin_a, cos_a, -sin_b, cos_b)
}

/// Calculate the cosine of the difference of two angles: a - b.
/// See:
/// [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).
/// * `sin_a`, `cos_a` the sine and cosine of angle a.
/// * `sin_b`, `cos_b` the sine and cosine of angle b.
///
/// return cos(a - b)
#[must_use]
pub fn cosine_diff<T>(
    sin_a: UnitNegRange<T>,
    cos_a: UnitNegRange<T>,
    sin_b: UnitNegRange<T>,
    cos_b: UnitNegRange<T>,
) -> UnitNegRange<T>
where
    T: Num + NumCast + PartialOrd,
{
    UnitNegRange::clamp(cos_a.0 * cos_b.0 + sin_a.0 * sin_b.0)
}

/// Calculate the cosine of the sum of two angles: a + b.
/// See:
/// [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).
/// * `sin_a`, `cos_a` the sine and cosine of angle a.
/// * `sin_b`, `cos_b` the sine and cosine of angle b.
///
/// return cos(a + b)
#[must_use]
pub fn cosine_sum<T>(
    sin_a: UnitNegRange<T>,
    cos_a: UnitNegRange<T>,
    sin_b: UnitNegRange<T>,
    cos_b: UnitNegRange<T>,
) -> UnitNegRange<T>
where
    T: Num + NumCast + PartialOrd + Copy + Neg,
{
    cosine_diff(sin_a, cos_a, -sin_b, cos_b)
}

/// Square of the sine of half the Angle.
/// See: [Half-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae)
/// # Examples
#[must_use]
pub fn sq_sine_half<T>(cos: UnitNegRange<T>) -> T
where
    T: Num + NumCast,
{
    let one: T = num_traits::cast(1).unwrap();
    let half: T = num_traits::cast(0.5).unwrap();
    half * (one - cos.0)
}

/// Square of the cosine of half the Angle.
/// See: [Half-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae)
#[must_use]
pub fn sq_cosine_half<T>(cos: UnitNegRange<T>) -> T
where
    T: Num + NumCast,
{
    let one: T = num_traits::cast(1).unwrap();
    let half: T = num_traits::cast(0.5).unwrap();
    half * (one + cos.0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::is_within_tolerance;
    use core::f64::EPSILON;

    #[test]
    fn unit_neg_range_traits() {
        let one = UnitNegRange(1.0);

        let one_clone = one.clone();
        assert!(one_clone == one);

        let minus_one = -one;
        assert!(minus_one == UnitNegRange(-1.0));
        assert!(minus_one < one);

        print!("UnitNegRange: {:?}", one);
    }

    #[test]
    fn unit_neg_range_clamp() {
        // value < -1
        assert_eq!(-1.0, UnitNegRange::clamp(-1.0 - EPSILON).0);
        // value = -1
        assert_eq!(-1.0, UnitNegRange::clamp(-1.0).0);
        // value = 1
        assert_eq!(1.0, UnitNegRange::clamp(1.0).0);
        // value > 1
        assert_eq!(1.0, UnitNegRange::clamp(1.0 + EPSILON).0);
    }

    #[test]
    fn unit_neg_range_is_valid() {
        assert!(!UnitNegRange(-1.0 - EPSILON).is_valid());
        assert!(UnitNegRange(-1.0).is_valid());
        assert!(UnitNegRange(1.0).is_valid());
        assert!(!UnitNegRange(1.0 + EPSILON).is_valid());
    }

    #[test]
    fn test_trig_functions() {
        let cos_60 = UnitNegRange(0.5);
        let sin_60 = swap_sin_cos(cos_60.0);

        let sin_120 = sin_60;
        let cos_120 = cosine_from_sine(sin_120, -1.0);

        let sin_60 = UnitNegRange::clamp(sin_60);
        let sin_120 = sin_60;
        let cos_120 = UnitNegRange::clamp(cos_120);

        assert!(is_within_tolerance(
            sin_120.0,
            sine_sum(sin_60, cos_60, sin_60, cos_60).0,
            EPSILON
        ));
        assert!(is_within_tolerance(
            cos_120.0,
            cosine_sum(sin_60, cos_60, sin_60, cos_60).0,
            EPSILON
        ));

        let result = sq_sine_half(cos_120);
        assert_eq!(sin_60.0, libm::sqrt(result));

        let result = sq_cosine_half(cos_120);
        assert!(is_within_tolerance(cos_60.0, libm::sqrt(result), EPSILON));
    }
}
