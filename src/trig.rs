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

use crate::{clamp, Radians, Validate};
use core::ops::Neg;

/// The `UnitNegRange` newtype an f64.  
/// A valid `UnitNegRange` value lies between -1.0 and +1.0 inclusive.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct UnitNegRange(pub f64);

impl UnitNegRange {
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
    pub fn clamp(value: f64) -> Self {
        Self(clamp(value, -1.0, 1.0))
    }
}

impl Validate for UnitNegRange {
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
    fn is_valid(&self) -> bool {
        (-1.0..=1.0).contains(&self.0)
    }
}

impl Neg for UnitNegRange {
    type Output = Self;

    /// An implementation of Neg for `UnitNegRange`.  
    /// Negates the value.
    fn neg(self) -> Self {
        Self(0.0 - self.0)
    }
}

/// Swap the sine into the cosine of an Angle and vice versa.  
/// Uses the identity sin<sup>2</sup> + cos<sup>2</sup> = 1.
/// See:
/// [Pythagorean identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Pythagorean_identities)  
/// # Examples
/// ```
/// use angle_sc::trig::{UnitNegRange, swap_sin_cos};
///
/// assert_eq!(UnitNegRange(0.0), swap_sin_cos(UnitNegRange(-1.0)));
/// assert_eq!(UnitNegRange(1.0), swap_sin_cos(UnitNegRange(0.0)));
/// ```
#[must_use]
pub fn swap_sin_cos(a: UnitNegRange) -> UnitNegRange {
    UnitNegRange::clamp(libm::sqrt((1.0 - a.0) * (1.0 + a.0)))
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
/// assert_eq!(1.0, cosine_from_sine(UnitNegRange(0.0), 1.0).0);
/// assert_eq!(-1.0, cosine_from_sine(UnitNegRange(0.0), -1.0).0);
/// ```
#[must_use]
pub fn cosine_from_sine(a: UnitNegRange, sign: f64) -> UnitNegRange {
    UnitNegRange(libm::copysign(swap_sin_cos(a).0, sign))
}

/// Calculate the sine of the difference of two angles: a - b.  
/// See:
/// [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).  
/// * `sin_a`, `cos_a` the sine and cosine of angle a.
/// * `sin_b`, `cos_b` the sine and cosine of angle b.
///
/// return sin(a - b)
#[must_use]
pub fn sine_diff(
    sin_a: UnitNegRange,
    cos_a: UnitNegRange,
    sin_b: UnitNegRange,
    cos_b: UnitNegRange,
) -> UnitNegRange {
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
pub fn sine_sum(
    sin_a: UnitNegRange,
    cos_a: UnitNegRange,
    sin_b: UnitNegRange,
    cos_b: UnitNegRange,
) -> UnitNegRange {
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
pub fn cosine_diff(
    sin_a: UnitNegRange,
    cos_a: UnitNegRange,
    sin_b: UnitNegRange,
    cos_b: UnitNegRange,
) -> UnitNegRange {
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
pub fn cosine_sum(
    sin_a: UnitNegRange,
    cos_a: UnitNegRange,
    sin_b: UnitNegRange,
    cos_b: UnitNegRange,
) -> UnitNegRange {
    cosine_diff(sin_a, cos_a, -sin_b, cos_b)
}

/// Square of the sine of half the Angle.  
/// See: [Half-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae)
/// # Examples
#[must_use]
pub fn sq_sine_half(cos: UnitNegRange) -> f64 {
    (1.0 - cos.0) * 0.5
}

/// Square of the cosine of half the Angle.  
/// See: [Half-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae)
#[must_use]
pub fn sq_cosine_half(cos: UnitNegRange) -> f64 {
    (1.0 + cos.0) * 0.5
}

/// Calculate the length of the adjacent side of a right angled spherical
/// triangle, given the cosine of the angle and length of the hypotenuse.
/// @pre 0 <= length < `PI_2`
/// * `cos_angle` the cosine of the adjacent angle.
/// * `length` the length of the hypotenuse
///
/// return the length of the opposite side.
#[must_use]
pub fn spherical_cosine_rule(cos_angle: UnitNegRange, length: Radians) -> Radians {
    Radians(libm::atan(cos_angle.0 * libm::tan(length.0)))
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

        let minus_one: UnitNegRange = -one;
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
        let sin_60 = swap_sin_cos(cos_60);

        let sin_120 = sin_60;
        let cos_120 = cosine_from_sine(sin_120, -1.0);

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

    #[test]
    fn test_spherical_cosine_rule() {
        let result = spherical_cosine_rule(UnitNegRange(0.0), Radians(1.0));
        assert_eq!(0.0, result.0);

        let result = spherical_cosine_rule(UnitNegRange(0.8660254037844386), Radians(0.5));
        assert_eq!(0.44190663576327144, result.0);

        let result = spherical_cosine_rule(UnitNegRange(0.5), Radians(1.0));
        assert_eq!(0.66161993185017653, result.0);

        let result = spherical_cosine_rule(UnitNegRange(1.0), Radians(1.0));
        assert_eq!(1.0, result.0);
    }
}
