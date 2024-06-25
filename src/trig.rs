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
//! trigonometric functions.

#![allow(clippy::float_cmp)]
#![allow(clippy::suboptimal_flops)]

use crate::{Radians, Validate};
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
    ///
    /// assert_eq!(-1.0, UnitNegRange::clamp(-1.0 - f64::EPSILON).0);
    /// assert_eq!(-1.0, UnitNegRange::clamp(-1.0).0);
    /// assert_eq!(-0.5, UnitNegRange::clamp(-0.5).0);
    /// assert_eq!(1.0, UnitNegRange::clamp(1.0).0);
    /// assert_eq!(1.0, UnitNegRange::clamp(1.0 + f64::EPSILON).0);
    /// ```
    #[must_use]
    pub fn clamp(value: f64) -> Self {
        Self(value.clamp(-1.0, 1.0))
    }

    /// The absolute value of the `UnitNegRange`.
    #[must_use]
    pub fn abs(self) -> Self {
        Self(libm::fabs(self.0))
    }
}

impl Validate for UnitNegRange {
    /// Test whether a `UnitNegRange` is valid.  
    /// I.e. whether it lies in the range: -1.0 <= value <= 1.0
    /// # Examples
    /// ```
    /// use angle_sc::trig::UnitNegRange;
    /// use angle_sc::Validate;
    ///
    /// assert!(!UnitNegRange(-1.0 - f64::EPSILON).is_valid());
    /// assert!(UnitNegRange(-1.0).is_valid());
    /// assert!(UnitNegRange(1.0).is_valid());
    /// assert!(!(UnitNegRange(1.0 + f64::EPSILON).is_valid()));
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

/// Calculates the length of the other side in a right angled triangle,
/// given the length of one side and the hypotenuse.  
/// See: [Pythagorean theorem](https://en.wikipedia.org/wiki/Pythagorean_theorem)  
/// * `length` the length of a side.
/// * `hypotenuse` the length of the hypotenuse
///
/// returns the length of the other side.
/// zero if length >= hypotenuse or the hypotenuse if length <= 0.
#[must_use]
pub fn calculate_adjacent_length(length: f64, hypotenuse: f64) -> f64 {
    if length <= 0.0 {
        hypotenuse
    } else if length >= hypotenuse {
        0.0
    } else {
        libm::sqrt((hypotenuse - length) * (hypotenuse + length))
    }
}

/// Calculates the length of the other side in a right angled spherical
/// triangle, given the length of one side and the hypotenuse.  
/// See: [Spherical law of cosines](https://en.wikipedia.org/wiki/Spherical_law_of_cosines)
/// * `a` the length of a side.
/// * `c` the length of the hypotenuse
///
/// returns the length of the other side.
/// zero if a >= c or c if a <= 0.
#[must_use]
pub fn spherical_adjacent_length(a: Radians, c: Radians) -> Radians {
    if a <= Radians(0.0) {
        c
    } else if a >= c {
        Radians(0.0)
    } else {
        Radians(libm::acos(libm::cos(c.0) / libm::cos(a.0)))
    }
}

/// Calculates the length of the hypotenuse in a right angled spherical
/// triangle, given the length of both sides.  
/// See: [Spherical law of cosines](https://en.wikipedia.org/wiki/Spherical_law_of_cosines)  
/// * `a`, `b` the lengths of the sides adjacent to the right angle.
///
/// returns the length of the hypotenuse.
#[must_use]
pub fn spherical_hypotenuse_length(a: Radians, b: Radians) -> Radians {
    if a <= Radians(0.0) {
        b
    } else if b <= Radians(0.0) {
        a
    } else {
        Radians(libm::acos(libm::cos(a.0) * libm::cos(b.0)))
    }
}

/// Calculate the length of the adjacent side of a right angled spherical
/// triangle, given the cosine of the angle and length of the hypotenuse.  
/// See: [Spherical law of cosines](https://en.wikipedia.org/wiki/Spherical_law_of_cosines)  
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

    #[test]
    fn unit_neg_range_traits() {
        let one = UnitNegRange(1.0);

        let one_clone = one.clone();
        assert_eq!(one_clone, one);

        let minus_one: UnitNegRange = -one;
        assert_eq!(minus_one, UnitNegRange(-1.0));
        assert!(minus_one < one);
        assert_eq!(one, minus_one.abs());

        print!("UnitNegRange: {:?}", one);
    }

    #[test]
    fn unit_neg_range_clamp() {
        // value < -1
        assert_eq!(-1.0, UnitNegRange::clamp(-1.0 - f64::EPSILON).0);
        // value = -1
        assert_eq!(-1.0, UnitNegRange::clamp(-1.0).0);
        // value = 1
        assert_eq!(1.0, UnitNegRange::clamp(1.0).0);
        // value > 1
        assert_eq!(1.0, UnitNegRange::clamp(1.0 + f64::EPSILON).0);
    }

    #[test]
    fn unit_neg_range_is_valid() {
        assert!(!UnitNegRange(-1.0 - f64::EPSILON).is_valid());
        assert!(UnitNegRange(-1.0).is_valid());
        assert!(UnitNegRange(1.0).is_valid());
        assert!(!UnitNegRange(1.0 + f64::EPSILON).is_valid());
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
            f64::EPSILON
        ));
        assert!(is_within_tolerance(
            cos_120.0,
            cosine_sum(sin_60, cos_60, sin_60, cos_60).0,
            f64::EPSILON
        ));

        let result = sq_sine_half(cos_120);
        assert_eq!(sin_60.0, libm::sqrt(result));

        let result = sq_cosine_half(cos_120);
        assert!(is_within_tolerance(
            cos_60.0,
            libm::sqrt(result),
            f64::EPSILON
        ));
    }

    #[test]
    fn test_calculate_adjacent_length() {
        // length == hypotenuse
        assert_eq!(0.0, calculate_adjacent_length(5.0, 5.0));

        // length == 0.0
        assert_eq!(5.0, calculate_adjacent_length(0.0, 5.0));

        // length > hypotenuse
        assert_eq!(0.0, calculate_adjacent_length(6.0, 5.0));

        // 3, 4, 5 triangle
        assert_eq!(3.0, calculate_adjacent_length(4.0, 5.0));
    }

    #[test]
    fn test_spherical_adjacent_length() {
        // length == hypotenuse
        assert_eq!(
            Radians(0.0),
            spherical_adjacent_length(Radians(5.0_f64.to_radians()), Radians(5.0_f64.to_radians()))
        );

        // length == 0
        assert_eq!(
            Radians(5.0_f64.to_radians()),
            spherical_adjacent_length(Radians(0.0), Radians(5.0_f64.to_radians()))
        );

        // length > hypotenuse
        assert_eq!(
            Radians(0.0),
            spherical_adjacent_length(Radians(6.0_f64.to_radians()), Radians(5.0_f64.to_radians()))
        );

        // 3, 4, 5 triangle
        let result =
            spherical_adjacent_length(Radians(4.0_f64.to_radians()), Radians(5.0_f64.to_radians()));
        assert!(is_within_tolerance(3.0_f64.to_radians(), result.0, 1.0e-4));
    }

    #[test]
    fn test_spherical_hypotenuse_length() {
        let zero = Radians(0.0);
        let three = Radians(3.0_f64.to_radians());
        let four = Radians(4.0_f64.to_radians());

        // Negative length a
        assert_eq!(three, spherical_hypotenuse_length(-four, three));
        // Negative length b
        assert_eq!(four, spherical_hypotenuse_length(four, -three));

        // Zero length a
        assert_eq!(three, spherical_hypotenuse_length(zero, three));
        // Zero length b
        assert_eq!(four, spherical_hypotenuse_length(four, zero));
        // Zero length a & b
        assert_eq!(zero, spherical_hypotenuse_length(zero, zero));

        // 3, 4, 5 triangles, note 5 degrees is 0.08726646259971647 radians
        let result = Radians(0.087240926337265545);
        assert_eq!(result, spherical_hypotenuse_length(four, three));
        assert_eq!(result, spherical_hypotenuse_length(three, four));
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
