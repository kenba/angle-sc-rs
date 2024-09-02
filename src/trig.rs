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

//! The `trig` module contains accurate and efficient trigonometry functions.
//! 
//! The accuracy of the `libm::cos` function is poor for small angles,
//! so `cos` values are calculated from `sin` values
//! using [Pythagoras' theorem](https://en.wikipedia.org/wiki/Pythagorean_theorem)
//! by `cosine_from_sine`.
//! The `sin_small_angle` and `cos_small_angle` functions use the the
//! [small-angle approximation](https://en.wikipedia.org/wiki/Small-angle_approximation)
//! to avoid calling the `libm::sin` function.
//! They should not affect the accuracy of `sin` and `cos` values.
//! 
//! The `sincosd` and `sincos` functions use
//! [remquo](https://pubs.opengroup.org/onlinepubs/9699919799/functions/remquo.html)
//! and override the default `sin` and `cos` values for 30° and 45° to reduce
//! round-off errors.  
//! Their reciprocal functions: `arctan2d` and `arctan2`
//! also override the default values for 30° and 45° to reduce round-trip errors.  
//! The `sincosd_diff`and `sincos_diff` functions
//! and the `Add` and `Sub` traits for `Degrees` and `Radians` use the
//! [2Sum](https://en.wikipedia.org/wiki/2Sum) algorithm to reduce round-off errors.

#![allow(clippy::float_cmp, clippy::suboptimal_flops)]

use crate::{two_sum, Degrees, Radians, Validate};
use core::{f64, ops::Neg};

pub const SQ_EPSILON: f64 = f64::EPSILON * f64::EPSILON;

/// `core::f64::consts::SQRT_3` is currently a nightly-only experimental API,  
/// see <https://doc.rust-lang.org/core/f64/consts/constant.SQRT_3.html>
#[allow(clippy::excessive_precision, clippy::unreadable_literal)]
pub const SQRT_3: f64 = 1.732050807568877293527446341505872367_f64;

/// The cosine of 30 degrees: √3 / 2
pub const COS_30_DEGREES: f64 = SQRT_3 / 2.0;
/// The maximum angle in Radians where: `libm::sin(value) == value`
pub const MAX_LINEAR_SIN_ANGLE: Radians = Radians(9.67e7 * f64::EPSILON);
/// The maximum angle in Radians where: `swap_sin_cos(libm::sin(value)) == 1.0`
pub const MAX_COS_ANGLE_IS_ONE: Radians = Radians(3.35e7 * f64::EPSILON);

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

/// The cosecant of an angle.  
/// 
/// * `sin` the sine of the angle.
/// 
/// returns the cosecant or `None` if `sin < SQ_EPSILON`
#[must_use]
pub fn csc(sin: UnitNegRange) -> Option<f64> {
    if sin.abs().0 >= SQ_EPSILON {
        Some(1.0 / sin.0)
    } else {
        None
    }
}

/// The secant of an angle.  
/// 
/// * `cos` the cosine of the angle.
/// 
/// returns the secant or `None` if `cos < SQ_EPSILON`
#[must_use]
pub fn sec(cos: UnitNegRange) -> Option<f64> {
    if cos.abs().0 >= SQ_EPSILON {
        Some(1.0 / cos.0)
    } else {
        None
    }
}

/// The tangent of an angle.  
/// 
/// * `cos` the cosine of the angle.
/// 
/// returns the tangent or `None` if `cos < SQ_EPSILON`
#[must_use]
pub fn tan(sin: UnitNegRange, cos: UnitNegRange) -> Option<f64> {
    let secant = sec(cos)?;
    Some(sin.0 * secant)
}

/// The cotangent of an angle.  
/// 
/// * `sin` the sine of the angle.
/// 
/// returns the cotangent or `None` if `sin < SQ_EPSILON`
#[must_use]
pub fn cot(sin: UnitNegRange, cos: UnitNegRange) -> Option<f64> {
    let cosecant = csc(sin)?;
    Some(cos.0 * cosecant)
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

/// Calculate the sine of an angle in `Radians`.  
/// Uses the [small-angle approximation](https://en.wikipedia.org/wiki/Small-angle_approximation):
/// sin θ ≈ θ  
/// where θ ≤ `MAX_LINEAR_SIN_ANGLE`
#[must_use]
pub fn sin_small_angle(angle: Radians) -> UnitNegRange {
    if angle.abs() > MAX_LINEAR_SIN_ANGLE {
        UnitNegRange(libm::sin(angle.0))
    } else {
        UnitNegRange(angle.0)
    }
}

/// Calculate the cosine of an angle in `Radians` from the sine of the angle.  
/// Uses the [small-angle approximation](https://en.wikipedia.org/wiki/Small-angle_approximation):
/// cos θ ≈ θ  
/// where θ ≤ `MAX_COS_ANGLE_IS_ONE`
/// or the identity sin<sup>2</sup> + cos<sup>2</sup> = 1
#[must_use]
pub fn cos_small_angle(angle: Radians, sin: UnitNegRange) -> UnitNegRange {
    let angle_abs = angle.abs();
    if angle_abs > MAX_COS_ANGLE_IS_ONE {
        cosine_from_sine(sin, core::f64::consts::FRAC_PI_2 - angle_abs.0)
    } else {
        UnitNegRange(1.0)
    }
}

/// Assign `sin` and `cos` to the `remquo` quadrant: `q`
#[must_use]
fn assign_sin_cos_to_quadrant(
    sin: UnitNegRange,
    cos: UnitNegRange,
    q: i32,
) -> (UnitNegRange, UnitNegRange) {
    match q & 3 {
        0 => (sin, cos),
        1 => (cos, -sin),
        2 => (-sin, -cos),
        _ => (-cos, sin),
    }
}

/// Calculate the sine and cosine of an angle from an angle in `Radians` and
/// the quadrant from `libm::remquo`.  
/// 
/// * `radians` the angle in `Radians` in range `-FRAC_PI_4..=FRAC_PI_4`
/// * `q` the quadrant from `libm::remquo`.
/// 
/// returns sine and cosine of the angle as `UnitNegRange`s.
#[must_use]
fn sin_cos_from_remquo_pi_2(radians: Radians, q: i32) -> (UnitNegRange, UnitNegRange) {
    // Note: radians is in range -FRAC_PI_4..=FRAC_PI_4
    let mut sin = sin_small_angle(radians);
    let mut cos = cos_small_angle(radians, sin);

    let abs_radians = libm::fabs(radians.0);
    if abs_radians == core::f64::consts::FRAC_PI_6 {
        // 30 degrees is a special case
        sin = UnitNegRange(libm::copysign(0.5, radians.0));
        cos = UnitNegRange(COS_30_DEGREES);
    } else if abs_radians == core::f64::consts::FRAC_PI_4 {
        // 45 degrees is also a special case
        sin = UnitNegRange(libm::copysign(core::f64::consts::FRAC_1_SQRT_2, radians.0));
        cos = UnitNegRange(core::f64::consts::FRAC_1_SQRT_2);
    }

    assign_sin_cos_to_quadrant(sin, cos, q)
}

/// Calculate the sine and cosine of an angle from a value in `Radians`.  
/// Note: calculates the cosine of the angle from its sine and overrides the
/// sine and cosine for 30° and 45° to their correct values.
/// 
/// * `radians` the angle in `Radians`
/// 
/// returns sine and cosine of the angle as `UnitNegRange`s.
#[must_use]
pub fn sincos(radians: Radians) -> (UnitNegRange, UnitNegRange) {
    let rq: (f64, i32) = libm::remquo(radians.0, core::f64::consts::FRAC_PI_2);
    sin_cos_from_remquo_pi_2(Radians(rq.0), rq.1)
}

/// Calculate the sine and cosine of an angle from the difference of a pair of
/// values in `Radians`.  
/// Note: calculates the cosine of the angle from its sine and overrides the
/// sine and cosine for 30° and 45° to their correct values.
/// 
/// * `a`, `b` the angles in `Radians`
/// 
/// returns sine and cosine of a - b as `UnitNegRange`s.
#[must_use]
pub fn sincos_diff(a: Radians, b: Radians) -> (UnitNegRange, UnitNegRange) {
    let delta = two_sum(a.0, -b.0);
    let rq: (f64, i32) = libm::remquo(delta.0, core::f64::consts::FRAC_PI_2);
    sin_cos_from_remquo_pi_2(Radians(rq.0 + delta.1), rq.1)
}

/// Calculate the sine and cosine of an angle from an angle in `Degrees` and
/// the quadrant from `libm::remquo`.  
/// 
/// * `degrees` the angle in `Degrees` in range `-45.0..=45.0`
/// * `q` the quadrant from `libm::remquo`.
/// 
/// returns sine and cosine of the angle as `UnitNegRange`s.
#[must_use]
fn sin_cos_from_remquo_90(degrees: Degrees, q: i32) -> (UnitNegRange, UnitNegRange) {
    // Note: degrees is in range -45.0..=45.0
    let angle = Radians(degrees.0.to_radians());
    let mut sin = sin_small_angle(angle);
    let mut cos = cos_small_angle(angle, sin);

    let abs_degrees = libm::fabs(degrees.0);
    if abs_degrees == 30.0 {
        // 30 degrees is a special case
        sin = UnitNegRange(libm::copysign(0.5, degrees.0));
        cos = UnitNegRange(COS_30_DEGREES);
    } else if abs_degrees == 45.0 {
        // 45 degrees is also a special case
        sin = UnitNegRange(libm::copysign(core::f64::consts::FRAC_1_SQRT_2, degrees.0));
        cos = UnitNegRange(core::f64::consts::FRAC_1_SQRT_2);
    }

    assign_sin_cos_to_quadrant(sin, cos, q)
}

/// Calculate the sine and cosine of an angle from a value in `Degrees`.  
/// Note: calculates the cosine of the angle from its sine and overrides the
/// sine and cosine for 30° and 45° to their correct values.
/// 
/// * `degrees` the angle in `Degrees`
/// 
/// returns sine and cosine of the angle as `UnitNegRange`s.
#[must_use]
pub fn sincosd(degrees: Degrees) -> (UnitNegRange, UnitNegRange) {
    let rq: (f64, i32) = libm::remquo(degrees.0, 90.0);
    sin_cos_from_remquo_90(Degrees(rq.0), rq.1)
}

/// Calculate the sine and cosine of an angle from the difference of a pair of
/// values in `Degrees`.  
/// Note: calculates the cosine of the angle from its sine and overrides the
/// sine and cosine for 30° and 45° to their correct values.
/// 
/// * `a`, `b` the angles in `Degrees`
/// 
/// returns sine and cosine of a - b as `UnitNegRange`s.
#[must_use]
pub fn sincosd_diff(a: Degrees, b: Degrees) -> (UnitNegRange, UnitNegRange) {
    let delta = two_sum(a.0, -b.0);
    let rq: (f64, i32) = libm::remquo(delta.0, 90.0);
    sin_cos_from_remquo_90(Degrees(rq.0 + delta.1), rq.1)
}

/// Calculate an angle in `Radians` from the its sine and cosine.  
/// Uses the [small-angle approximation](https://en.wikipedia.org/wiki/Small-angle_approximation):
/// sin θ ≈ θ  
/// where cos θ = 1
#[must_use]
pub fn arctan2_small_angle(sin: UnitNegRange, cos: UnitNegRange) -> Radians {
    if cos.0 < 1.0 {
        Radians(libm::atan2(sin.0, cos.0))
    } else {
        Radians(sin.0)
    }
}

/// Accurately calculate an angle in `Radians` from its sine and cosine.
/// 
/// * `sin`, `cos` the sine and cosine of the angle in `UnitNegRange`s.
/// 
/// returns the angle in `Radians`.
#[must_use]
pub fn arctan2(sin: UnitNegRange, cos: UnitNegRange) -> Radians {
    let sin_abs = sin.abs();
    let cos_abs = cos.abs();

    // calculate radians in the range 0.0..=PI/2
    let radians = if cos_abs == sin_abs {
        core::f64::consts::FRAC_PI_4
    } else if sin_abs > cos_abs {
        core::f64::consts::FRAC_PI_2 - arctan2_small_angle(cos_abs, sin_abs).0
    } else {
        arctan2_small_angle(sin_abs, cos_abs).0
    };

    // calculate radians in the range 0.0..=PI
    let positive_radians = if cos.0.is_sign_negative() {
        core::f64::consts::PI - radians
    } else {
        radians
    };

    // return radians in the range -PI..=PI
    Radians(libm::copysign(positive_radians, sin.0))
}

#[must_use]
fn arctan2d_small_positive_angle(sin_abs: UnitNegRange, cos_abs: UnitNegRange) -> Degrees {
    if sin_abs.0 == 0.5 {
        Degrees(30.0)
    } else {
        Degrees(arctan2_small_angle(sin_abs, cos_abs).0.to_degrees())
    }
}

/// Accurately calculate an angle in `Degrees` from its sine and cosine.
/// 
/// * `sin`, `cos` the sine and cosine of the angle in `UnitNegRange`s.
/// 
/// returns the angle in `Degrees`.
#[must_use]
pub fn arctan2d(sin: UnitNegRange, cos: UnitNegRange) -> Degrees {
    let sin_abs = sin.abs();
    let cos_abs = cos.abs();

    // calculate degrees in the range 0.0..=90.0
    let degrees = if cos_abs == sin_abs {
        45.0
    } else if sin_abs > cos_abs {
        90.0 - arctan2d_small_positive_angle(cos_abs, sin_abs).0
    } else {
        arctan2d_small_positive_angle(sin_abs, cos_abs).0
    };

    // calculate degrees in the range 0.0..=180.0
    let positive_degrees = if cos.0.is_sign_negative() {
        180.0 - degrees
    } else {
        degrees
    };

    // return degrees in the range -180.0..=180.0
    Degrees(libm::copysign(positive_degrees, sin.0))
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

        let recip_sq_epsilon = 1.0 / SQ_EPSILON;

        let sin_msq_epsilon = UnitNegRange(-SQ_EPSILON);
        assert_eq!(-recip_sq_epsilon, csc(sin_msq_epsilon).unwrap());
        assert_eq!(-recip_sq_epsilon, sec(sin_msq_epsilon).unwrap());

        let cos_msq_epsilon = swap_sin_cos(sin_msq_epsilon);
        assert_eq!(1.0, sec(cos_msq_epsilon).unwrap());
        assert_eq!(1.0, csc(cos_msq_epsilon).unwrap());

        assert_eq!(-SQ_EPSILON, tan(sin_msq_epsilon, cos_msq_epsilon).unwrap());
        assert_eq!(-recip_sq_epsilon, cot(sin_msq_epsilon, cos_msq_epsilon).unwrap());

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
    fn test_small_angle_conversion() {
        // Test sin(angle) == sin_small_angle(angle) for MAX_LINEAR_SIN_ANGLE
        assert_eq!(
            libm::sin(MAX_LINEAR_SIN_ANGLE.0),
            sin_small_angle(MAX_LINEAR_SIN_ANGLE).0
        );

        // Test cos(angle) == cos_small_angle(angle) for MAX_COS_ANGLE_IS_ONE
        let s = sin_small_angle(MAX_COS_ANGLE_IS_ONE);
        assert_eq!(
            libm::cos(MAX_COS_ANGLE_IS_ONE.0),
            cos_small_angle(MAX_COS_ANGLE_IS_ONE, s).0
        );
        assert_eq!(1.0, libm::cos(MAX_COS_ANGLE_IS_ONE.0));

        // Test max angle where conventional cos(angle) == 1.0
        let angle = Radians(4.74e7 * f64::EPSILON);
        assert_eq!(1.0, libm::cos(angle.0));

        // Note: cos_small_angle(angle) < cos(angle) at the given angle
        // cos(angle) is not accurate for angles close to zero.
        let s = sin_small_angle(angle);
        let result = cos_small_angle(angle, s);
        assert!(result.0 < libm::cos(angle.0));
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
