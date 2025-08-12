// Copyright (c) 2024-2025 Ken Barker

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

//! The `trig` module contains functions for performing accurate trigonometry calculations.
//!
//! The accuracy of the `libm::sin` function is poor for angles >= π/4
//! and the accuracy of the `libm::cos` function is poor for small angles,
//! i.e., < π/4.
//! So `sin` π/4 is explicitly set to 1/√2 and `cos` values are calculated
//! from `sin` values using
//! [Pythagoras' theorem](https://en.wikipedia.org/wiki/Pythagorean_theorem).
//!
//! The `sincos` function accurately calculates the sine and cosine of angles
//! in `radians` by using
//! [remquo](https://pubs.opengroup.org/onlinepubs/9699919799/functions/remquo.html)
//! to reduce an angle into the range: -π/4 <= angle <= π/4;
//! and its quadrant: along the positive or negative, *x* or *y* axis of the
//! unit circle.
//! The `sincos_diff` function reduces the
//! [round-off error](https://en.wikipedia.org/wiki/Round-off_error)
//! of the difference of two angles in radians using the
//! [2Sum](https://en.wikipedia.org/wiki/2Sum) algorithm.
//!
//! The `sincosd` function is the `degrees` equivalent of `sincos` and
//! `sincosd_diff` is the `degrees` equivalent of `sincos_diff`.
//!
//! The sines and cosines of angles are represented by the `UnitNegRange`
//! struct which ensures that they lie in the range:
//! -1.0 <= value <= 1.0.
//!
//! The functions `arctan2` and `arctan2d` are the reciprocal of `sincos` and
//! `sincosd`, transforming sine and cosines of angles into `radians` or
//! `degrees` respectively.
//!
//! The module contains the other trigonometric functions:
//! tan, cot, sec and csc as functions taking sin and/or cos and returning
//! an `Option<f64>` to protect against divide by zero.
//!
//! The module also contains functions for:
//! - [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities);
//! - [half-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae);
//! - and the [spherical law of cosines](https://en.wikipedia.org/wiki/Spherical_law_of_cosines).

#![allow(clippy::float_cmp, clippy::suboptimal_flops)]

use crate::{Degrees, Radians, Validate, two_sum};
use core::cmp::Ordering;
use core::{f64, ops::Neg};

/// ε * ε, a very small number.
pub const SQ_EPSILON: f64 = f64::EPSILON * f64::EPSILON;

/// `core::f64::consts::SQRT_3` is currently a nightly-only experimental API,
/// see <https://doc.rust-lang.org/core/f64/consts/constant.SQRT_3.html>
#[allow(clippy::excessive_precision, clippy::unreadable_literal)]
pub const SQRT_3: f64 = 1.732050807568877293527446341505872367_f64;

/// The cosine of 30 degrees: √3/2
pub const COS_30_DEGREES: f64 = SQRT_3 / 2.0;
/// The maximum angle in Radians where: `libm::sin(value) == value`
pub const MAX_LINEAR_SIN_ANGLE: Radians = Radians(9.67e7 * f64::EPSILON);
/// The maximum angle in Radians where: `swap_sin_cos(libm::sin(value)) == 1.0`
pub const MAX_COS_ANGLE_IS_ONE: Radians = Radians(3.35e7 * f64::EPSILON);

/// Convert an angle in `Degrees` to `Radians`.
///
/// Corrects ±30° to ±π/6.
#[must_use]
fn to_radians(angle: Degrees) -> Radians {
    if angle.0.abs() == 30.0 {
        Radians(libm::copysign(core::f64::consts::FRAC_PI_6, angle.0))
    } else {
        Radians(angle.0.to_radians())
    }
}

/// The `UnitNegRange` newtype an f64.
/// A valid `UnitNegRange` value lies between -1.0 and +1.0 inclusive.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct UnitNegRange(pub f64);

impl Default for UnitNegRange {
    fn default() -> Self {
        Self(0.0)
    }
}

impl UnitNegRange {
    /// Clamp value into the valid range: -1.0 to +1.0 inclusive.
    ///
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
    pub const fn clamp(value: f64) -> Self {
        Self(value.clamp(-1.0, 1.0))
    }

    /// The absolute value of the `UnitNegRange`.
    #[must_use]
    pub const fn abs(self) -> Self {
        Self(self.0.abs())
    }
}

impl Validate for UnitNegRange {
    /// Test whether a `UnitNegRange` is valid.
    ///
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
    ///
    /// Negates the value.
    fn neg(self) -> Self {
        Self(0.0 - self.0)
    }
}

/// Calculate a * a - b * b.
///
/// Note: calculates (a - b) * (a + b) to minimize round-off error.
/// * `a`, `b` the values.
///
/// returns (a - b) * (a + b)
#[must_use]
pub fn sq_a_minus_sq_b(a: UnitNegRange, b: UnitNegRange) -> UnitNegRange {
    UnitNegRange((a.0 - b.0) * (a.0 + b.0))
}

/// Calculate 1 - a * a.
///
/// Note: calculates (1 - a) * (1 + a) to minimize round-off error.
/// * `a` the value.
///
/// returns (1 - a) * (1 + a)
#[must_use]
pub fn one_minus_sq_value(a: UnitNegRange) -> UnitNegRange {
    sq_a_minus_sq_b(UnitNegRange(1.0), a)
}

/// Swap the sine into the cosine of an angle and vice versa.
///
/// Uses the identity sin<sup>2</sup> + cos<sup>2</sup> = 1.
/// See:
/// [Pythagorean identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Pythagorean_identities)
/// * `a` the sine of the angle.
///
/// # Examples
/// ```
/// use angle_sc::trig::{UnitNegRange, swap_sin_cos};
///
/// assert_eq!(UnitNegRange(0.0), swap_sin_cos(UnitNegRange(-1.0)));
/// assert_eq!(UnitNegRange(1.0), swap_sin_cos(UnitNegRange(0.0)));
/// ```
#[must_use]
pub fn swap_sin_cos(a: UnitNegRange) -> UnitNegRange {
    UnitNegRange(libm::sqrt(one_minus_sq_value(a).0))
}

/// Calculate the cosine of an angle from it's sine and the sign of the cosine.
///
/// See: `swap_sin_cos`.
/// * `a` the sine of the angle.
/// * `sign` the sign of the cosine of the angle.
///
/// return the cosine of the Angle.
/// # Examples
/// ```
/// use angle_sc::trig::{UnitNegRange, cosine_from_sine, COS_30_DEGREES};
///
/// assert_eq!(COS_30_DEGREES, cosine_from_sine(UnitNegRange(0.5), 1.0).0);
/// ```
#[must_use]
pub fn cosine_from_sine(a: UnitNegRange, sign: f64) -> UnitNegRange {
    if a.0.abs() > MAX_COS_ANGLE_IS_ONE.0 {
        let b = swap_sin_cos(a);
        if b.0 > 0.0 {
            UnitNegRange(libm::copysign(b.0, sign))
        } else {
            b
        }
    } else {
        UnitNegRange(libm::copysign(1.0, sign))
    }
}

/// Calculate the sine of an angle in `Radians`.
///
/// Corrects sin ±π/4 to ±1/√2.
#[must_use]
pub fn sine(angle: Radians) -> UnitNegRange {
    let angle_abs = angle.0.abs();
    if angle_abs == core::f64::consts::FRAC_PI_4 {
        UnitNegRange(libm::copysign(core::f64::consts::FRAC_1_SQRT_2, angle.0))
    } else if angle_abs > MAX_LINEAR_SIN_ANGLE.0 {
        UnitNegRange(libm::sin(angle.0))
    } else {
        UnitNegRange(angle.0)
    }
}

/// Calculate the cosine of an angle in `Radians` using the sine of the angle.
///
/// Corrects cos π/4 to 1/√2.
#[must_use]
pub fn cosine(angle: Radians, sin: UnitNegRange) -> UnitNegRange {
    let angle_abs = angle.0.abs();
    if angle_abs == core::f64::consts::FRAC_PI_4 {
        UnitNegRange(libm::copysign(
            core::f64::consts::FRAC_1_SQRT_2,
            core::f64::consts::FRAC_PI_2 - angle_abs,
        ))
    } else {
        cosine_from_sine(sin, core::f64::consts::FRAC_PI_2 - angle_abs)
    }
}

/// Assign `sin` and `cos` to the `remquo` quadrant: `q`:
///
/// - 0: no conversion
/// - 1: rotate 90° clockwise
/// - 2: opposite quadrant
/// - 3: rotate 90° counter-clockwise
#[must_use]
fn assign_sin_cos_to_quadrant(
    sin: UnitNegRange,
    cos: UnitNegRange,
    q: i32,
) -> (UnitNegRange, UnitNegRange) {
    match q & 3 {
        1 => (cos, -sin),  // quarter_turn_cw
        2 => (-sin, -cos), // opposite
        3 => (-cos, sin),  // quarter_turn_ccw
        _ => (sin, cos),
    }
}

/// Calculate the sine and cosine of an angle from a value in `Radians`.
///
/// Note: calculates the cosine of the angle from its sine and overrides both
/// the sine and cosine for π/4 to their correct values: 1/√2
///
/// * `radians` the angle in `Radians`
///
/// returns sine and cosine of the angle as `UnitNegRange`s.
#[must_use]
pub fn sincos(radians: Radians) -> (UnitNegRange, UnitNegRange) {
    let rq: (f64, i32) = libm::remquo(radians.0, core::f64::consts::FRAC_PI_2);

    // radians_q is radians in range `-FRAC_PI_4..=FRAC_PI_4`
    let radians_q = Radians(rq.0);
    let sin = sine(radians_q);
    assign_sin_cos_to_quadrant(sin, cosine(radians_q, sin), rq.1)
}

/// Calculate the sine and cosine of an angle from the difference of a pair of
/// values in `Radians`.
///
/// Note: calculates the cosine of the angle from its sine and overrides the
/// sine and cosine for π/4 to their correct values: 1/√2
///
/// * `a`, `b` the angles in `Radians`
///
/// returns sine and cosine of a - b as `UnitNegRange`s.
#[must_use]
pub fn sincos_diff(a: Radians, b: Radians) -> (UnitNegRange, UnitNegRange) {
    let delta = two_sum(a.0, -b.0);
    let rq: (f64, i32) = libm::remquo(delta.0, core::f64::consts::FRAC_PI_2);

    // radians_q is radians in range `-FRAC_PI_4..=FRAC_PI_4`
    let radians_q = Radians(rq.0 + delta.1);
    let sin = sine(radians_q);
    assign_sin_cos_to_quadrant(sin, cosine(radians_q, sin), rq.1)
}

/// Accurately calculate an angle in `Radians` from its sine and cosine.
///
/// * `sin`, `cos` the sine and cosine of the angle in `UnitNegRange`s.
///
/// returns the angle in `Radians`.
///
/// # Panics
///
/// Panics if `sin` or `cos` are `NaN`.
#[must_use]
pub fn arctan2(sin: UnitNegRange, cos: UnitNegRange) -> Radians {
    let sin_abs = sin.0.abs();
    let cos_abs = cos.0.abs();

    // calculate radians in the range 0.0..=PI/2
    let radians_pi_2 = match sin_abs.partial_cmp(&cos_abs).expect("sin or cos is NaN") {
        Ordering::Equal => core::f64::consts::FRAC_PI_4,
        Ordering::Less => libm::atan2(sin_abs, cos_abs),
        Ordering::Greater => core::f64::consts::FRAC_PI_2 - libm::atan2(cos_abs, sin_abs),
    };

    // calculate radians in the range 0.0..=PI
    let radians_pi = if cos.0 < 0.0 {
        core::f64::consts::PI - radians_pi_2
    } else {
        radians_pi_2
    };

    // return radians in the range -π < radians <= π
    Radians(libm::copysign(radians_pi, sin.0))
}

/// Calculate the sine and cosine of an angle from a value in `Degrees`.
///
/// Note: calculates the cosine of the angle from its sine and overrides the
/// sine and cosine for ±30° and ±45° to their correct values.
///
/// * `degrees` the angle in `Degrees`
///
/// returns sine and cosine of the angle as `UnitNegRange`s.
#[must_use]
pub fn sincosd(degrees: Degrees) -> (UnitNegRange, UnitNegRange) {
    let rq: (f64, i32) = libm::remquo(degrees.0, 90.0);

    // radians_q is radians in range `-π/4 <= radians <= π/4`
    let radians_q = to_radians(Degrees(rq.0));
    let sin = sine(radians_q);
    assign_sin_cos_to_quadrant(sin, cosine(radians_q, sin), rq.1)
}

/// Calculate the sine and cosine of an angle from the difference of a pair of
/// values in `Degrees`.
///
/// Note: calculates the cosine of the angle from its sine and overrides the
/// sine and cosine for ±30° and ±45° to their correct values.
///
/// * `a`, `b` the angles in `Degrees`
///
/// returns sine and cosine of a - b as `UnitNegRange`s.
#[must_use]
pub fn sincosd_diff(a: Degrees, b: Degrees) -> (UnitNegRange, UnitNegRange) {
    let delta = two_sum(a.0, -b.0);
    let rq: (f64, i32) = libm::remquo(delta.0, 90.0);

    // radians_q is radians in range `-π/4 <= radians <= π/4`
    let radians_q = to_radians(Degrees(rq.0 + delta.1));
    let sin = sine(radians_q);
    assign_sin_cos_to_quadrant(sin, cosine(radians_q, sin), rq.1)
}

/// Accurately calculate a small an angle in `Degrees` from the its sine and cosine.
///
/// Converts sin of 0.5 to 30°.
#[must_use]
fn arctan2_degrees(sin_abs: f64, cos_abs: f64) -> f64 {
    if sin_abs == 0.5 {
        30.0
    } else {
        libm::atan2(sin_abs, cos_abs).to_degrees()
    }
}

/// Accurately calculate an angle in `Degrees` from its sine and cosine.
///
/// * `sin`, `cos` the sine and cosine of the angle in `UnitNegRange`s.
///
/// returns the angle in `Degrees`.
/// # Panics
///
/// Panics if `sin` or `cos` are `NaN`.
#[must_use]
pub fn arctan2d(sin: UnitNegRange, cos: UnitNegRange) -> Degrees {
    let sin_abs = sin.0.abs();
    let cos_abs = cos.0.abs();

    // calculate degrees in the range 0.0..=90.0
    let degrees_90 = match sin_abs.partial_cmp(&cos_abs).expect("sin or cos is NaN") {
        Ordering::Equal => 45.0,
        Ordering::Less => arctan2_degrees(sin_abs, cos_abs),
        Ordering::Greater => 90.0 - arctan2_degrees(cos_abs, sin_abs),
    };

    // calculate degrees in the range 0° <= degrees <= 180°
    let degrees_180 = if cos.0 < 0.0 {
        180.0 - degrees_90
    } else {
        degrees_90
    };

    // return degrees in the range -180° < degrees <= 180°
    Degrees(libm::copysign(degrees_180, sin.0))
}

/// The cosecant of an angle.
///
/// * `sin` the sine of the angle.
///
/// returns the cosecant or `None` if `sin < SQ_EPSILON`
#[must_use]
pub fn csc(sin: UnitNegRange) -> Option<f64> {
    if sin.0.abs() >= SQ_EPSILON {
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
    if cos.0.abs() >= SQ_EPSILON {
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
    sec(cos).map(|secant| sin.0 * secant)
}

/// The cotangent of an angle.
///
/// * `sin` the sine of the angle.
///
/// returns the cotangent or `None` if `sin < SQ_EPSILON`
#[must_use]
pub fn cot(sin: UnitNegRange, cos: UnitNegRange) -> Option<f64> {
    csc(sin).map(|cosecant| cos.0 * cosecant)
}

/// Calculate the sine of the difference of two angles: a - b.
///
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
///
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
///
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
///
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
///
/// See: [Half-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae)
#[must_use]
pub fn sq_sine_half(cos: UnitNegRange) -> f64 {
    (1.0 - cos.0) * 0.5
}

/// Square of the cosine of half the Angle.
///
/// See: [Half-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae)
#[must_use]
pub fn sq_cosine_half(cos: UnitNegRange) -> f64 {
    (1.0 + cos.0) * 0.5
}

/// Calculates the length of the other side in a right angled triangle,
/// given the length of one side and the hypotenuse.
///
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
///
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
///
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
///
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
        let zero = UnitNegRange::default();
        assert_eq!(UnitNegRange(0.0), zero);
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
        assert_eq!(COS_30_DEGREES, sin_60.0);

        let sin_120 = sin_60;
        let cos_120 = cosine_from_sine(sin_120, -1.0);

        let zero = cosine_from_sine(UnitNegRange(1.0), -1.0);
        assert_eq!(0.0, zero.0);
        assert!(zero.0.is_sign_positive());

        let recip_sq_epsilon = 1.0 / SQ_EPSILON;

        let sin_msq_epsilon = UnitNegRange(-SQ_EPSILON);
        assert_eq!(-recip_sq_epsilon, csc(sin_msq_epsilon).unwrap());
        assert_eq!(-recip_sq_epsilon, sec(sin_msq_epsilon).unwrap());

        let cos_msq_epsilon = swap_sin_cos(sin_msq_epsilon);
        assert_eq!(1.0, sec(cos_msq_epsilon).unwrap());
        assert_eq!(1.0, csc(cos_msq_epsilon).unwrap());

        assert_eq!(-SQ_EPSILON, tan(sin_msq_epsilon, cos_msq_epsilon).unwrap());
        assert_eq!(
            -recip_sq_epsilon,
            cot(sin_msq_epsilon, cos_msq_epsilon).unwrap()
        );

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
        // Test angle == sine(angle) for MAX_LINEAR_SIN_ANGLE
        assert_eq!(MAX_LINEAR_SIN_ANGLE.0, sine(MAX_LINEAR_SIN_ANGLE).0);

        // Test cos(angle) == cosine(angle) for MAX_COS_ANGLE_IS_ONE
        let s = sine(MAX_COS_ANGLE_IS_ONE);
        assert_eq!(
            libm::cos(MAX_COS_ANGLE_IS_ONE.0),
            cosine(MAX_COS_ANGLE_IS_ONE, s).0
        );
        assert_eq!(1.0, libm::cos(MAX_COS_ANGLE_IS_ONE.0));

        // Test max angle where conventional cos(angle) == 1.0
        let angle = Radians(4.74e7 * f64::EPSILON);
        assert_eq!(1.0, libm::cos(angle.0));

        // Note: cosine(angle) < cos(angle) at the given angle
        // cos(angle) is not accurate for angles close to zero.
        let s = sine(angle);
        let result = cosine(angle, s);
        assert_eq!(1.0 - f64::EPSILON / 2.0, result.0);
        assert!(result.0 < libm::cos(angle.0));
    }

    #[test]
    fn test_radians_conversion() {
        // Radians is irrational because PI is an irrational number
        // π/2 != π/3 + π/6
        // assert_eq!(core::f64::consts::FRAC_PI_2, core::f64::consts::FRAC_PI_3 + core::f64::consts::FRAC_PI_6);
        assert!(
            core::f64::consts::FRAC_PI_2
                != core::f64::consts::FRAC_PI_3 + core::f64::consts::FRAC_PI_6
        );

        // π/2 + ε = π/3 + π/6 // error is ε
        assert_eq!(
            core::f64::consts::FRAC_PI_2 + f64::EPSILON,
            core::f64::consts::FRAC_PI_3 + core::f64::consts::FRAC_PI_6
        );

        // π/2 = 2 * π/4
        assert_eq!(
            core::f64::consts::FRAC_PI_2,
            2.0 * core::f64::consts::FRAC_PI_4
        );
        // π = 2 * π/2
        assert_eq!(core::f64::consts::PI, 2.0 * core::f64::consts::FRAC_PI_2);

        // π/4 = 45°
        assert_eq!(core::f64::consts::FRAC_PI_4, 45.0_f64.to_radians());

        // sine π/4 is off by Epsilon / 2
        assert_eq!(
            core::f64::consts::FRAC_1_SQRT_2 - 0.5 * f64::EPSILON,
            libm::sin(core::f64::consts::FRAC_PI_4)
        );

        // -π/6 radians round trip
        let result = sincos(Radians(-core::f64::consts::FRAC_PI_6));
        assert_eq!(-0.5, result.0.0);
        assert_eq!(COS_30_DEGREES, result.1.0);
        assert_eq!(-core::f64::consts::FRAC_PI_6, arctan2(result.0, result.1).0);

        // π/3 radians round trip
        let result = sincos(Radians(core::f64::consts::FRAC_PI_3));
        // Not exactly correct because PI is an irrational number
        // assert_eq!(COS_30_DEGREES, result.0.0);
        assert!(is_within_tolerance(
            COS_30_DEGREES,
            result.0.0,
            f64::EPSILON
        ));
        // assert_eq!(0.5, result.1.0);
        assert!(is_within_tolerance(0.5, result.1.0, f64::EPSILON));
        assert_eq!(core::f64::consts::FRAC_PI_3, arctan2(result.0, result.1).0);

        // -π radians round trip to +π radians
        let result = sincos(Radians(-core::f64::consts::PI));
        assert_eq!(0.0, result.0.0);
        assert_eq!(-1.0, result.1.0);
        assert_eq!(core::f64::consts::PI, arctan2(result.0, result.1).0);

        // π - π/4 radians round trip
        let result = sincos_diff(
            Radians(core::f64::consts::PI),
            Radians(core::f64::consts::FRAC_PI_4),
        );
        assert_eq!(core::f64::consts::FRAC_1_SQRT_2, result.0.0);
        assert_eq!(-core::f64::consts::FRAC_1_SQRT_2, result.1.0);
        assert_eq!(
            core::f64::consts::PI - core::f64::consts::FRAC_PI_4,
            arctan2(result.0, result.1).0
        );

        // 6*π - π/3 radians round trip
        let result = sincos_diff(
            Radians(3.0 * core::f64::consts::TAU),
            Radians(core::f64::consts::FRAC_PI_3),
        );
        // Not exactly correct because π is an irrational number
        // assert_eq!(-COS_30_DEGREES, result.0.0);
        assert!(is_within_tolerance(
            -COS_30_DEGREES,
            result.0.0,
            f64::EPSILON
        ));
        // assert_eq!(0.5, result.1.0);
        assert!(is_within_tolerance(0.5, result.1.0, f64::EPSILON));
        assert_eq!(-core::f64::consts::FRAC_PI_3, arctan2(result.0, result.1).0);
    }

    #[test]
    fn test_degrees_conversion() {
        // Degrees is rational
        assert_eq!(90.0, 60.0 + 30.0);
        assert_eq!(90.0, 2.0 * 45.0);
        assert_eq!(180.0, 2.0 * 90.0);

        // -30 degrees round trip
        let result = sincosd(Degrees(-30.0));
        assert_eq!(-0.5, result.0.0);
        assert_eq!(COS_30_DEGREES, result.1.0);
        assert_eq!(-30.0, arctan2d(result.0, result.1).0);

        // 60 degrees round trip
        let result = sincosd(Degrees(60.0));
        assert_eq!(COS_30_DEGREES, result.0.0);
        assert_eq!(0.5, result.1.0);
        assert_eq!(60.0, arctan2d(result.0, result.1).0);

        // -180 degrees round trip to +180 degrees
        let result = sincosd(Degrees(-180.0));
        assert_eq!(0.0, result.0.0);
        assert_eq!(-1.0, result.1.0);
        assert_eq!(180.0, arctan2d(result.0, result.1).0);

        // 180 - 45 degrees round trip
        let result = sincosd_diff(Degrees(180.0), Degrees(45.0));
        assert_eq!(core::f64::consts::FRAC_1_SQRT_2, result.0.0);
        assert_eq!(-core::f64::consts::FRAC_1_SQRT_2, result.1.0);
        assert_eq!(180.0 - 45.0, arctan2d(result.0, result.1).0);

        // 1080 - 60 degrees round trip
        let result = sincosd_diff(Degrees(1080.0), Degrees(60.0));
        assert_eq!(-COS_30_DEGREES, result.0.0);
        assert_eq!(0.5, result.1.0);
        assert_eq!(-60.0, arctan2d(result.0, result.1).0);
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
