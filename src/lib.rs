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

//! [![crates.io](https://img.shields.io/crates/v/angle-sc.svg)](https://crates.io/crates/angle-sc)
//! [![docs.io](https://docs.rs/angle-sc/badge.svg)](https://docs.rs/angle-sc/)
//! [![License](https://img.shields.io/badge/License-MIT-blue)](https://opensource.org/license/mit/)
//! [![Rust](https://github.com/kenba/angle-sc-rs/actions/workflows/rust.yml/badge.svg)](https://github.com/kenba/angle-sc-rs/actions)
//! [![codecov](https://codecov.io/gh/kenba/angle-sc-rs/graph/badge.svg?token=6DTOY9Y4BT)](https://codecov.io/gh/kenba/angle-sc-rs)
//!
//! An angle represented by its sine and cosine.
//!
//! The cosine and sine of angle *θ* can be viewed as *x* and *y* coordinates with
//!  *θ* measured anti-clockwise from the *x* axis.  
//!  They form a [unit circle](https://en.wikipedia.org/wiki/Unit_circle), see *Figure 1*.
//!
//! ![Unit circle](https://upload.wikimedia.org/wikipedia/commons/thumb/7/72/Sinus_und_Kosinus_am_Einheitskreis_1.svg/250px-Sinus_und_Kosinus_am_Einheitskreis_1.svg.png)  
//! *Figure 1 Unit circle formed by sin *θ* and cos *θ**
//!
//! The `Angle` on the `opposite` side of the unit circle is calculated by simply
//! negating the sin and cos of `Angle`.  
//! `Angle` addition and subtraction are performed using
//! [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).  
//! `Angle` `double` uses the [double-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Double-angle_formulae)
//! and `half` uses the
//! [half-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae).  
//! The `Angle` `<` operator compares whether an `Angle` is clockwise of the other
//! `Angle` on the unit circle.
//!
//! The `sin` and `cos` fields of `Angle` are `UnitNegRange`s:,
//! a [newtype](https://rust-unofficial.github.io/patterns/patterns/behavioural/newtype.html)
//! with values in the range -1.0 to +1.0 inclusive.  
//! The `Degrees` and `Radians` newtypes are used to convert to and from `Angle`s.  
//! The `Validate` trait is used to check that `Angle`s and `UnitNegRange`s are valid.
//!
//! The library is declared [no_std](https://docs.rust-embedded.org/book/intro/no-std.html)
//! so it can be used in embedded applications.

#![cfg_attr(not(test), no_std)]
#![allow(clippy::float_cmp)]

pub mod trig;
use core::cmp::{Ordering, PartialOrd};
use core::convert::From;
use core::ops::{Add, Neg, Sub};
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// The Degrees newtype an f64.
#[derive(Clone, Copy, Debug, PartialEq, Serialize, Deserialize)]
pub struct Degrees(pub f64);

impl Degrees {
    /// Normalise a Degrees into the range:
    /// -180 < value <= 180
    /// # Examples
    /// ```
    /// use angle_sc::Degrees;
    ///
    /// assert_eq!(0.0, Degrees(-360.0).normalise().0);
    /// assert_eq!(180.0, Degrees(-180.0).normalise().0);
    /// assert_eq!(180.0, Degrees(180.0).normalise().0);
    /// assert_eq!(0.0, Degrees(360.0).normalise().0);
    /// ```
    #[must_use]
    pub fn normalise(&self) -> Self {
        if self.0 <= -180.0 {
            Self(self.0 + 360.0)
        } else if self.0 <= 180.0 {
            *self
        } else {
            Self(self.0 - 360.0)
        }
    }
}

impl Neg for Degrees {
    type Output = Self;

    /// An implementation of Neg for Degrees, i.e. -angle.
    /// # Examples
    /// ```
    /// use angle_sc::Degrees;
    ///
    /// let angle_45 = Degrees(45.0);
    /// let result_m45 = -angle_45;
    /// assert_eq!(-45.0, result_m45.0);
    /// ```
    #[must_use]
    fn neg(self) -> Self {
        Self(0.0 - self.0)
    }
}

impl Add for Degrees {
    type Output = Self;

    /// Add a pair of angles in Degrees, wraps around +/-180.
    /// # Examples
    /// ```
    /// use angle_sc::{Degrees};
    ///
    /// let angle_120 = Degrees(120.0);
    /// let result = angle_120 + angle_120;
    /// assert_eq!(-angle_120, result);
    /// ```
    #[must_use]
    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0).normalise()
    }
}

impl Sub for Degrees {
    type Output = Self;

    /// Subtract a pair of angles in Degrees, wraps around +/-180.
    /// # Examples
    /// ```
    /// use angle_sc::{Degrees};
    ///
    /// let angle_120 = Degrees(120.0);
    /// let result = -angle_120 - angle_120;
    /// assert_eq!(angle_120, result);
    /// ```
    #[must_use]
    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0).normalise()
    }
}

/// The Radians newtype an f64.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct Radians(pub f64);

impl Radians {
    /// Normalise a Radians into the range:
    /// -`PI` < value <= `PI`
    /// # Examples
    /// ```
    /// use angle_sc::Radians;
    ///
    /// assert_eq!(0.0, Radians(-core::f64::consts::TAU).normalise().0);
    /// assert_eq!(core::f64::consts::PI, Radians(-core::f64::consts::PI).normalise().0);
    /// assert_eq!(core::f64::consts::PI, Radians(core::f64::consts::PI).normalise().0);
    /// assert_eq!(0.0, Radians(core::f64::consts::TAU).normalise().0);
    /// ```
    #[must_use]
    pub fn normalise(&self) -> Self {
        if self.0 <= -core::f64::consts::PI {
            Self(self.0 + core::f64::consts::TAU)
        } else if self.0 <= core::f64::consts::PI {
            *self
        } else {
            Self(self.0 - core::f64::consts::TAU)
        }
    }
}

impl Neg for Radians {
    type Output = Self;

    /// An implementation of Neg for Radians, i.e. -angle.
    /// # Examples
    /// ```
    /// use angle_sc::Radians;
    ///
    /// let angle_45 = Radians(core::f64::consts::FRAC_PI_4);
    /// let result_m45 = -angle_45;
    /// assert_eq!(-core::f64::consts::FRAC_PI_4, result_m45.0);
    /// ```
    #[must_use]
    fn neg(self) -> Self {
        Self(0.0 - self.0)
    }
}

impl Add for Radians {
    type Output = Self;

    /// Add a pair of angles in Radians, wraps around +/-PI.
    /// # Examples
    /// ```
    /// use angle_sc::{Radians, is_within_tolerance};
    ///
    /// let angle_120 = Radians(2.0 * core::f64::consts::FRAC_PI_3);
    /// let result = angle_120 + angle_120;
    /// assert!(is_within_tolerance(-2.0 * core::f64::consts::FRAC_PI_3, result.0,  4.0 * core::f64::EPSILON));
    /// ```
    #[must_use]
    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0).normalise()
    }
}

impl Sub for Radians {
    type Output = Self;

    /// Subtract a pair of angles in Radians,  wraps around +/-PI.
    /// # Examples
    /// ```
    /// use angle_sc::{Radians, is_within_tolerance};
    ///
    /// let angle_120 = Radians(2.0 * core::f64::consts::FRAC_PI_3);
    /// let angle_m120 = -angle_120;
    /// let result = angle_m120 - angle_120;
    /// assert!(is_within_tolerance(angle_120.0, result.0,  4.0 * core::f64::EPSILON));
    /// ```
    #[must_use]
    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0).normalise()
    }
}

impl From<Radians> for Degrees {
    /// Create an angle in Degrees from an angle in Radians.
    /// # Examples
    /// ```
    /// use angle_sc::{Degrees, Radians};
    ///
    /// let arg = Radians(core::f64::consts::FRAC_PI_2);
    /// let answer = Degrees::from(arg);
    /// assert_eq!(90.0, answer.0);
    /// ```
    #[must_use]
    fn from(a: Radians) -> Self {
        Self(a.0.to_degrees())
    }
}

/// An angle represented by it's sine and cosine as `UnitNegRanges`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Angle {
    /// The sine of the angle.
    sin: trig::UnitNegRange,
    /// The cosine of the angle.
    cos: trig::UnitNegRange,
}

/// A default angle: zero degrees or radians.
impl Default for Angle {
    /// Implementation of Default for Angle returns Angle(0.0, 1.0),
    /// i.e. the Angle corresponding to zero degrees or radians.
    /// # Examples
    /// ```
    /// use angle_sc::Angle;
    ///
    /// let zero = Angle::default();
    /// assert_eq!(0.0, zero.sin().0);
    /// assert_eq!(1.0, zero.cos().0);
    /// ```
    #[must_use]
    fn default() -> Self {
        Self {
            sin: trig::UnitNegRange(0.0),
            cos: trig::UnitNegRange(1.0),
        }
    }
}

impl Validate for Angle {
    /// Test whether an `Angle` is valid, i.e. both sin and cos are valid
    /// `UnitNegRange`s and the length of their hypotenuse is approximately 1.0.
    fn is_valid(&self) -> bool {
        self.sin.is_valid()
            && self.cos.is_valid()
            && is_within_tolerance(1.0, libm::hypot(self.sin.0, self.cos.0), core::f64::EPSILON)
    }
}

impl Angle {
    /// Construct an Angle from sin and cos values.  
    #[must_use]
    pub const fn new(sin: trig::UnitNegRange, cos: trig::UnitNegRange) -> Self {
        Self { sin, cos }
    }

    /// Construct an Angle from y and x values.  
    /// Normalises the values.
    #[must_use]
    pub fn from_y_x(y: f64, x: f64) -> Self {
        let length = libm::hypot(y, x);

        if is_small(length, core::f64::EPSILON) {
            Self::default()
        } else {
            Self::new(
                trig::UnitNegRange::clamp(y / length),
                trig::UnitNegRange::clamp(x / length),
            )
        }
    }

    /// The sine of the Angle.
    #[must_use]
    pub const fn sin(self) -> trig::UnitNegRange {
        self.sin
    }

    /// The cosine of the Angle.
    #[must_use]
    pub const fn cos(self) -> trig::UnitNegRange {
        self.cos
    }

    /// The absolute value of the angle, i.e. the angle with a positive sine.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_m45 = Angle::from(Degrees(-45.0));
    /// let result_45 = angle_m45.abs();
    /// assert_eq!(Degrees(45.0), Degrees::from(result_45));
    /// ```
    #[must_use]
    pub fn abs(self) -> Self {
        Self {
            sin: trig::UnitNegRange(libm::fabs(self.sin.0)),
            cos: self.cos,
        }
    }

    /// The opposite angle on the circle, i.e. +/- 180 degrees.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_m30 = Angle::from(Degrees(-30.0));
    /// let result = angle_m30.opposite();
    /// assert_eq!(Degrees(150.0), Degrees::from(result));
    /// ```
    #[must_use]
    pub fn opposite(self) -> Self {
        Self {
            sin: -self.sin,
            cos: -self.cos,
        }
    }

    /// A quarter turn clockwise around the circle, i.e. + 90 degrees.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_m30 = Angle::from(Degrees(-30.0));
    /// let result = angle_m30.quarter_turn_cw();
    /// assert_eq!(Angle::from(Degrees(60.0)), result);
    /// ```
    #[must_use]
    pub fn quarter_turn_cw(self) -> Self {
        Self {
            sin: self.cos,
            cos: -self.sin,
        }
    }

    /// A quarter turn counter clockwise around the circle, i.e. - 90 degrees.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_120 = Angle::from(Degrees(120.0));
    /// let result = angle_120.quarter_turn_ccw();
    /// assert_eq!(Angle::from(Degrees(30.0)), result);
    /// ```
    #[must_use]
    pub fn quarter_turn_ccw(self) -> Self {
        Self {
            sin: -self.cos,
            cos: self.sin,
        }
    }

    /// Negate the cosine of the Angle.
    /// I.e. `PI` - `angle.radians()` for positive angles,
    ///      `angle.radians()` + `PI` for negative angles
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_45 = Angle::from(Degrees(45.0));
    /// let result_45 = angle_45.negate_cos();
    /// assert_eq!(Degrees(135.0), Degrees::from(result_45));
    /// ```
    #[must_use]
    pub fn negate_cos(self) -> Self {
        Self {
            sin: self.sin,
            cos: -self.cos,
        }
    }

    /// Double the Angle.
    /// See: [Double-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Double-angle_formulae)
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_30 = Angle::from(Degrees(30.0));
    /// let result_60 = angle_30.double();
    ///
    /// // Note: multiplication is not precise...
    /// // assert_eq!(Degrees(60.0), Degrees::from(result_60));
    /// let delta_angle = libm::fabs(60.0 - Degrees::from(result_60).0);
    /// assert!(delta_angle <= 32.0 * std::f64::EPSILON);
    /// ```
    #[must_use]
    pub fn double(self) -> Self {
        Self {
            sin: trig::UnitNegRange::clamp(2.0 * self.sin.0 * self.cos.0),
            cos: trig::UnitNegRange::clamp((self.cos.0 - self.sin.0) * (self.cos.0 + self.sin.0)),
        }
    }

    /// Half the Angle.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_30 = Angle::from(Degrees(30.0));
    /// let angle_60 = Angle::from(Degrees(60.0));
    ///
    /// assert_eq!(angle_30, angle_60.half());
    /// ```
    #[must_use]
    pub fn half(self) -> Self {
        Self {
            sin: trig::UnitNegRange(libm::copysign(
                libm::sqrt(trig::sq_sine_half(self.cos)),
                self.sin.0,
            )),
            cos: trig::UnitNegRange(libm::sqrt(trig::sq_cosine_half(self.cos))),
        }
    }
}

impl Neg for Angle {
    type Output = Self;

    /// An implementation of Neg for Angle, i.e. -angle.  
    /// Negates the sine of the Angle, does not affect the cosine.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_45 = Angle::from(Degrees(45.0));
    /// let result_m45 = -angle_45;
    /// assert_eq!(Degrees(-45.0), Degrees::from(result_m45));
    /// ```
    #[must_use]
    fn neg(self) -> Self {
        Self {
            sin: -self.sin,
            cos: self.cos,
        }
    }
}

impl Add for Angle {
    type Output = Self;

    /// Add two Angles, i.e. a + b  
    /// Uses trigonometric identity functions, see:
    /// [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).  
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_30 = Angle::from(Degrees(30.0));
    /// let angle_60 = Angle::from(Degrees(60.0));
    /// let result_90 = angle_30 + angle_60;
    /// assert_eq!(Degrees(90.0), Degrees::from(result_90));
    /// ```
    #[must_use]
    fn add(self, other: Self) -> Self {
        Self {
            sin: trig::sine_sum(self.sin, self.cos, other.sin, other.cos),
            cos: trig::cosine_sum(self.sin, self.cos, other.sin, other.cos),
        }
    }
}

impl Sub for Angle {
    type Output = Self;

    /// Subtract two Angles, i.e. a - b  
    /// Uses trigonometric identity functions, see:
    /// [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).  
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees, is_within_tolerance};
    ///
    /// let angle_30 = Angle::from(Degrees(30.0));
    /// let angle_60 = Angle::from(Degrees(60.0));
    /// let result_30 = angle_60 - angle_30;
    ///
    /// assert!(is_within_tolerance(Degrees(30.0).0, Degrees::from(result_30).0, 32.0 * std::f64::EPSILON));
    /// ```
    #[must_use]
    fn sub(self, other: Self) -> Self {
        Self {
            sin: trig::sine_diff(self.sin, self.cos, other.sin, other.cos),
            cos: trig::cosine_diff(self.sin, self.cos, other.sin, other.cos),
        }
    }
}

impl PartialOrd for Angle {
    /// Compare two Angles, i.e. a < b.  
    /// It compares whether an `Angle` is clockwise of the other `Angle` on the
    /// unit circle.  
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    /// let degrees_120 = Angle::from(Degrees(120.0));
    /// let degrees_m120 = -degrees_120;
    /// assert!(degrees_120 < degrees_m120);
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let delta = *other - *self;
        trig::UnitNegRange(0.0).partial_cmp(&delta.sin)
    }
}

impl From<Degrees> for Angle {
    /// Construct an Angle from an angle in Degrees.  
    /// In order to minimize round-off errors, this function calculates sines
    /// of angles with sine values <= 1 / sqrt(2): see
    /// <https://stackoverflow.com/questions/31502120/sin-and-cos-give-unexpected-results-for-well-known-angles>  
    /// It is based on
    /// [GeographicLib::Math::sincosd](https://github.com/geographiclib/geographiclib/blob/1b0be832df51665ebe943f6d4d72eabc0de1bb92/src/Math.cpp#L106) function.
    #[must_use]
    fn from(a: Degrees) -> Self {
        let rq = libm::remquo(a.0, 90.0);

        // Default is zero degrees.
        let mut sin = trig::UnitNegRange(0.0);
        let mut cos = trig::UnitNegRange(1.0);
        let abs_angle = libm::fabs(rq.0);
        if abs_angle > 0.0 {
            // 45 degrees is a special case
            if abs_angle == 45.0 {
                cos = trig::UnitNegRange(core::f64::consts::FRAC_1_SQRT_2);
                sin = trig::UnitNegRange(libm::copysign(cos.0, rq.0));
            } else {
                // 30 degrees is also a special case
                sin = trig::UnitNegRange(if abs_angle == 30.0 {
                    libm::copysign(0.5, rq.0)
                } else {
                    libm::sin(rq.0.to_radians())
                });
                cos = trig::swap_sin_cos(sin);
            }
        }

        match rq.1 & 3 {
            0 => Self { sin, cos },
            1 => Self {
                sin: cos,
                cos: -sin,
            },
            2 => Self {
                sin: -sin,
                cos: -cos,
            },
            _ => Self {
                sin: -cos,
                cos: sin,
            },
        }
    }
}

impl From<Radians> for Angle {
    /// Construct an Angle from an angle in Radians.  
    /// In order to minimize round-off errors, this function calculates sines
    /// of angles with sine values <= 1 / sqrt(2)
    #[must_use]
    fn from(a: Radians) -> Self {
        const FRAC_3_PI_4: f64 = core::f64::consts::PI - core::f64::consts::FRAC_PI_4;

        let valid_angle = a.normalise();
        let abs_angle = libm::fabs(valid_angle.0);

        let over_45_degrees = core::f64::consts::FRAC_PI_4 < abs_angle;
        let under_135_degrees = abs_angle < FRAC_3_PI_4;
        if over_45_degrees && under_135_degrees {
            let cos = trig::UnitNegRange(libm::sin(core::f64::consts::FRAC_PI_2 - abs_angle));
            let sin = trig::cosine_from_sine(trig::UnitNegRange(cos.0), valid_angle.0);

            Self { sin, cos }
        } else {
            let sin = trig::UnitNegRange(libm::sin(valid_angle.0));
            let cos = trig::cosine_from_sine(
                trig::UnitNegRange(sin.0),
                core::f64::consts::FRAC_PI_2 - abs_angle,
            );

            Self { sin, cos }
        }
    }
}

impl From<Angle> for Radians {
    /// Convert an Angle to Radians.
    #[must_use]
    fn from(a: Angle) -> Self {
        Self(libm::atan2(a.sin.0, a.cos.0))
    }
}

impl From<Angle> for Degrees {
    /// Convert an Angle to Degrees.
    #[must_use]
    fn from(a: Angle) -> Self {
        Self::from(Radians::from(a))
    }
}

impl Serialize for Angle {
    /// Serialize an Angle to an value in Degrees.
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_newtype_struct("Degrees", &Degrees::from(*self))
    }
}

impl<'de> Deserialize<'de> for Angle {
    /// Deserialize an value in Degrees to an Angle.
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(Self::from(Degrees::deserialize(deserializer)?))
    }
}

//////////////////////////////////////////////////////////////////////////////

/// Return the minimum of a or b.
#[must_use]
pub fn min<T>(a: T, b: T) -> T
where
    T: PartialOrd + Copy,
{
    if b < a {
        b
    } else {
        a
    }
}

/// Return the maximum of a or b.
#[must_use]
pub fn max<T>(a: T, b: T) -> T
where
    T: PartialOrd + Copy,
{
    if b < a {
        a
    } else {
        b
    }
}

/// Clamp a value to lie in the range min, max inclusive.
#[must_use]
pub fn clamp<T>(value: T, min: T, max: T) -> T
where
    T: PartialOrd + Copy,
{
    if value < min {
        min
    } else if max < value {
        max
    } else {
        value
    }
}

/// The Validate trait.
pub trait Validate {
    /// return true if the type is valid, false otherwise.
    fn is_valid(&self) -> bool;
}

/// Check whether value <= tolerance.
#[must_use]
pub fn is_small<T>(value: T, tolerance: T) -> bool
where
    T: PartialOrd + Copy,
{
    value <= tolerance
}

/// Check whether a value is within tolerance of a reference value.
/// * `reference` the required value
/// * `value` the value to test
/// * `tolerance` the permitted tolerance
/// return true if abs(reference - value) is <= tolerance
#[must_use]
pub fn is_within_tolerance<T>(reference: T, value: T, tolerance: T) -> bool
where
    T: PartialOrd + Copy + Sub<Output = T>,
{
    let delta = max(reference, value) - min(reference, value);
    is_small(delta, tolerance)
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::f64::consts::{FRAC_1_SQRT_2, FRAC_PI_3, FRAC_PI_6, TAU};
    use core::f64::EPSILON;

    #[test]
    fn degrees_traits() {
        let one = Degrees(1.0);
        let two = Degrees(2.0);

        let one_clone = one.clone();
        assert!(one_clone == one);

        let m_two = -two;
        assert_eq!(-2.0, m_two.0);

        let m_one = one + m_two;
        assert_eq!(-1.0, m_one.0);

        let d_120 = Degrees(120.0);
        let d_m120 = Degrees(-120.0);

        assert_eq!(d_m120, d_120 + d_120);
        assert_eq!(d_120, d_m120 + d_m120);
        assert_eq!(d_120, d_m120 - d_120);

        let serialized = serde_json::to_string(&one).unwrap();
        let deserialized: Degrees = serde_json::from_str(&serialized).unwrap();
        assert_eq!(one, deserialized);

        let bad_text = "junk";
        let _serde_error = serde_json::from_str::<Degrees>(&bad_text).unwrap_err();

        print!("Degrees: {:?}", one);
    }

    #[test]
    fn test_convert_degrees() {
        let arg = Radians(core::f64::consts::FRAC_PI_2);
        let result = Degrees::from(arg);

        assert_eq!(90.0, result.0);
    }

    #[test]
    fn radians_traits() {
        let one = Radians(1.0);
        let two = Radians(2.0);
        assert!(one < two);

        let one_clone = one.clone();
        assert!(one_clone == one);

        let m_two = -two;
        assert_eq!(-2.0, m_two.0);

        let m_one = one + m_two;
        assert_eq!(-1.0, m_one.0);

        let result_1 = m_two - two;
        assert_eq!(TAU - 4.0, result_1.0);

        let result_2 = two - m_two;
        assert_eq!(4.0 - TAU, result_2.0);

        print!("Radians: {:?}", one);
    }

    #[test]
    fn angle_traits() {
        let zero = Angle::default();
        assert_eq!(0.0, zero.sin().0);
        assert_eq!(1.0, zero.cos().0);
        assert!(zero.is_valid());

        let zero_clone = zero.clone();
        assert_eq!(zero, zero_clone);

        let degrees_m45 = Angle::from_y_x(-EPSILON, EPSILON);
        assert!(degrees_m45.is_valid());
        assert!(is_within_tolerance(
            -FRAC_1_SQRT_2,
            degrees_m45.sin().0,
            EPSILON
        ));
        assert!(is_within_tolerance(
            FRAC_1_SQRT_2,
            degrees_m45.cos().0,
            EPSILON
        ));

        assert!(degrees_m45 < zero);

        let too_small = Angle::from_y_x(-EPSILON / 2.0, EPSILON / 2.0);
        assert!(too_small.is_valid());
        assert_eq!(zero, too_small);

        let degrees_30 = Angle::from(Radians(FRAC_PI_6));
        assert!(degrees_30.is_valid());
        assert!(is_within_tolerance(0.5, degrees_30.sin().0, EPSILON));
        assert!(is_within_tolerance(
            0.8660254037844386,
            degrees_30.cos().0,
            EPSILON
        ));

        let degrees_60 = Angle::from(Radians(FRAC_PI_3));
        assert!(degrees_60.is_valid());
        assert!(is_within_tolerance(
            0.8660254037844386,
            degrees_60.sin().0,
            EPSILON
        ));
        assert!(is_within_tolerance(0.5, degrees_60.cos().0, EPSILON));

        let degrees_45 = Angle::from(Degrees(45.0));
        assert!(degrees_45.is_valid());
        assert_eq!(FRAC_1_SQRT_2, degrees_45.sin().0);
        assert_eq!(FRAC_1_SQRT_2, degrees_45.cos().0);

        let degrees_m120 = Angle::from(Degrees(-120.0));
        assert!(degrees_m120.is_valid());
        assert!(is_within_tolerance(
            -0.8660254037844386,
            degrees_m120.sin().0,
            EPSILON
        ));
        assert!(is_within_tolerance(-0.5, degrees_m120.cos().0, EPSILON));

        let degrees_m140 = Angle::from(Degrees(-140.0));
        assert!(degrees_m140.is_valid());
        assert!(is_within_tolerance(
            -0.6427876096865393,
            degrees_m140.sin().0,
            EPSILON
        ));
        assert!(is_within_tolerance(
            -0.7660444431189781,
            degrees_m140.cos().0,
            EPSILON
        ));

        let serialized = serde_json::to_string(&zero).unwrap();
        let deserialized: Angle = serde_json::from_str(&serialized).unwrap();
        assert_eq!(zero, deserialized);

        let bad_text = "junk";
        let _serde_error = serde_json::from_str::<Angle>(&bad_text).unwrap_err();

        print!("Angle: {:?}", degrees_m45);
    }

    #[test]
    fn angle_maths() {
        let degrees_30 = Angle::from(Degrees(30.0));
        let degrees_60 = Angle::from(Degrees(60.0));
        let degrees_120 = Angle::from(Degrees(120.0));
        let degrees_m120 = -degrees_120;

        assert!(degrees_120 < degrees_m120);
        assert_eq!(degrees_120, degrees_m120.abs());
        assert_eq!(degrees_60, degrees_m120.opposite());
        assert_eq!(degrees_120, degrees_30.quarter_turn_cw());
        assert_eq!(degrees_30, degrees_120.quarter_turn_ccw());
        assert_eq!(degrees_60, degrees_120.negate_cos());

        let result = degrees_m120 - degrees_120;
        assert!(is_within_tolerance(
            Degrees(120.0).0,
            Degrees::from(result).0,
            120.0 * EPSILON
        ));

        let result = degrees_120 + degrees_120;
        assert!(is_within_tolerance(
            Degrees(-120.0).0,
            Degrees::from(result).0,
            120.0 * EPSILON
        ));

        let result = degrees_60.double();
        assert!(is_within_tolerance(
            Degrees(120.0).0,
            Degrees::from(result).0,
            120.0 * EPSILON
        ));

        let result = degrees_120.double();
        assert!(is_within_tolerance(
            Degrees(-120.0).0,
            Degrees::from(result).0,
            120.0 * EPSILON
        ));

        assert_eq!(-degrees_60, degrees_m120.half());
    }

    #[test]
    fn test_min_and_max() {
        // min -ve and +ve
        assert_eq!(min(-1.0 + EPSILON, -1.0), -1.0);
        assert_eq!(min(1.0, 1.0 + EPSILON), 1.0);
        // max -ve and +ve
        assert_eq!(max(-1.0, -1.0 - EPSILON), -1.0);
        assert_eq!(max(1.0 - EPSILON, 1.0), 1.0);
    }

    #[test]
    fn test_clamp() {
        // value < min
        assert_eq!(clamp(-1.0 - EPSILON, -1.0, 1.0), -1.0);
        // value = min
        assert_eq!(clamp(-1.0, -1.0, 1.0), -1.0);
        // value = max
        assert_eq!(clamp(1.0, -1.0, 1.0), 1.0);
        // value > max
        assert_eq!(clamp(1.0 + EPSILON, -1.0, 1.0), 1.0);
    }

    #[test]
    fn test_is_within_tolerance() {
        // below minimum tolerance
        assert_eq!(
            false,
            is_within_tolerance(1.0 - 2.0 * EPSILON, 1.0, EPSILON)
        );

        // within minimum tolerance
        assert!(is_within_tolerance(1.0 - EPSILON, 1.0, EPSILON));

        // within maximum tolerance
        assert!(is_within_tolerance(1.0 + EPSILON, 1.0, EPSILON));

        // above maximum tolerance
        assert_eq!(
            false,
            is_within_tolerance(1.0 + 2.0 * EPSILON, 1.0, EPSILON)
        );
    }
}
