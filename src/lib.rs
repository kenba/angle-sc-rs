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
use num_traits::{Num, NumCast};
use serde::{Deserialize, Serialize};

/// The Degrees newtype.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Degrees<T>(pub T);

impl<T: Num + Copy> Degrees<T> {
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
    pub fn normalise(&self) -> Self
    where
        T: NumCast + Copy,
    {
        let value: f64 = num_traits::cast(self.0).unwrap();
        let value = if value <= -180.0 {
            value + 360.0
        } else if value > 180.0 {
            value - 360.0
        } else {
            value
        };

        Self(num_traits::cast(value).unwrap())
    }
}

impl<T: Num + NumCast + Copy> Neg for Degrees<T> {
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
        let zero: T = num_traits::cast(0).unwrap();
        Self(zero - self.0)
    }
}

impl<T: Num + NumCast + Copy> Add for Degrees<T> {
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

impl<T: Num + NumCast + Copy> Sub for Degrees<T> {
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
        self + -other
    }
}

/// The Radians newtype.
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd)]
pub struct Radians<T>(pub T);

impl<T: Num> Radians<T> {
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
    pub fn normalise(&self) -> Self
    where
        T: NumCast + Copy,
    {
        let value: f64 = num_traits::cast(self.0).unwrap();
        let value = if value <= -core::f64::consts::PI {
            value + core::f64::consts::TAU
        } else if value > core::f64::consts::PI {
            value - core::f64::consts::TAU
        } else {
            value
        };

        Self(num_traits::cast(value).unwrap())
    }
}

impl<T: Num + NumCast + Copy> Neg for Radians<T> {
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
        let zero: T = num_traits::cast(0).unwrap();
        Self(zero - self.0)
    }
}

impl<T: Num + NumCast + Copy> Add for Radians<T> {
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

impl<T: Num + NumCast + Copy> Sub for Radians<T> {
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
        self + -other
    }
}

impl<T: Num + NumCast + Copy> From<Radians<T>> for Degrees<T> {
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
    fn from(a: Radians<T>) -> Self
    where
        T: NumCast + Copy,
    {
        let value: f64 = num_traits::cast(a.0).unwrap();
        Self(num_traits::cast(value.to_degrees()).unwrap())
    }
}

/// An angle represented by it's sine and cosine as `UnitNegRanges`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Angle<T> {
    /// The sine of the angle.
    sin: trig::UnitNegRange<T>,
    /// The cosine of the angle.
    cos: trig::UnitNegRange<T>,
}

/// A default angle: zero degrees or radians.
impl<T: Num + NumCast> Default for Angle<T> {
    /// Implementation of Default for Angle returns Angle(0.0, 1.0),
    /// i.e. the Angle corresponding to zero degrees or radians.
    /// # Examples
    /// ```
    /// use angle_sc::Angle;
    ///
    /// let zero: Angle<f64> = Angle::default();
    /// assert_eq!(0.0, zero.sin().0);
    /// assert_eq!(1.0, zero.cos().0);
    /// ```
    #[must_use]
    fn default() -> Self {
        let zero: T = num_traits::cast(0).unwrap();
        let one: T = num_traits::cast(1).unwrap();
        Self {
            sin: trig::UnitNegRange(zero),
            cos: trig::UnitNegRange(one),
        }
    }
}

impl<T: Num + NumCast + PartialOrd + Copy> Validate for Angle<T> {
    /// Test whether an `Angle` is valid, i.e. both sin and cos are valid
    /// `UnitNegRange`s and the length of their hypotenuse is approximately 1.0.
    fn is_valid(&self) -> bool {
        let sin: f32 = num_traits::cast(self.sin.0).unwrap();
        let cos: f32 = num_traits::cast(self.cos.0).unwrap();
        self.sin.is_valid()
            && self.cos.is_valid()
            && is_within_tolerance(1.0_f32, libm::hypotf(sin, cos), core::f32::EPSILON)
    }
}

impl<T> Angle<T> {
    /// Construct an Angle from sin and cos values.
    #[must_use]
    pub const fn new(sin: trig::UnitNegRange<T>, cos: trig::UnitNegRange<T>) -> Self {
        Self { sin, cos }
    }

    /// Construct an Angle from y and x values.
    /// Normalises the values.
    #[must_use]
    pub fn from_y_x(y: T, x: T) -> Self
    where
        T: Num + NumCast + PartialOrd + Copy,
    {
        let y: f64 = num_traits::cast(y).unwrap();
        let x: f64 = num_traits::cast(x).unwrap();
        let length = libm::hypot(y, x);

        if is_small(length, core::f64::EPSILON) {
            Self::default()
        } else {
            Self::new(
                trig::UnitNegRange::clamp(num_traits::cast(y / length).unwrap()),
                trig::UnitNegRange::clamp(num_traits::cast(x / length).unwrap()),
            )
        }
    }

    /// The sine of the Angle.
    #[must_use]
    pub fn sin(self) -> trig::UnitNegRange<T> {
        self.sin
    }

    /// The cosine of the Angle.
    #[must_use]
    pub fn cos(self) -> trig::UnitNegRange<T> {
        self.cos
    }

    /// The absolute value of the angle, i.e. the angle with a positive sine.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_m45: Angle<f64> = Angle::from(Degrees(-45.0));
    /// let result_45 = angle_m45.abs();
    /// assert_eq!(Degrees(45.0), Degrees::from(result_45));
    /// ```
    #[must_use]
    pub fn abs(self) -> Self
    where
        T: Num + NumCast,
    {
        let sin_0: f64 = num_traits::cast(self.sin.0).unwrap();
        let value = libm::fabs(sin_0);
        Self {
            sin: trig::UnitNegRange(num_traits::cast(value).unwrap()),
            cos: self.cos,
        }
    }

    /// The opposite angle on the circle, i.e. +/- 180 degrees.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_m30: Angle<f64> = Angle::from(Degrees(-30.0));
    /// let result = angle_m30.opposite();
    /// assert_eq!(Degrees(150.0), Degrees::from(result));
    /// ```
    #[must_use]
    pub fn opposite(self) -> Self
    where
        T: Num + NumCast + Copy + Neg,
    {
        Self {
            sin: -self.sin,
            cos: -self.cos,
        }
    }

    /// Negate the cosine of the Angle.
    /// I.e. `PI` - `angle.radians()` for positive angles,
    ///      `angle.radians()` + `PI` for negative angles
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_45: Angle<f64> = Angle::from(Degrees(45.0));
    /// let result_45 = angle_45.negate_cos();
    /// assert_eq!(Degrees(135.0), Degrees::from(result_45));
    /// ```
    #[must_use]
    pub fn negate_cos(self) -> Self
    where
        T: Num + NumCast + Copy + Neg,
    {
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
    /// let angle_30: Angle<f64> = Angle::from(Degrees(30.0));
    /// let result_60 = angle_30.double();
    /// let result_60: Degrees<f64> = Degrees::from(result_60);
    ///
    /// // Note: multiplication is not precise...
    /// // assert_eq!(Degrees(60.0), result_60);
    /// let delta_angle = libm::fabs(60.0 - result_60.0);
    /// assert!(delta_angle <= 32.0 * std::f64::EPSILON);
    /// ```
    #[must_use]
    pub fn double(self) -> Self
    where
        T: Num + NumCast + Copy + Neg + PartialOrd,
    {
        let sin_0: f64 = num_traits::cast(self.sin.0).unwrap();
        let cos_0: f64 = num_traits::cast(self.cos.0).unwrap();
        Self {
            sin: trig::UnitNegRange::clamp(num_traits::cast(2.0 * sin_0 * cos_0).unwrap()),
            cos: trig::UnitNegRange::clamp(
                num_traits::cast((cos_0 - sin_0) * (cos_0 + sin_0)).unwrap(),
            ),
        }
    }

    /// Half the Angle.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_30: Angle<f64> = Angle::from(Degrees(30.0));
    /// let angle_60: Angle<f64> = Angle::from(Degrees(60.0));
    ///
    /// assert_eq!(angle_30, angle_60.half());
    /// ```
    #[must_use]
    pub fn half(self) -> Self
    where
        T: Num + NumCast + Copy + Neg + PartialOrd,
    {
        let sq_sin_half: f64 = num_traits::cast(trig::sq_sine_half(self.cos)).unwrap();
        let sin_0: f64 = num_traits::cast(self.sin.0).unwrap();
        let sin_half = libm::copysign(libm::sqrt(sq_sin_half), sin_0);

        let sq_cos_half: f64 = num_traits::cast(trig::sq_cosine_half(self.cos)).unwrap();
        let cos_half = libm::sqrt(sq_cos_half);

        Self {
            sin: trig::UnitNegRange::clamp(num_traits::cast(sin_half).unwrap()),
            cos: trig::UnitNegRange::clamp(num_traits::cast(cos_half).unwrap()),
        }
    }
}

impl<T: Num + NumCast + Copy> Neg for Angle<T> {
    type Output = Self;

    /// An implementation of Neg for Angle, i.e. -angle.
    /// Negates the sine of the Angle, does not affect the cosine.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_45: Angle<f64> = Angle::from(Degrees(45.0));
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

impl<T: Num + NumCast + Copy + PartialOrd + Neg> Add for Angle<T> {
    type Output = Self;

    /// Add two Angles, i.e. a + b
    /// Uses trigonometric identity functions, see:
    /// [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    ///
    /// let angle_30: Angle<f64> = Angle::from(Degrees(30.0));
    /// let angle_60: Angle<f64> = Angle::from(Degrees(60.0));
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

impl<T: Num + NumCast + Copy + PartialOrd + Neg> Sub for Angle<T> {
    type Output = Self;

    /// Subtract two Angles, i.e. a - b
    /// Uses trigonometric identity functions, see:
    /// [angle sum and difference identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities).
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees, is_within_tolerance};
    ///
    /// let angle_30: Angle<f64> = Angle::from(Degrees(30.0));
    /// let angle_60: Angle<f64> = Angle::from(Degrees(60.0));
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

impl<T: Num + NumCast + Copy + PartialOrd + Neg> PartialOrd for Angle<T> {
    /// Compare two Angles, i.e. a < b.
    /// It compares whether an `Angle` is clockwise of the other `Angle` on the
    /// unit circle.
    /// # Examples
    /// ```
    /// use angle_sc::{Angle, Degrees};
    /// let degrees_120: Angle<f64> = Angle::from(Degrees(120.0));
    /// let degrees_m120 = -degrees_120;
    /// assert!(degrees_120 < degrees_m120);
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let zero: T = num_traits::cast(0).unwrap();
        let delta = *other - *self;
        trig::UnitNegRange(zero).partial_cmp(&delta.sin)
    }
}

impl<S: Num + NumCast, T: Num + NumCast + PartialOrd + Copy + Neg> From<Degrees<S>> for Angle<T> {
    /// Construct an Angle from an angle in Degrees.
    /// In order to minimize round-off errors, this function calculates sines
    /// of angles with sine values <= 1 / sqrt(2): see
    /// <https://stackoverflow.com/questions/31502120/sin-and-cos-give-unexpected-results-for-well-known-angles>
    /// It is based on
    /// [GeographicLib::Math::sincosd](https://github.com/geographiclib/geographiclib/blob/1b0be832df51665ebe943f6d4d72eabc0de1bb92/src/Math.cpp#L106) function.
    #[must_use]
    fn from(a: Degrees<S>) -> Self
    where
        S: Num + NumCast,
        T: Num + NumCast + PartialOrd + Copy + Neg,
    {
        let a_0: f64 = num_traits::cast(a.0).unwrap();
        let rq = libm::remquo(a_0, 90.0);

        // Default is zero degrees.
        let mut sin = 0.0;
        let mut cos = 1.0;
        let abs_angle = libm::fabs(rq.0);
        if abs_angle > 0.0 {
            // 45 degrees is a special case
            if abs_angle == 45.0 {
                cos = core::f64::consts::FRAC_1_SQRT_2;
                sin = libm::copysign(cos, rq.0);
            } else {
                // 30 degrees is also a special case
                sin = if abs_angle == 30.0 {
                    libm::copysign(0.5, rq.0)
                } else {
                    libm::sin(rq.0.to_radians())
                };
                cos = trig::swap_sin_cos(sin);
            }
        }

        let sin = trig::UnitNegRange::<T>(num_traits::cast(sin).unwrap());
        let cos = trig::UnitNegRange::<T>(num_traits::cast(cos).unwrap());
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

impl<S: Num + NumCast + Copy, T: Num + NumCast + PartialOrd + Copy + Neg> From<Radians<S>>
    for Angle<T>
{
    /// Construct an Angle from an angle in Radians.
    /// In order to minimize round-off errors, this function calculates sines
    /// of angles with sine values <= 1 / sqrt(2)
    #[allow(clippy::similar_names)]
    #[must_use]
    fn from(a: Radians<S>) -> Self
    where
        S: Num + NumCast + Copy,
        T: Num + NumCast + PartialOrd + Copy + Neg,
    {
        const FRAC_3_PI_4: f64 = core::f64::consts::PI - core::f64::consts::FRAC_PI_4;

        let valid_angle: f64 = num_traits::cast(a.normalise().0).unwrap();
        let abs_angle = libm::fabs(valid_angle);

        let over_45_degrees = core::f64::consts::FRAC_PI_4 < abs_angle;
        let under_135_degrees = abs_angle < FRAC_3_PI_4;
        if over_45_degrees && under_135_degrees {
            let cos = libm::sin(core::f64::consts::FRAC_PI_2 - abs_angle);
            let sin = trig::cosine_from_sine(cos, valid_angle);
            let sin: trig::UnitNegRange<T> = trig::UnitNegRange(num_traits::cast(sin).unwrap());
            let cos: trig::UnitNegRange<T> = trig::UnitNegRange(num_traits::cast(cos).unwrap());

            Self { sin, cos }
        } else {
            let sin = libm::sin(valid_angle);
            let sign = core::f64::consts::FRAC_PI_2 - abs_angle;
            let cos = trig::cosine_from_sine(sin, sign);
            let sin: trig::UnitNegRange<T> = trig::UnitNegRange(num_traits::cast(sin).unwrap());
            let cos: trig::UnitNegRange<T> = trig::UnitNegRange(num_traits::cast(cos).unwrap());

            Self { sin, cos }
        }
    }
}

impl<S: Num + NumCast, T: Num + NumCast> From<Angle<T>> for Radians<S> {
    /// Convert an Angle to Radians.
    #[must_use]
    fn from(a: Angle<T>) -> Self
    where
        S: Num + NumCast,
        T: Num + NumCast,
    {
        let sin: f64 = num_traits::cast(a.sin.0).unwrap();
        let cos: f64 = num_traits::cast(a.cos.0).unwrap();
        Self(num_traits::cast(libm::atan2(sin, cos)).unwrap())
    }
}

impl<S: Num + NumCast + Copy, T: Num + NumCast> From<Angle<T>> for Degrees<S> {
    /// Convert an Angle to Degrees.
    #[must_use]
    fn from(a: Angle<T>) -> Self
    where
        S: Num + NumCast + Copy,
        T: Num + NumCast,
    {
        Self::from(Radians::from(a))
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
        let deserialized: Degrees<f64> = serde_json::from_str(&serialized).unwrap();
        assert_eq!(one, deserialized);

        let bad_text = "junk";
        let _serde_error = serde_json::from_str::<Degrees<f64>>(&bad_text).unwrap_err();

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

        assert_eq!(zero, Angle::from(Degrees(0.0)));

        let degrees_45: Angle<f64> = Angle::from(Degrees(45.0));
        assert!(degrees_45.is_valid());
        assert_eq!(FRAC_1_SQRT_2, degrees_45.sin().0);
        assert_eq!(FRAC_1_SQRT_2, degrees_45.cos().0);

        let degrees_m120: Angle<f64> = Angle::from(Degrees(-120.0));
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

        // let serialized = serde_json::to_string(&zero).unwrap();
        // let deserialized: Angle = serde_json::from_str(&serialized).unwrap();
        // assert_eq!(zero, deserialized);

        // let bad_text = "junk";
        // let _serde_error = serde_json::from_str::<Angle>(&bad_text).unwrap_err();

        print!("Angle: {:?}", degrees_m45);
    }

    #[test]
    fn angle_maths() {
        let degrees_60: Angle<f64> = Angle::from(Degrees(60.0));
        let degrees_120: Angle<f64> = Angle::from(Degrees(120.0));
        let degrees_m120 = -degrees_120;

        assert!(degrees_120 < degrees_m120);
        assert_eq!(degrees_120, degrees_m120.abs());
        assert_eq!(degrees_60, degrees_m120.opposite());
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
