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
//! A Rust library for performing accurate and efficient trigonometry calculations.
//!
//! ## Description
//!
//! The standard trigonometry functions: `sin`, `cos`, `tan`, etc.
//! [give unexpected results for well-known angles](https://stackoverflow.com/questions/31502120/sin-and-cos-give-unexpected-results-for-well-known-angles#answer-31525208).  
//! This is because the functions use parameters with `radians` units instead of `degrees`.
//! The conversion from `degrees` to `radians` suffers from
//! [round-off error](https://en.wikipedia.org/wiki/Round-off_error) due to
//! `radians` being based on the irrational number π.
//! This library provides a [sincos](src/trig.rs#sincos) function to calculate more
//! accurate values than the standard `sin` and `cos` functions for angles in radians  
//! and a [sincosd](src/trig.rs#sincosd) function to calculate more accurate values
//! for angles in degrees.
//!
//! The library also provides an [Angle](#angle) struct which represents an angle
//! by its sine and cosine as the coordinates of a
//! [unit circle](https://en.wikipedia.org/wiki/Unit_circle),  
//! see *Figure 1*.
//!
//! ![Unit circle](https://upload.wikimedia.org/wikipedia/commons/thumb/7/72/Sinus_und_Kosinus_am_Einheitskreis_1.svg/250px-Sinus_und_Kosinus_am_Einheitskreis_1.svg.png)  
//! *Figure 1 Unit circle formed by cos *θ* and sin *θ**
//!
//! The `Angle` struct enables more accurate calculations of angle rotations and
//! conversions to and from `degrees` or `radians`.
//!
//! ## Features
//!
//! * `Degrees`, `Radians` and `Angle` types;
//! * functions for accurately calculating sines and cosines of angles in `Degrees` or `Radians`
//!     using [remquo](https://pubs.opengroup.org/onlinepubs/9699919799/functions/remquo.html);
//! * functions for accurately calculating sines and cosines of differences of angles in `Degrees` or `Radians`
//!     using the [2Sum](https://en.wikipedia.org/wiki/2Sum) algorithm;
//! * functions for accurately calculating sums and differences of `Angles` using
//!     [trigonometric identities](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities);
//! * and some [spherical trigonometry](https://en.wikipedia.org/wiki/Spherical_trigonometry) functions.
//! * The library is declared [no_std](https://docs.rust-embedded.org/book/intro/no-std.html).
//!
//! ## Examples
//!
//! The following example shows the `round-off error` inherent in calculating angles in `radians`.  
//! It calculates the correct sine and cosine for 60° and converts them back
//! precisely to 60°, but it fails to convert them to the precise angle in `radians`: π/3.
//! ```
//! use angle_sc::{Angle, Degrees, Radians, is_within_tolerance, trig};
//!
//! let angle_60 = Angle::from(Degrees(60.0));
//! assert_eq!(trig::COS_30_DEGREES, angle_60.sin().0);
//! assert_eq!(0.5, angle_60.cos().0);
//! assert_eq!(60.0, Degrees::from(angle_60).0);
//!
//! // assert_eq!(core::f64::consts::FRAC_PI_3, Radians::from(angle_60).0); // Fails because PI is irrational
//! assert!(is_within_tolerance(
//!    core::f64::consts::FRAC_PI_3,
//!    Radians::from(angle_60).0,
//!    f64::EPSILON
//! ));
//! ```
//!
//! The following example calculates the sine and cosine between the difference
//! of two angles in `degrees`: -155° - 175°.  
//! It is more accurate than calling the `Angle` `From` trait in the example above
//! with the difference in `degrees`.  
//! It is particularly useful for implementing the
//! [Haversine formula](https://en.wikipedia.org/wiki/Haversine_formula)
//! which requires sines and cosines of both longitude and latitude differences.  
//! Note: in this example sine and cosine of 30° are converted precisely to π/6.
//! ```
//! use angle_sc::{Angle, Degrees, Radians, trig};
//!
//! // Difference of Degrees(-155.0) - Degrees(175.0)
//! let angle_30 = Angle::from((Degrees(-155.0), Degrees(175.0)));
//! assert_eq!(0.5, angle_30.sin().0);
//! assert_eq!(trig::COS_30_DEGREES, angle_30.cos().0);
//! assert_eq!(30.0, Degrees::from(angle_30).0);
//! assert_eq!(core::f64::consts::FRAC_PI_6, Radians::from(angle_30).0);
//! ```
//!
//! ## Design
//!
//! ### Trigonometry Functions
//!
//! The `trig` module contains accurate and efficient trigonometry functions.
//!
//! ### Angle
//!
//! The `Angle` struct represents an angle by its sine and cosine instead of in
//! `degrees` or `radians`.
//!
//! This representation an angle makes functions such as
//! rotating an angle +/-90° around the unit circle or calculating the opposite angle;
//! simple, accurate and efficient since they just involve changing the signs
//! and/or positions of the `sin` and `cos` values.
//!
//! `Angle` `Add` and `Sub` traits are implemented using
//! [angle sum and difference](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Angle_sum_and_difference_identities)
//! trigonometric identities,
//! while `Angle` [double](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Double-angle_formulae)
//! and [half](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae) methods use other
//! trigonometric identities.
//!
//! The `sin` and `cos` fields of `Angle` are `UnitNegRange`s:,
//! a [newtype](https://rust-unofficial.github.io/patterns/patterns/behavioural/newtype.html)
//! with values in the range -1.0 to +1.0 inclusive.

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
    /// The absolute value of the angle.
    #[must_use]
    pub fn abs(self) -> Self {
        Self(libm::fabs(self.0))
    }

    /// The opposite angle on the circle, i.e. +/- 180 degrees.
    #[must_use]
    pub fn opposite(self) -> Self {
        Self(if 0.0 < self.0 {
            self.0 - 180.0
        } else {
            self.0 + 180.0
        })
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
    /// Uses the [2Sum](https://en.wikipedia.org/wiki/2Sum) algorithm to reduce
    /// round-off error.
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
        let (s, t) = two_sum(self.0, other.0);
        Self(if s <= -180.0 {
            s + 360.0 + t
        } else if s > 180.0 {
            s - 360.0 + t
        } else {
            s
        })
    }
}

impl Sub for Degrees {
    type Output = Self;

    /// Subtract a pair of angles in Degrees, wraps around +/-180.  
    /// Uses the [2Sum](https://en.wikipedia.org/wiki/2Sum) algorithm to reduce
    /// round-off error.
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

/// The Radians newtype an f64.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd)]
pub struct Radians(pub f64);

impl Radians {
    /// The absolute value of the angle.
    #[must_use]
    pub fn abs(self) -> Self {
        Self(libm::fabs(self.0))
    }

    /// The opposite angle on the circle, i.e. +/- PI.
    #[must_use]
    pub fn opposite(self) -> Self {
        Self(if 0.0 < self.0 {
            self.0 - core::f64::consts::PI
        } else {
            self.0 + core::f64::consts::PI
        })
    }

    /// Clamp value into the range: `0.0..=max_value`.
    /// # Examples
    /// ```
    /// use angle_sc::Radians;
    ///
    /// let value = Radians(-f64::EPSILON);
    /// assert_eq!(Radians(0.0), value.clamp(Radians(1.0)));
    /// let value = Radians(0.0);
    /// assert_eq!(Radians(0.0), value.clamp(Radians(1.0)));
    /// let value = Radians(1.0);
    /// assert_eq!(Radians(1.0), value.clamp(Radians(1.0)));
    /// let value = Radians(1.0 + f64::EPSILON);
    /// assert_eq!(Radians(1.0), value.clamp(Radians(1.0)));
    /// ```
    #[must_use]
    pub fn clamp(self, max_value: Self) -> Self {
        Self(self.0.clamp(0.0, max_value.0))
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
    /// Uses the [2Sum](https://en.wikipedia.org/wiki/2Sum) algorithm to reduce
    /// round-off error.
    /// # Examples
    /// ```
    /// use angle_sc::{Radians, is_within_tolerance};
    ///
    /// let angle_120 = Radians(2.0 * core::f64::consts::FRAC_PI_3);
    /// let result = angle_120 + angle_120;
    /// assert!(is_within_tolerance(-2.0 * core::f64::consts::FRAC_PI_3, result.0,  4.0 * f64::EPSILON));
    /// ```
    #[must_use]
    fn add(self, other: Self) -> Self {
        let (s, t) = two_sum(self.0, other.0);
        Self(if s <= -core::f64::consts::PI {
            s + core::f64::consts::TAU + t
        } else if s > core::f64::consts::PI {
            s - core::f64::consts::TAU + t
        } else {
            s
        })
    }
}

impl Sub for Radians {
    type Output = Self;

    /// Subtract a pair of angles in Radians,  wraps around +/-PI.  
    /// Uses the [2Sum](https://en.wikipedia.org/wiki/2Sum) algorithm to reduce
    /// round-off error.
    /// # Examples
    /// ```
    /// use angle_sc::{Radians, is_within_tolerance};
    ///
    /// let angle_120 = Radians(2.0 * core::f64::consts::FRAC_PI_3);
    /// let angle_m120 = -angle_120;
    /// let result = angle_m120 - angle_120;
    /// assert!(is_within_tolerance(angle_120.0, result.0,  4.0 * f64::EPSILON));
    /// ```
    #[must_use]
    fn sub(self, other: Self) -> Self {
        self + -other
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
            && is_within_tolerance(1.0, libm::hypot(self.sin.0, self.cos.0), f64::EPSILON)
    }
}

impl Angle {
    /// Construct an Angle from sin and cos values.  
    #[must_use]
    pub const fn new(sin: trig::UnitNegRange, cos: trig::UnitNegRange) -> Self {
        Self { sin, cos }
    }

    /// Construct an Angle from y and x values.  
    /// Normalizes the values.
    #[must_use]
    pub fn from_y_x(y: f64, x: f64) -> Self {
        let length = libm::hypot(y, x);

        if is_small(length, f64::EPSILON) {
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

    /// The tangent of the Angle.
    ///
    /// returns the tangent or `None` if `self.cos < SQ_EPSILON`
    #[must_use]
    pub fn tan(self) -> Option<f64> {
        trig::tan(self.sin, self.cos)
    }

    /// The cosecant of the Angle.
    ///
    /// returns the cosecant or `None` if `self.sin < SQ_EPSILON`
    #[must_use]
    pub fn csc(self) -> Option<f64> {
        trig::csc(self.sin)
    }

    /// The secant of the Angle.
    ///
    /// returns the secant or `None` if `self.cos < SQ_EPSILON`
    #[must_use]
    pub fn sec(self) -> Option<f64> {
        trig::sec(self.cos)
    }

    /// The cotangent of the Angle.
    ///
    /// returns the cotangent or `None` if `self.sin < SQ_EPSILON`
    #[must_use]
    pub fn cot(self) -> Option<f64> {
        trig::cot(self.sin, self.cos)
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
            sin: self.sin.abs(),
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

    /// A quarter turn clockwise around the circle, i.e. + 90°.
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

    /// A quarter turn counter-clockwise around the circle, i.e. - 90°.
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
    /// assert!(delta_angle <= 32.0 * f64::EPSILON);
    /// ```
    #[must_use]
    pub fn double(self) -> Self {
        Self {
            sin: trig::UnitNegRange::clamp(2.0 * self.sin.0 * self.cos.0),
            cos: trig::UnitNegRange::clamp((self.cos.0 - self.sin.0) * (self.cos.0 + self.sin.0)),
        }
    }

    /// Half of the Angle.  
    /// See: [Half-angle formulae](https://en.wikipedia.org/wiki/List_of_trigonometric_identities#Half-angle_formulae)
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
    /// assert!(is_within_tolerance(Degrees(30.0).0, Degrees::from(result_30).0, 32.0 * f64::EPSILON));
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
    ///
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
    /// Construct an `Angle` from an angle in Degrees.  
    ///
    /// Examples:
    /// ```
    /// use angle_sc::{Angle, Degrees, is_within_tolerance, trig};
    ///
    /// let angle = Angle::from(Degrees(60.0));
    /// assert_eq!(trig::COS_30_DEGREES, angle.sin().0);
    /// assert_eq!(0.5, angle.cos().0);
    /// assert_eq!(60.0, Degrees::from(angle).0);
    /// ```
    #[must_use]
    fn from(a: Degrees) -> Self {
        let (sin, cos) = trig::sincosd(a);
        Self { sin, cos }
    }
}

impl From<(Degrees, Degrees)> for Angle {
    /// Construct an `Angle` from the difference of a pair angles in Degrees:
    /// a - b  
    ///
    /// Examples:
    /// ```
    /// use angle_sc::{Angle, Degrees, trig};
    ///
    /// // Difference of Degrees(-155.0) - Degrees(175.0)
    /// let angle = Angle::from((Degrees(-155.0), Degrees(175.0)));
    /// assert_eq!(0.5, angle.sin().0);
    /// assert_eq!(trig::COS_30_DEGREES, angle.cos().0);
    /// assert_eq!(30.0, Degrees::from(angle).0);
    /// ```
    #[must_use]
    fn from(params: (Degrees, Degrees)) -> Self {
        let (sin, cos) = trig::sincosd_diff(params.0, params.1);
        Self { sin, cos }
    }
}

impl From<Radians> for Angle {
    /// Construct an `Angle` from an angle in Radians.  
    ///
    /// Examples:
    /// ```
    /// use angle_sc::{Angle, Radians, trig};
    ///
    /// let angle = Angle::from(Radians(-core::f64::consts::FRAC_PI_6));
    /// assert_eq!(-0.5, angle.sin().0);
    /// assert_eq!(trig::COS_30_DEGREES, angle.cos().0);
    /// assert_eq!(-core::f64::consts::FRAC_PI_6, Radians::from(angle).0);
    /// ```
    #[must_use]
    fn from(a: Radians) -> Self {
        let (sin, cos) = trig::sincos(a);
        Self { sin, cos }
    }
}

impl From<(Radians, Radians)> for Angle {
    /// Construct an Angle from the difference of a pair angles in Radians:
    /// a - b  
    ///
    /// Examples:
    /// ```
    /// use angle_sc::{Angle, Radians, trig};
    ///
    /// // 6*π - π/3 radians round trip
    /// let angle = Angle::from((
    ///     Radians(3.0 * core::f64::consts::TAU),
    ///     Radians(core::f64::consts::FRAC_PI_3),
    /// ));
    /// assert_eq!(-core::f64::consts::FRAC_PI_3, Radians::from(angle).0);
    /// ```
    #[must_use]
    fn from(params: (Radians, Radians)) -> Self {
        let (sin, cos) = trig::sincos_diff(params.0, params.1);
        Self { sin, cos }
    }
}

impl From<Angle> for Radians {
    /// Convert an Angle to Radians.
    #[must_use]
    fn from(a: Angle) -> Self {
        trig::arctan2(a.sin, a.cos)
    }
}

impl From<Angle> for Degrees {
    /// Convert an Angle to Degrees.
    #[must_use]
    fn from(a: Angle) -> Self {
        trig::arctan2d(a.sin, a.cos)
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

/// Calculates floating-point sum and error.
/// The [2Sum](https://en.wikipedia.org/wiki/2Sum) algorithm.
///
/// * `a`, `b` the floating-point numbers to add.
///
/// returns (a + b) and the floating-point error: $t = a + b - (a \oplus b)$  
/// so: $a+b=s+t$.
#[must_use]
pub fn two_sum<T>(a: T, b: T) -> (T, T)
where
    T: Copy + Add<Output = T> + Sub<Output = T>,
{
    let s = a + b;
    let a_prime = s - b;
    let b_prime = s - a_prime;
    let delta_a = a - a_prime;
    let delta_b = b - b_prime;
    let t = delta_a + delta_b;
    (s, t)
}

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
///
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

    #[test]
    fn test_degrees_traits() {
        let one = Degrees(1.0);
        let two = Degrees(2.0);
        let one_clone = one.clone();
        assert!(one_clone == one);

        let m_two = -two;
        assert_eq!(-2.0, m_two.0);
        assert_eq!(two, m_two.abs());

        let m_one = one + m_two;
        assert_eq!(-1.0, m_one.0);

        let d_120 = Degrees(120.0);
        let d_m120 = Degrees(-120.0);
        assert_eq!(d_120, d_m120.abs());

        assert_eq!(Degrees(30.0), Degrees(-155.0) - Degrees(175.0));

        assert_eq!(d_m120, d_120 + d_120);
        assert_eq!(d_120, d_m120 + d_m120);
        assert_eq!(d_120, d_m120 - d_120);

        assert_eq!(Degrees(-60.0), d_120.opposite());
        assert_eq!(Degrees(60.0), d_m120.opposite());

        let serialized = serde_json::to_string(&one).unwrap();
        let deserialized: Degrees = serde_json::from_str(&serialized).unwrap();
        assert_eq!(one, deserialized);

        let bad_text = "junk";
        let _serde_error = serde_json::from_str::<Degrees>(&bad_text).unwrap_err();

        print!("Degrees: {:?}", one);
    }

    #[test]
    fn test_radians_traits() {
        let one = Radians(1.0);
        let two = Radians(2.0);
        assert!(one < two);

        let one_clone = one.clone();
        assert!(one_clone == one);

        let m_two = -two;
        assert_eq!(-2.0, m_two.0);
        assert_eq!(two, m_two.abs());

        let m_one = one + m_two;
        assert_eq!(-1.0, m_one.0);

        let result_1 = m_two - two;
        assert_eq!(core::f64::consts::TAU - 4.0, result_1.0);
        assert_eq!(core::f64::consts::PI - 4.0, result_1.opposite().0);

        let result_2 = two - m_two;
        assert_eq!(4.0 - core::f64::consts::TAU, result_2.0);
        assert_eq!(4.0 - core::f64::consts::PI, result_2.opposite().0);

        let value = Radians(-f64::EPSILON);
        assert_eq!(Radians(0.0), value.clamp(Radians(1.0)));
        let value = Radians(0.0);
        assert_eq!(Radians(0.0), value.clamp(Radians(1.0)));
        let value = Radians(1.0);
        assert_eq!(Radians(1.0), value.clamp(Radians(1.0)));
        let value = Radians(1.0 + f64::EPSILON);
        assert_eq!(Radians(1.0), value.clamp(Radians(1.0)));

        print!("Radians: {:?}", one);
    }

    #[test]
    fn test_angle_traits() {
        let zero = Angle::default();
        assert_eq!(0.0, zero.sin().0);
        assert_eq!(1.0, zero.cos().0);
        assert_eq!(0.0, zero.tan().unwrap());
        assert!(zero.csc().is_none());
        assert_eq!(1.0, zero.sec().unwrap());
        assert!(zero.cot().is_none());
        assert!(zero.is_valid());

        let zero_clone = zero.clone();
        assert_eq!(zero, zero_clone);

        let one = Angle::from_y_x(1.0, 0.0);
        assert_eq!(1.0, one.sin().0);
        assert_eq!(0.0, one.cos().0);
        assert!(one.tan().is_none());
        assert_eq!(1.0, one.csc().unwrap());
        assert!(one.sec().is_none());
        assert_eq!(0.0, one.cot().unwrap());
        assert!(one.is_valid());

        let angle_m45 = Angle::from_y_x(-f64::EPSILON, f64::EPSILON);
        assert!(is_within_tolerance(
            -core::f64::consts::FRAC_1_SQRT_2,
            angle_m45.sin().0,
            f64::EPSILON
        ));
        assert!(is_within_tolerance(
            core::f64::consts::FRAC_1_SQRT_2,
            angle_m45.cos().0,
            f64::EPSILON
        ));

        assert!(angle_m45 < zero);

        let serialized = serde_json::to_string(&zero).unwrap();
        let deserialized: Angle = serde_json::from_str(&serialized).unwrap();
        assert_eq!(zero, deserialized);

        let bad_text = "junk";
        let _serde_error = serde_json::from_str::<Angle>(&bad_text).unwrap_err();

        print!("Angle: {:?}", angle_m45);
    }
    #[test]
    fn test_angle_conversion() {
        let zero = Angle::default();

        let too_small = Angle::from_y_x(-f64::EPSILON / 2.0, f64::EPSILON / 2.0);
        assert!(too_small.is_valid());
        assert_eq!(zero, too_small);

        let small = Angle::from(-trig::MAX_COS_ANGLE_IS_ONE);
        assert!(small.is_valid());
        assert_eq!(-trig::MAX_COS_ANGLE_IS_ONE.0, small.sin().0);
        assert_eq!(1.0, small.cos().0);
        assert_eq!(-trig::MAX_COS_ANGLE_IS_ONE.0, Radians::from(small).0);

        let angle_30 = Angle::from((
            Radians(core::f64::consts::FRAC_PI_3),
            Radians(core::f64::consts::FRAC_PI_6),
        ));
        assert!(angle_30.is_valid());
        assert_eq!(0.5, angle_30.sin().0);
        assert_eq!(libm::sqrt(3.0) / 2.0, angle_30.cos().0);
        assert_eq!(30.0, Degrees::from(angle_30).0);
        assert_eq!(core::f64::consts::FRAC_PI_6, Radians::from(angle_30).0);

        let angle_45 = Angle::from(Radians(core::f64::consts::FRAC_PI_4));
        assert!(angle_45.is_valid());
        assert_eq!(core::f64::consts::FRAC_1_SQRT_2, angle_45.sin().0);
        assert_eq!(core::f64::consts::FRAC_1_SQRT_2, angle_45.cos().0);
        assert_eq!(45.0, Degrees::from(angle_45).0);
        assert_eq!(core::f64::consts::FRAC_PI_4, Radians::from(angle_45).0);

        let angle_m45 = Angle::from(Degrees(-45.0));
        assert!(angle_m45.is_valid());
        assert_eq!(-core::f64::consts::FRAC_1_SQRT_2, angle_m45.sin().0);
        assert_eq!(core::f64::consts::FRAC_1_SQRT_2, angle_m45.cos().0);
        assert_eq!(-45.0, Degrees::from(angle_m45).0);
        assert_eq!(-core::f64::consts::FRAC_PI_4, Radians::from(angle_m45).0);

        let angle_60 = Angle::from((Degrees(-140.0), Degrees(160.0)));
        assert!(angle_60.is_valid());
        assert_eq!(libm::sqrt(3.0) / 2.0, angle_60.sin().0);
        assert_eq!(0.5, angle_60.cos().0);
        assert_eq!(60.0, Degrees::from(angle_60).0);
        // Fails because PI is irrational
        // assert_eq!(core::f64::consts::FRAC_PI_3, Radians::from(angle_60).0);
        assert!(is_within_tolerance(
            core::f64::consts::FRAC_PI_3,
            Radians::from(angle_60).0,
            f64::EPSILON
        ));

        let angle_30 = Angle::from((Degrees(-155.0), Degrees(175.0)));
        // assert!(angle_30.is_valid());
        assert_eq!(0.5, angle_30.sin().0);
        assert_eq!(libm::sqrt(3.0) / 2.0, angle_30.cos().0);
        assert_eq!(30.0, Degrees::from(angle_30).0);
        assert_eq!(core::f64::consts::FRAC_PI_6, Radians::from(angle_30).0);

        let angle_120 = Angle::from(Degrees(120.0));
        assert!(angle_120.is_valid());
        assert_eq!(libm::sqrt(3.0) / 2.0, angle_120.sin().0);
        assert_eq!(-0.5, angle_120.cos().0);
        assert_eq!(120.0, Degrees::from(angle_120).0);
        assert_eq!(
            2.0 * core::f64::consts::FRAC_PI_3,
            Radians::from(angle_120).0
        );

        let angle_m120 = Angle::from(Degrees(-120.0));
        assert!(angle_m120.is_valid());
        assert_eq!(-libm::sqrt(3.0) / 2.0, angle_m120.sin().0);
        assert_eq!(-0.5, angle_m120.cos().0);
        assert_eq!(-120.0, Degrees::from(angle_m120).0);
        assert_eq!(
            -2.0 * core::f64::consts::FRAC_PI_3,
            Radians::from(angle_m120).0
        );

        let angle_m140 = Angle::from(Degrees(-140.0));
        assert!(angle_m140.is_valid());
        assert!(is_within_tolerance(
            -0.6427876096865393,
            angle_m140.sin().0,
            f64::EPSILON
        ));
        assert!(is_within_tolerance(
            -0.7660444431189781,
            angle_m140.cos().0,
            f64::EPSILON
        ));
        assert_eq!(-140.0, Degrees::from(angle_m140).0);

        let angle_180 = Angle::from(Degrees(180.0));
        assert!(angle_180.is_valid());
        assert_eq!(0.0, angle_180.sin().0);
        assert_eq!(-1.0, angle_180.cos().0);
        assert_eq!(180.0, Degrees::from(angle_180).0);
        assert_eq!(core::f64::consts::PI, Radians::from(angle_180).0);
    }

    #[test]
    fn test_angle_maths() {
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
        assert_eq!(Degrees(120.0).0, Degrees::from(result).0);

        let result = degrees_120 + degrees_120;
        assert_eq!(Degrees(-120.0).0, Degrees::from(result).0);

        let result = degrees_60.double();
        assert_eq!(Degrees(120.0).0, Degrees::from(result).0);

        let result = degrees_120.double();
        assert_eq!(Degrees(-120.0).0, Degrees::from(result).0);

        assert_eq!(-degrees_60, degrees_m120.half());
    }

    #[test]
    fn test_two_sum() {
        let result = two_sum(1.0, 1.0);
        assert_eq!(2.0, result.0);
        assert_eq!(0.0, result.1);

        let result = two_sum(1.0, 1e-53);
        assert_eq!(1.0, result.0);
        assert_eq!(1e-53, result.1);

        let result = two_sum(1.0, -1e-53);
        assert_eq!(1.0, result.0);
        assert_eq!(-1e-53, result.1);
    }

    #[test]
    fn test_min_and_max() {
        // min -ve and +ve
        assert_eq!(min(-1.0 + f64::EPSILON, -1.0), -1.0);
        assert_eq!(min(1.0, 1.0 + f64::EPSILON), 1.0);
        // max -ve and +ve
        assert_eq!(max(-1.0, -1.0 - f64::EPSILON), -1.0);
        assert_eq!(max(1.0 - f64::EPSILON, 1.0), 1.0);
    }

    #[test]
    fn test_is_within_tolerance() {
        // below minimum tolerance
        assert_eq!(
            false,
            is_within_tolerance(1.0 - 2.0 * f64::EPSILON, 1.0, f64::EPSILON)
        );

        // within minimum tolerance
        assert!(is_within_tolerance(1.0 - f64::EPSILON, 1.0, f64::EPSILON));

        // within maximum tolerance
        assert!(is_within_tolerance(1.0 + f64::EPSILON, 1.0, f64::EPSILON));

        // above maximum tolerance
        assert_eq!(
            false,
            is_within_tolerance(1.0 + 2.0 * f64::EPSILON, 1.0, f64::EPSILON)
        );
    }
}
