// Copyright (c) 2026 Ken Barker

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

//! The `vector2d` module contains 2D vector functions.

/// 2D vector dot product function: a . b.
///
/// * `a_0`, `a_1` the first vector values.
/// * `b_0`, `b_1` the second vector values.
///
/// * returns the dot product of the 2D vectors.
#[must_use]
pub fn dot_product(a_0: f64, a_1: f64, b_0: f64, b_1: f64) -> f64 {
    a_0 * b_0 + a_1 * b_1
}

/// 2D vector perp product function: a x b.
///
/// * `a_0`, `a_1` the first vector values.
/// * `b_0`, `b_1` the second vector values.
///
/// * returns the perp product of the 2D vectors.
#[must_use]
pub fn perp_product(a_0: f64, a_1: f64, b_0: f64, b_1: f64) -> f64 {
    dot_product(a_0, a_1, b_1, -b_0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dot_product() {
        assert_eq!(1.0, dot_product(1.0, 0.0, 1.0, 0.0));
        assert_eq!(0.0, dot_product(1.0, 0.0, 0.0, 1.0));
        assert_eq!(0.0, dot_product(0.0, 1.0, 1.0, 0.0));
    }

    #[test]
    fn test_perp_product() {
        assert_eq!(0.0, perp_product(1.0, 0.0, 1.0, 0.0));
        assert_eq!(1.0, perp_product(1.0, 0.0, 0.0, 1.0));
        assert_eq!(-1.0, perp_product(0.0, 1.0, 1.0, 0.0));
    }
}
