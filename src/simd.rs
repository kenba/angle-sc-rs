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

//! The `simd` module contains functions for performing simd vector
//! calculations on the `x86` and `x86_64` processor architectures.

#[cfg(target_arch = "x86")]
use core::arch::x86::{__m128d, _mm_cvtsd_f64, _mm_dp_pd, _mm_set_pd};
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::{__m128d, _mm_cvtsd_f64, _mm_dp_pd, _mm_set_pd};

/// 2D vector double dot product function: a . b.
///
/// * `a`, `b` the __m128d double vectors.
///
/// * returns the 2D dot product of the vector double values.
///
/// # Safety
///
/// Requires SIMD Extensions SSE4.2 on the target processor.
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "sse4.2")]
#[inline]
#[must_use]
pub unsafe fn dot2d(a: __m128d, b: __m128d) -> f64 {
    let c = _mm_dp_pd(a, b, 0x33);
    _mm_cvtsd_f64(c)
}

/// 2D vector double dot product function: a . b.
///
/// * `a_0`, `a_1` the first vector values.
/// * `b_0`, `b_1` the second vector values.
///
/// * returns the 2D dot product of the vector double values.
///
/// # Safety
///
/// Requires SIMD Extensions SSE4.2 on the target processor.
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "sse4.2")]
#[inline]
#[must_use]
pub unsafe fn dot_product(a_0: f64, a_1: f64, b_0: f64, b_1: f64) -> f64 {
    unsafe { dot2d(_mm_set_pd(a_1, a_0), _mm_set_pd(b_1, b_0)) }
}

/// 2D vector double perp product function: a x b.
///
/// * `a_0`, `a_1` the first vector values.
/// * `b_0`, `b_1` the second vector values.
///
/// * returns the 2D perp product of the vector double values.
///
/// # Safety
///
/// Requires SIMD Extensions SSE4.2 on the target processor.
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
#[target_feature(enable = "sse4.2")]
#[inline]
#[must_use]
pub unsafe fn perp_product(a_0: f64, a_1: f64, b_0: f64, b_1: f64) -> f64 {
    unsafe { dot2d(_mm_set_pd(a_1, a_0), _mm_set_pd(-b_0, b_1)) }
}
