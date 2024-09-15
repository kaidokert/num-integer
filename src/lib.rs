// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Integer trait and functions.
//!
//! ## Compatibility
//!
//! The `num-integer` crate is tested for rustc 1.31 and greater.

#![doc(html_root_url = "https://docs.rs/num-integer/0.1")]
#![no_std]

use num_traits::{PrimInt, Signed};

pub trait Integer: PrimInt + Signed {
    /// Floored integer division.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert!(( 8).div_floor(& 3) ==  2);
    /// assert!(( 8).div_floor(&-3) == -3);
    /// assert!((-8).div_floor(& 3) == -3);
    /// assert!((-8).div_floor(&-3) ==  2);
    ///
    /// assert!(( 1).div_floor(& 2) ==  0);
    /// assert!(( 1).div_floor(&-2) == -1);
    /// assert!((-1).div_floor(& 2) == -1);
    /// assert!((-1).div_floor(&-2) ==  0);
    /// ~~~
    fn div_floor(&self, other: &Self) -> Self;

    /// Floored integer modulo, satisfying:
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// # let n = 1; let d = 1;
    /// assert!(n.div_floor(&d) * d + n.mod_floor(&d) == n)
    /// ~~~
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert!(( 8).mod_floor(& 3) ==  2);
    /// assert!(( 8).mod_floor(&-3) == -1);
    /// assert!((-8).mod_floor(& 3) ==  1);
    /// assert!((-8).mod_floor(&-3) == -2);
    ///
    /// assert!(( 1).mod_floor(& 2) ==  1);
    /// assert!(( 1).mod_floor(&-2) == -1);
    /// assert!((-1).mod_floor(& 2) ==  1);
    /// assert!((-1).mod_floor(&-2) == -1);
    /// ~~~
    fn mod_floor(&self, other: &Self) -> Self;

    /// Ceiled integer division.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(( 8).div_ceil( &3),  3);
    /// assert_eq!(( 8).div_ceil(&-3), -2);
    /// assert_eq!((-8).div_ceil( &3), -2);
    /// assert_eq!((-8).div_ceil(&-3),  3);
    ///
    /// assert_eq!(( 1).div_ceil( &2), 1);
    /// assert_eq!(( 1).div_ceil(&-2), 0);
    /// assert_eq!((-1).div_ceil( &2), 0);
    /// assert_eq!((-1).div_ceil(&-2), 1);
    /// ~~~
    fn div_ceil(&self, other: &Self) -> Self {
        let (q, r) = self.div_mod_floor(other);
        if r.is_zero() {
            q
        } else {
            q + Self::one()
        }
    }

    /// Greatest Common Divisor (GCD).
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(6.gcd(&8), 2);
    /// assert_eq!(7.gcd(&3), 1);
    /// ~~~
    fn gcd(&self, other: &Self) -> Self;

    /// Lowest Common Multiple (LCM).
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(7.lcm(&3), 21);
    /// assert_eq!(2.lcm(&4), 4);
    /// assert_eq!(0.lcm(&0), 0);
    /// ~~~
    fn lcm(&self, other: &Self) -> Self;

    /// Greatest Common Divisor (GCD) and
    /// Lowest Common Multiple (LCM) together.
    ///
    /// Potentially more efficient than calling `gcd` and `lcm`
    /// individually for identical inputs.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(10.gcd_lcm(&4), (2, 20));
    /// assert_eq!(8.gcd_lcm(&9), (1, 72));
    /// ~~~
    #[inline]
    fn gcd_lcm(&self, other: &Self) -> (Self, Self) {
        (self.gcd(other), self.lcm(other))
    }

    /// Deprecated, use `is_multiple_of` instead.
    #[deprecated(note = "Please use is_multiple_of instead")]
    #[inline]
    fn divides(&self, other: &Self) -> bool {
        self.is_multiple_of(other)
    }

    /// Returns `true` if `self` is a multiple of `other`.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(9.is_multiple_of(&3), true);
    /// assert_eq!(3.is_multiple_of(&9), false);
    /// ~~~
    fn is_multiple_of(&self, other: &Self) -> bool;

    /// Returns `true` if the number is even.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(3.is_even(), false);
    /// assert_eq!(4.is_even(), true);
    /// ~~~
    fn is_even(&self) -> bool;

    /// Returns `true` if the number is odd.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(3.is_odd(), true);
    /// assert_eq!(4.is_odd(), false);
    /// ~~~
    fn is_odd(&self) -> bool;

    /// Simultaneous truncated integer division and modulus.
    /// Returns `(quotient, remainder)`.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(( 8).div_rem( &3), ( 2,  2));
    /// assert_eq!(( 8).div_rem(&-3), (-2,  2));
    /// assert_eq!((-8).div_rem( &3), (-2, -2));
    /// assert_eq!((-8).div_rem(&-3), ( 2, -2));
    ///
    /// assert_eq!(( 1).div_rem( &2), ( 0,  1));
    /// assert_eq!(( 1).div_rem(&-2), ( 0,  1));
    /// assert_eq!((-1).div_rem( &2), ( 0, -1));
    /// assert_eq!((-1).div_rem(&-2), ( 0, -1));
    /// ~~~
    fn div_rem(&self, other: &Self) -> (Self, Self);

    /// Simultaneous floored integer division and modulus.
    /// Returns `(quotient, remainder)`.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(( 8).div_mod_floor( &3), ( 2,  2));
    /// assert_eq!(( 8).div_mod_floor(&-3), (-3, -1));
    /// assert_eq!((-8).div_mod_floor( &3), (-3,  1));
    /// assert_eq!((-8).div_mod_floor(&-3), ( 2, -2));
    ///
    /// assert_eq!(( 1).div_mod_floor( &2), ( 0,  1));
    /// assert_eq!(( 1).div_mod_floor(&-2), (-1, -1));
    /// assert_eq!((-1).div_mod_floor( &2), (-1,  1));
    /// assert_eq!((-1).div_mod_floor(&-2), ( 0, -1));
    /// ~~~
    fn div_mod_floor(&self, other: &Self) -> (Self, Self) {
        (self.div_floor(other), self.mod_floor(other))
    }

    /// Rounds up to nearest multiple of argument.
    ///
    /// # Notes
    ///
    /// For signed types, `a.next_multiple_of(b) = a.prev_multiple_of(b.neg())`.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(( 16).next_multiple_of(& 8),  16);
    /// assert_eq!(( 23).next_multiple_of(& 8),  24);
    /// assert_eq!(( 16).next_multiple_of(&-8),  16);
    /// assert_eq!(( 23).next_multiple_of(&-8),  16);
    /// assert_eq!((-16).next_multiple_of(& 8), -16);
    /// assert_eq!((-23).next_multiple_of(& 8), -16);
    /// assert_eq!((-16).next_multiple_of(&-8), -16);
    /// assert_eq!((-23).next_multiple_of(&-8), -24);
    /// ~~~
    #[inline]
    fn next_multiple_of(&self, other: &Self) -> Self
    where
        Self: Clone,
    {
        let m = self.mod_floor(other);
        self.clone()
            + if m.is_zero() {
                Self::zero()
            } else {
                other.clone() - m
            }
    }

    /// Rounds down to nearest multiple of argument.
    ///
    /// # Notes
    ///
    /// For signed types, `a.prev_multiple_of(b) = a.next_multiple_of(b.neg())`.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// assert_eq!(( 16).prev_multiple_of(& 8),  16);
    /// assert_eq!(( 23).prev_multiple_of(& 8),  16);
    /// assert_eq!(( 16).prev_multiple_of(&-8),  16);
    /// assert_eq!(( 23).prev_multiple_of(&-8),  24);
    /// assert_eq!((-16).prev_multiple_of(& 8), -16);
    /// assert_eq!((-23).prev_multiple_of(& 8), -24);
    /// assert_eq!((-16).prev_multiple_of(&-8), -16);
    /// assert_eq!((-23).prev_multiple_of(&-8), -16);
    /// ~~~
    #[inline]
    fn prev_multiple_of(&self, other: &Self) -> Self
    where
        Self: Clone,
    {
        self.clone() - self.mod_floor(other)
    }

    /// Decrements self by one.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// let mut x: i32 = 43;
    /// x.dec();
    /// assert_eq!(x, 42);
    /// ~~~
    fn dec(&mut self)
    where
        Self: Clone,
    {
        *self = self.clone() - Self::one()
    }

    /// Increments self by one.
    ///
    /// # Examples
    ///
    /// ~~~
    /// # use num_integer::Integer;
    /// let mut x: i32 = 41;
    /// x.inc();
    /// assert_eq!(x, 42);
    /// ~~~
    fn inc(&mut self)
    where
        Self: Clone,
    {
        *self = self.clone() + Self::one()
    }
}

/// Simultaneous integer division and modulus
#[inline]
pub fn div_rem<T: Integer>(x: T, y: T) -> (T, T) {
    x.div_rem(&y)
}
/// Floored integer division
#[inline]
pub fn div_floor<T: Integer>(x: T, y: T) -> T {
    x.div_floor(&y)
}
/// Floored integer modulus
#[inline]
pub fn mod_floor<T: Integer>(x: T, y: T) -> T {
    x.mod_floor(&y)
}
/// Simultaneous floored integer division and modulus
#[inline]
pub fn div_mod_floor<T: Integer>(x: T, y: T) -> (T, T) {
    x.div_mod_floor(&y)
}
/// Ceiled integer division
#[inline]
pub fn div_ceil<T: Integer>(x: T, y: T) -> T {
    x.div_ceil(&y)
}

/// Calculates the Greatest Common Divisor (GCD) of the number and `other`. The
/// result is always non-negative.
#[inline(always)]
pub fn gcd<T: Integer>(x: T, y: T) -> T {
    x.gcd(&y)
}
/// Calculates the Lowest Common Multiple (LCM) of the number and `other`.
#[inline(always)]
pub fn lcm<T: Integer>(x: T, y: T) -> T {
    x.lcm(&y)
}

/// Calculates the Greatest Common Divisor (GCD) and
/// Lowest Common Multiple (LCM) of the number and `other`.
#[inline(always)]
pub fn gcd_lcm<T: Integer>(x: T, y: T) -> (T, T) {
    x.gcd_lcm(&y)
}

impl<T> Integer for T
where
    T: PrimInt + Signed,
{
    /// Floored integer division
    fn div_floor(&self, other: &Self) -> Self {
        // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
        // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
        let (d, r) = self.div_rem(other);
        let zero = T::zero();
        if (r > zero && *other < zero) || (r < zero && *other > zero) {
            d - T::one()
        } else {
            d
        }
    }

    /// Floored integer modulo
    fn mod_floor(&self, other: &Self) -> Self {
        // Algorithm from [Daan Leijen. _Division and Modulus for Computer Scientists_,
        // December 2001](http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf)
        let r = *self % *other;
        let zero = T::zero();
        if (r > zero && *other < zero) || (r < zero && *other > zero) {
            r + *other
        } else {
            r
        }
    }

    /// Calculates the Greatest Common Divisor (GCD) of the number and
    /// `other`. The result is always non-negative.
    fn gcd(&self, other: &Self) -> Self {
        // Use Stein's algorithm
        let mut m = *self;
        let mut n = *other;
        if m == T::zero() || n == T::zero() {
            return (m | n).abs();
        }

        // find common factors of 2
        let shift = (m | n).trailing_zeros() as usize;

        // The algorithm needs positive numbers, but the minimum value
        // can't be represented as a positive one.
        // It's also a power of two, so the gcd can be
        // calculated by bitshifting in that case

        // Assuming two's complement, the number created by the shift
        // is positive for all numbers except gcd = abs(min value)
        // The call to .abs() causes a panic in debug mode
        if m == Self::min_value() || n == Self::min_value() {
            let intermediate = T::one() << shift;
            return intermediate.abs();
        }

        // guaranteed to be positive now, rest like unsigned algorithm
        m = m.abs();
        n = n.abs();

        // divide n and m by 2 until odd
        m = m >> m.trailing_zeros() as usize;
        n = n >> n.trailing_zeros() as usize;

        while m != n {
            if m > n {
                m = m - n;
                m = m >> m.trailing_zeros() as usize;
            } else {
                n = n - m;
                n = n >> n.trailing_zeros() as usize;
            }
        }
        m << shift
    }

    /// Calculates the Lowest Common Multiple (LCM) of the number and
    /// `other`.
    fn lcm(&self, other: &Self) -> Self {
        self.gcd_lcm(other).1
    }

    /// Calculates the Greatest Common Divisor (GCD) and
    /// Lowest Common Multiple (LCM) of the number and `other`.
    fn gcd_lcm(&self, other: &Self) -> (Self, Self) {
        if self.is_zero() && other.is_zero() {
            return (Self::zero(), Self::zero());
        }
        let gcd = self.gcd(other);
        // should not have to recalculate abs
        let lcm = (*self * (*other / gcd)).abs();
        (gcd, lcm)
    }

    /// Returns `true` if the number is a multiple of `other`.
    fn is_multiple_of(&self, other: &Self) -> bool {
        if other.is_zero() {
            return self.is_zero();
        }
        *self % *other == T::zero()
    }

    /// Returns `true` if the number is divisible by `2`
    fn is_even(&self) -> bool {
        (*self & T::one()) == T::zero()
    }

    /// Returns `true` if the number is not divisible by `2`
    fn is_odd(&self) -> bool {
        !self.is_even()
    }

    /// Simultaneous truncated integer division and modulus.
    fn div_rem(&self, other: &Self) -> (Self, Self) {
        (*self / *other, *self % *other)
    }
}
