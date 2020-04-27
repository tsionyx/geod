//! The traits for an angle

use std::{convert::TryFrom, error::Error, str::FromStr};

use num_traits::{CheckedAdd, CheckedSub};

pub mod dd;
mod degree;
pub mod dms_dd;
mod errors;

pub use errors::AngleNotInRange;

#[allow(clippy::module_name_repetitions)]
/// Common terminology for angles
/// <https://en.wikipedia.org/wiki/Angle#Individual_angles>
pub trait AngleNames: Copy + PartialOrd {
    fn zero() -> Self;

    /// The angle made of perpendicular rays
    fn right() -> Self;

    /// The angle made of two exactly opposite direction
    fn straight() -> Self;

    /// The angle made of full circle (perigon)
    fn complete() -> Self;

    /// No angle
    fn is_zero(self) -> bool {
        self == Self::zero()
    }

    /// Is the angle sharp?
    fn is_acute(self) -> bool {
        self > Self::zero() && self < Self::right()
    }

    /// Are the lines perpendicular?
    fn is_right(self) -> bool {
        self == Self::right()
    }

    /// Is the angle blunt?
    fn is_obtuse(self) -> bool {
        self > Self::right() && self < Self::straight()
    }

    /// Is the angle forms a straight line?
    fn is_straight(self) -> bool {
        self == Self::straight()
    }

    /// Is the angle more than a straight line?
    fn is_reflex(self) -> bool {
        self > Self::straight() && self < Self::complete()
    }

    /// Is the angle full round?
    fn is_complete(self) -> bool {
        self == Self::complete()
    }
}

/// Angle with ordering, addition/subtraction operations and
/// the abilities to construct itself from a string or float number
pub trait Angle:
    AngleNames
    + Ord
    + CheckedAdd
    + CheckedSub
    + FromStr<Err = <Self as Angle>::ParseErr>
    + TryFrom<f64, Error = <Self as Angle>::NumErr>
{
    /// The error that can appear when representing some part of the angle with a number
    type NumErr: Error;
    /// The error that can appear while parsing the angle from a string
    type ParseErr: Error;

    /// Adjacent angle which sum to a right angle
    fn complement(self) -> Option<Self> {
        Self::right().checked_sub(&self)
    }

    /// Adjacent angle which sum to a straight angle
    fn supplement(self) -> Option<Self> {
        Self::straight().checked_sub(&self)
    }

    /// Adjacent angle which sum to a complete angle
    fn explement(self) -> Self {
        Self::complete()
            .checked_sub(&self)
            .expect("Current implementation stores angles <=360 degrees")
    }

    /// Difference between the angles by modulo independent of the order
    fn abs_diff(self, rhs: Self) -> Self {
        let diff = self.checked_sub(&rhs).or_else(|| rhs.checked_sub(&self));

        // difference should always be less than the maximum (considered valid) angle
        diff.expect("Difference is small enough to be valid angle")
    }

    /// Is the `other` angle differs by an exact multiple of a full turn
    fn turn_eq(self, mut other: Self) -> bool {
        while other >= Self::complete() {
            other = other - Self::complete();
        }

        self == other
    }

    /// Produce an error when the angles more than the right one are invalid
    fn obtuse_detected() -> Self::NumErr;

    /// Produce an error when the angles more than the straight one are invalid
    fn reflex_detected() -> Self::NumErr;
}

pub(super) trait UnitsAngle: Angle {
    type Units: CheckedAdd + CheckedSub;

    fn with_units(u: Self::Units) -> Result<Self, Self::NumErr>;
    fn units(self) -> Self::Units;

    fn max_units() -> Self::Units {
        Self::complete().units()
    }
}

#[macro_export]
/// Implement addition and subtraction operations
/// on the `UnitsAngle` types.
/// `$sum_t` should be able to hold a sum of any units
/// without the risk of overflow.
macro_rules! impl_angle_ops {
    ($t:ty: <$sum_t: ty) => {
        impl Add for $t {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                if let Some(sum) = self.checked_add(&rhs) {
                    return sum;
                }

                // the sum can overflow `Units`, so convert everything to $sum_t
                let self_units = <$sum_t>::from(self.units());
                let rhs_units = <$sum_t>::from(rhs.units());
                let max = <$sum_t>::from(Self::max_units());
                assert!(self_units <= max);
                assert!(rhs_units <= max);
                assert!(self_units + rhs_units > max);

                let sum_units = (self_units + rhs_units - max)
                    .try_into()
                    .expect("Less than max should be valid");
                Self::with_units(sum_units)
                    .expect("Wrapping sum around the max degree is always a valid degree")
            }
        }

        impl CheckedAdd for $t {
            fn checked_add(&self, rhs: &Self) -> Option<Self> {
                self.units()
                    .checked_add(rhs.units())
                    .filter(|&sum_units| sum_units <= Self::max_units())
                    .and_then(|units| Self::with_units(units).ok())
            }
        }

        impl Sub for $t {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self::Output {
                if let Some(diff) = self.checked_sub(&rhs) {
                    return diff;
                }

                let self_ = self.units();
                let rhs = rhs.units();
                assert!(self_ < rhs);

                let max = Self::max_units();

                let diff = max - (rhs - self_);
                Self::with_units(diff).expect("The diff is less than the max angle")
            }
        }

        impl CheckedSub for $t {
            fn checked_sub(&self, rhs: &Self) -> Option<Self> {
                self.units()
                    .checked_sub(rhs.units())
                    .and_then(|units| Self::with_units(units).ok())
            }
        }
    };
}
