use num_traits::{CheckedAdd, CheckedSub};

use super::Angle;

pub(super) trait UnitsAngle: Angle {
    type Units: CheckedAdd + CheckedSub;

    fn with_units(u: Self::Units) -> Result<Self, Self::NumErr>;
    fn units(self) -> Self::Units;
    fn max_units() -> Self::Units;
}

#[macro_export]
/// Implement addition and subtraction operations
/// on the `UnitsAngle` types
macro_rules! impl_angle_ops {
    ($t:ty) => {
        impl Add for $t {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                if let Some(sum) = self.checked_add(&rhs) {
                    return sum;
                }

                // the sum can overflow u32, so convert everything to u64
                let self_units = u64::from(self.units());
                let rhs_units = u64::from(rhs.units());
                let max = u64::from(Self::max_units());
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
