use num_traits::{CheckedAdd, CheckedSub};

use super::Angle;

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

pub(super) fn parse_angle_re(is_ascii: bool, arc_seconds_fd: usize) -> String {
    let (deg, min, sec) = if is_ascii {
        ("\\*?", '\'', '"')
    } else {
        ("°", '′', '″')
    };

    format!(
        r#"(?x)                                 # enables verbose mode (to allow these comments)
        ^                                           # match the whole line from the start
        (?P<deg>[123]?\d{{1,2}})                        # mandatory degree VALUE (0..=399) - requires more validation!
        {}                                              # degree sign (can be mandatory or optional)
        (?:\x20?                                        # minutes and seconds group optionally started with the space
            (?P<min>[0-5]?\d)                               # minutes VALUE (0..=59)
            {}                                              # arcminute sign
            (?:\x20?                                        # seconds with the decimal fraction group optionally started with the space
                (?P<sec>[0-5]?\d)                               # whole seconds VALUE (0..=59)
                (?:                                             # fractions of arcsecond with the decimal dot
                    \.(?P<sec_fract>\d{{1,{precision}}})            # fractions of arcsecond VALUE (up to [precision] digits, 0..=99)
                )?                                              # fractions of arcsecond are optional
                {}                                              # arcsecond sign
            )?                                              # seconds are optional
        )?                                              # minutes and seconds are optional
        $                                           # match the whole line till the end
        "#,
        deg,
        min,
        sec,
        precision = arc_seconds_fd
    )
}
