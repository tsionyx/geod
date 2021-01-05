//! The angle implementation can be used to store and process either:
//!  - degrees with their decimal fractions with the micro (10<sup>-6</sup>) precision;
//!  - or DMS (degrees, minutes, seconds) with the centi (1/100-th) of arcsecond precision.
//!
//! Operands with the different representations can produce
//! approximate result on the operations of addition or subtraction.
//! But when using the same (DMS+DMS or Decimal+Decimal) representations,
//! the result is always accurate.

use std::{
    borrow::Cow,
    convert::{TryFrom, TryInto},
    fmt,
    ops::{Add, Sub},
    str::FromStr,
};

use lazy_static::lazy_static;
use num_traits::{CheckedAdd, CheckedSub};
use regex::Regex;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{
    impl_angle_ops, impl_angle_traits, impl_conv_traits, try_from_tuples_and_arrays,
    utils::{div_mod, pow_10, RoundDiv, StripChar},
};

use super::{
    degree::{
        parse_dms_re, ARC_MINUTE_SIGN, ARC_SECOND_SIGN, DEGREE_SIGN, FULL_TURN_DEG, HALF_TURN_DEG,
        MAX_DEGREE, MINUTES_IN_DEGREE, QUARTER_TURN_DEG, SECONDS_IN_MINUTE,
    },
    errors::{AngleNotInRange, ParseAngleError},
    Angle, AngleNames, UnitsAngle,
};

/// The implementation can accurately store _either_ decimal fractions of the degree
/// (with the 10<sup>-6</sup> degrees precision)
/// _or_ degree, minute, second (with the 10<sup>-2</sup> arcsecond precision).
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Default, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AccurateDegree {
    units: u32,
}

impl UnitsAngle for AccurateDegree {
    type Units = u32;

    fn with_units(units: u32) -> Result<Self, AngleNotInRange> {
        if units > Self::max_units() {
            return Err(AngleNotInRange::Degrees);
        }

        Ok(Self { units })
    }

    fn units(self) -> Self::Units {
        self.units
    }

    fn max_units() -> u32 {
        // TODO: recursive stack overflow for the default impl
        Self::units_in_deg() * (u32::from(MAX_DEGREE))
    }
}

impl_angle_traits!(AccurateDegree);
impl_angle_ops!(AccurateDegree: <u64);
impl_conv_traits!(AccurateDegree, micro_deg_in_deg, deg_min_sec_cas, HUNDRED);

impl AccurateDegree {
    const fn units_in_deg() -> u32 {
        // The optimum number (N) should obey the following rules:
        // - N <= 11_930_464 (~= 2^32 / 360)
        //   to allow to store the whole 360 degrees (one turn) in a 32-bit integer
        // - N is divisible by `10^x` for maximum `x` possible
        //   (to store decimal degrees with the highest precision).
        //   From the first rule, x <= 7.
        // - N is divisible by `3600 * 10^y` for maximum `y` possible
        //   (to store the arc seconds and their decimal fractions efficiently).
        //   From the first rule, y <= 3.
        // - the two precisions metric (`10^x` and `3600 * 10^y`) should not differ significantly
        //   to allow a user to switch the units easily.
        //
        // The two optimal solutions are:
        //  1) `x = 5, y = 3, N = 3.6 * 10^6`. Allow to get precise values for 10^-3 arc seconds OR 10^-5 degrees.
        //  Therefore, precision for the decimal and sexagesimal representation, differs in 36 times.
        //  2) `x = 6, y = 2, N = 9 * 10^6`. Allow to get precise values for 10^-2 arc seconds OR 10^-6 degrees.
        //  Precision for the decimal and sexagesimal representation, differs in 3.6 times.
        9_000_000
    }

    // the number of degree's decimal digits
    const PRECISION: u8 = 6;

    // the number of arcseconds's decimal digits
    const SECONDS_FD: usize = 2;
    const HUNDRED: u32 = pow_10(Self::SECONDS_FD);

    const fn micro_deg_in_deg() -> u32 {
        pow_10(Self::PRECISION as usize)
    }

    fn micro_deg_to_unit_coef() -> u32 {
        let (quot, rem) = div_mod(Self::units_in_deg(), Self::micro_deg_in_deg());
        // should be divided without remainder
        assert_eq!(rem, 0);
        quot
    }

    const fn cas_in_deg() -> u32 {
        let sec_in_min = SECONDS_IN_MINUTE as u32;
        let min_in_deg = MINUTES_IN_DEGREE as u32;
        let sec_in_deg = sec_in_min * min_in_deg;
        Self::HUNDRED * sec_in_deg
    }

    fn cas_to_unit_coef() -> u32 {
        let (quot, rem) = div_mod(Self::units_in_deg(), Self::cas_in_deg());
        // should be divided without remainder
        assert_eq!(rem, 0);
        quot
    }

    fn with_deg_and_fraction(degrees: u16, fraction: u32) -> Result<Self, AngleNotInRange> {
        let valid_degrees = 0..=MAX_DEGREE;
        if !valid_degrees.contains(&degrees) {
            return Err(AngleNotInRange::Degrees);
        };

        let max_fraction_units = Self::micro_deg_in_deg();

        let valid_fraction = if degrees == MAX_DEGREE {
            0..1
        } else {
            0..max_fraction_units
        };

        if !valid_fraction.contains(&fraction) {
            return Err(AngleNotInRange::MicroDegrees);
        }

        let total_micro = u64::from(degrees) * u64::from(max_fraction_units) + u64::from(fraction);
        let total_micro = u32::try_from(total_micro).map_err(|_| AngleNotInRange::Degrees)?;

        let units = Self::micro_deg_to_unit_coef() * total_micro;
        Ok(Self { units })
    }

    /// Degree, minute, second, centisecond.
    ///
    /// [Read more](https://en.wikipedia.org/wiki/Minute_and_second_of_arc)
    ///
    /// # Errors
    /// When some part of the angle is out of scope
    /// (e.g. minutes > 60 or degree > 360), the `AngleNotInRange` returned.
    pub fn with_dms(
        degree: u16,
        minutes: u8,
        seconds: u8,
        centi_seconds: u8,
    ) -> Result<Self, AngleNotInRange> {
        Self::check_dms(degree, minutes, seconds, centi_seconds)?;

        // prevent further multiplication overflow by extending precision
        let centi = u64::from(Self::HUNDRED);
        let sec_in_min = u64::from(SECONDS_IN_MINUTE);
        let min_in_deg = u64::from(MINUTES_IN_DEGREE);

        let total_minutes = u64::from(degree) * min_in_deg + u64::from(minutes);
        let total_seconds = (total_minutes * sec_in_min) + u64::from(seconds);
        let total_cas = (total_seconds * centi) + u64::from(centi_seconds);

        let total_cas = u32::try_from(total_cas).map_err(|_| AngleNotInRange::Degrees)?;
        Self::with_units(Self::cas_to_unit_coef() * total_cas)
    }

    fn check_dms(
        degree: u16,
        minutes: u8,
        seconds: u8,
        centi_seconds: u8,
    ) -> Result<(), AngleNotInRange> {
        let valid_degrees = 0..=MAX_DEGREE;
        if !valid_degrees.contains(&degree) {
            return Err(AngleNotInRange::Degrees);
        }

        let (valid_minutes, valid_seconds, valid_centi) = if degree == MAX_DEGREE {
            (0..1, 0..1, 0..1)
        } else {
            (
                0..MINUTES_IN_DEGREE,
                0..SECONDS_IN_MINUTE,
                0..(Self::HUNDRED as u8),
            )
        };

        if !valid_minutes.contains(&minutes) {
            return Err(AngleNotInRange::ArcMinutes);
        }

        if !valid_seconds.contains(&seconds) {
            return Err(AngleNotInRange::ArcSeconds);
        }

        if !valid_centi.contains(&centi_seconds) {
            return Err(AngleNotInRange::ArcCentiSeconds);
        }

        Ok(())
    }

    /// The whole number of degrees in the angle
    pub const fn degrees(self) -> u16 {
        let degrees = self.units / Self::units_in_deg();
        degrees as u16
    }

    /// The microdegrees (10<sup>-6</sup> degrees) component of the angle
    pub fn deg_fract(self) -> u32 {
        let fract_units = self.units % Self::units_in_deg();
        fract_units.div_round(Self::micro_deg_to_unit_coef())
    }

    /// The arc minutes component of the angle.
    pub fn arc_minutes(self) -> u8 {
        self.dms_parts(true).1
    }

    /// The arc seconds component of the angle.
    pub fn arc_seconds(self) -> u8 {
        self.dms_parts(true).2
    }

    /// The centi arc seconds (1/100-th of the arc second) component of the angle.
    ///
    /// Use with caution! The overflow of `0.999_999` degrees
    /// intentionally handled incorrectly to keep the [`degrees`](#method.degrees) value valid.
    /// To get the accurate value in such a boundary condition,
    /// use [`deg_min_sec_cas`](#method.deg_min_sec_cas) instead.
    pub fn centi_arc_seconds(self) -> u8 {
        self.dms_parts(true).3
    }

    /// If `keep_degrees` is false, overflow in minutes will be added to degrees
    fn dms_parts(self, keep_degrees: bool) -> (u16, u8, u8, u8) {
        let sec_in_min = u32::from(SECONDS_IN_MINUTE);
        let min_in_deg = u32::from(MINUTES_IN_DEGREE);

        let total_cas = self.units.div_round(Self::cas_to_unit_coef());
        let (total_seconds, cas) = div_mod(total_cas, Self::HUNDRED);
        let (total_minutes, sec) = div_mod(total_seconds, sec_in_min);
        let (deg, minutes) = div_mod(total_minutes, min_in_deg);

        let deg = deg.try_into().expect("Overflow in degrees");
        let minutes = minutes.try_into().expect("Overflow in minutes");
        let sec = sec.try_into().expect("Overflow in seconds");
        let cas = cas.try_into().expect("Overflow in centi seconds");

        let decimal_deg = self.degrees();
        if deg > decimal_deg {
            assert_eq!(deg, decimal_deg + 1);
            assert_eq!(minutes, 0);
            assert_eq!(sec, 0);
            assert_eq!(cas, 0);
            if keep_degrees {
                // subtract minimal DMS to prevent overflow in degrees
                let min_dms = Self::with_dms(0, 0, 0, 1).expect("Min DMS is valid");
                // `match_degrees=false` to prevent any possibility of the recursive call
                return (self - min_dms).dms_parts(false);
            }
        }

        (deg, minutes, sec, cas)
    }

    /// Parts of the angle as in the DMS scheme.
    ///
    /// There is a corner case when the degree part returned is not the same as the result of [`degrees()`](#method.degrees):
    /// when the angle's value is too close to a whole degree
    /// in terms of internal representation, but still slightly less than it.
    ///
    /// However, in terms of the DMS, it is already represented as a whole degree
    /// since the distance is too small to be represented in DMS scheme.
    ///
    ///```
    /// # use geod::AccurateDegree;
    /// # use std::convert::TryFrom;
    /// let a = AccurateDegree::try_from(35.999999).unwrap();
    ///
    /// assert_eq!(a.degrees(), 35);
    /// assert_eq!(a.arc_minutes(), 59);
    /// assert_eq!(a.arc_seconds(), 59);
    /// assert_eq!(a.centi_arc_seconds(), 99);
    ///
    /// // the value is closer to 36 than to 35 59'59.99"
    /// // and therefore rounds up
    /// assert_eq!(a.deg_min_sec_cas(), (36, 0, 0, 0));
    /// ```
    pub fn deg_min_sec_cas(self) -> (u16, u8, u8, u8) {
        self.dms_parts(false)
    }

    /// Since the DMS and decimal representation have different granularity,
    /// when comparing one with the other we should consider a gap
    /// of the half of larger granularity.
    pub fn almost_equal(self, rhs: Self) -> bool {
        let gran1 = Self::micro_deg_to_unit_coef();
        let gran2 = Self::cas_to_unit_coef();

        let max_error = gran1.max(gran2) >> 1;
        self.abs_diff(rhs) <= Self { units: max_error }
    }
}

lazy_static! {
    static ref RE_UNICODE: Regex = Regex::new(&parse_dms_re(false, AccurateDegree::SECONDS_FD))
        .expect("Unicode regex is valid");
    static ref RE_ASCII: Regex =
        Regex::new(&parse_dms_re(true, AccurateDegree::SECONDS_FD)).expect("ASCII regex is valid");
}

impl TryFrom<(u16, u8, u8, u16)> for AccurateDegree {
    type Error = AngleNotInRange;

    fn try_from(value: (u16, u8, u8, u16)) -> Result<Self, Self::Error> {
        let (deg, min, sec, centi) = value;
        // Why not `u8` for the first? It is a workaround to allow to construct coordinates.
        let centi = centi
            .try_into()
            .map_err(|_| AngleNotInRange::ArcCentiSeconds)?;
        Self::with_dms(deg, min, sec, centi)
    }
}

impl TryFrom<[u16; 4]> for AccurateDegree {
    type Error = AngleNotInRange;

    fn try_from(value: [u16; 4]) -> Result<Self, Self::Error> {
        let [deg, min, sec, centi] = value;
        let min = u8::try_from(min).map_err(|_| AngleNotInRange::ArcMinutes)?;
        let sec = u8::try_from(sec).map_err(|_| AngleNotInRange::ArcSeconds)?;
        let centi = u8::try_from(centi).map_err(|_| AngleNotInRange::ArcCentiSeconds)?;
        Self::with_dms(deg, min, sec, centi)
    }
}

try_from_tuples_and_arrays!((u16, u8, u8, u16; max=u16) -> <AccurateDegree, AngleNotInRange>);

#[cfg(test)]
mod tests {
    use std::{f64, mem::size_of};

    use super::*;

    #[test]
    fn accurate_angle_is_32_bits() {
        assert_eq!(size_of::<AccurateDegree>(), 4)
    }

    #[test]
    fn default() {
        let zero_angle = AccurateDegree::default();
        assert!(zero_angle.is_zero());

        assert_eq!(zero_angle.degrees(), 0);
        assert_eq!(zero_angle.deg_fract(), 0);
        assert_eq!(zero_angle.units(), 0);

        assert_eq!(zero_angle.arc_minutes(), 0);
        assert_eq!(zero_angle.arc_seconds(), 0);
        assert_eq!(zero_angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn max_valid_value() {
        let north_pole: AccurateDegree = 180.try_into().unwrap();
        assert!(north_pole.is_straight());
        assert_eq!(north_pole.degrees(), 180);
        assert_eq!(north_pole.deg_fract(), 0);
        assert_eq!(north_pole.units(), 1_620_000_000);

        assert_eq!(north_pole.arc_minutes(), 0);
        assert_eq!(north_pole.arc_seconds(), 0);
        assert_eq!(north_pole.centi_arc_seconds(), 0);

        let north_pole2: AccurateDegree = AccurateDegree::with_dms(180, 0, 0, 0).unwrap();
        assert_eq!(north_pole2, north_pole);
    }

    /// <https://en.wikipedia.org/wiki/Tropic_of_Capricorn>
    #[test]
    fn intermediate() {
        let polar_circle = AccurateDegree::with_deg_and_fraction(66, 563_334).unwrap();
        assert!(polar_circle.is_acute());
        assert_eq!(polar_circle.degrees(), 66);
        assert_eq!(polar_circle.deg_fract(), 563_334);
        let as_float: f64 = polar_circle.into();
        assert!((as_float - 66.563_334).abs() < f64::EPSILON);

        assert_eq!(polar_circle.arc_minutes(), 33);
        assert_eq!(polar_circle.arc_seconds(), 48);
        assert_eq!(polar_circle.centi_arc_seconds(), 0);
    }

    #[test]
    fn bigger_than_straight_is_valid() {
        let angle = AccurateDegree::with_deg_and_fraction(200, 0).unwrap();
        assert!(angle.is_reflex());
        assert_eq!(angle.degrees(), 200);
        assert_eq!(angle.deg_fract(), 0);
        let as_float: f64 = angle.into();
        assert!((as_float - 200.0).abs() < f64::EPSILON);

        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn bigger_than_straight_dms() {
        let angle = AccurateDegree::with_dms(181, 0, 2, 11).unwrap();
        assert!(angle.is_reflex());
        assert_eq!(angle.degrees(), 181);

        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 2);
        assert_eq!(angle.centi_arc_seconds(), 11);
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn bigger_than_complete() {
        let _a = AccurateDegree::with_deg_and_fraction(365, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn bigger_than_complete_degree() {
        let _a = AccurateDegree::with_dms(361, 0, 0, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcMinutes")]
    fn bigger_than_complete_minute() {
        let _a = AccurateDegree::with_dms(360, 5, 0, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcSeconds")]
    fn bigger_than_complete_second() {
        let _a = AccurateDegree::with_dms(360, 0, 2, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcCentiSeconds")]
    fn bigger_than_complete_milli_second() {
        let _a = AccurateDegree::with_dms(360, 0, 0, 1).unwrap();
    }

    #[test]
    #[should_panic(expected = "MicroDegrees")]
    fn bigger_than_complete_minimum_fraction() {
        let _a = AccurateDegree::with_deg_and_fraction(360, 1).unwrap();
    }

    #[test]
    fn complete() {
        let angle = AccurateDegree::with_deg_and_fraction(360, 0).unwrap();
        assert!(angle.is_complete());
        assert_eq!(angle.degrees(), 360);
        assert_eq!(angle.deg_fract(), 0);
        let as_float: f64 = angle.into();
        assert!((as_float - 360.0).abs() < f64::EPSILON);

        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    #[should_panic(expected = "ArcMinutes")]
    fn bad_minutes() {
        let _a = AccurateDegree::with_dms(30, 60, 60, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcSeconds")]
    fn bad_seconds() {
        let _a = AccurateDegree::with_dms(30, 59, 60, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcSeconds")]
    fn bad_seconds_2() {
        let _a = AccurateDegree::with_dms(30, 59, 100, 0).unwrap();
    }

    #[test]
    fn good_milli_seconds() {
        let angle = AccurateDegree::with_dms(30, 59, 0, 99).unwrap();
        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 99);
    }

    #[test]
    #[should_panic(expected = "ArcCentiSeconds")]
    fn bad_milli_seconds() {
        let _a = AccurateDegree::with_dms(30, 59, 0, 100).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcCentiSeconds")]
    fn bad_milli_seconds_2() {
        let _a = AccurateDegree::with_dms(30, 59, 0, 150).unwrap();
    }

    #[test]
    fn from_f64() {
        let angle = AccurateDegree::try_from(23.499_999).unwrap();
        assert!(angle.is_acute());

        let angle2 = AccurateDegree::with_deg_and_fraction(23, 499_999).unwrap();
        assert_eq!(angle, angle2);

        let as_float = Into::<f64>::into(angle);
        assert!((as_float - 23.499_999).abs() < f64::EPSILON);
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn from_f64_deg_overflow() {
        let _a = AccurateDegree::try_from(425.0).unwrap();
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn from_f64_wrap_around_u16() {
        let angle: AccurateDegree = 65566.5.try_into().unwrap();

        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 30);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);

        let as_float: f64 = angle.into();
        assert!((as_float - 65566.5).abs() < f64::EPSILON);
    }

    #[test]
    fn from_u16() {
        let angle: AccurateDegree = 300.try_into().unwrap();
        assert!(angle.is_reflex());

        assert_eq!(angle.degrees(), 300);
        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_u8() {
        let angle = AccurateDegree::with_deg_and_fraction(108, 0).unwrap();
        assert!(angle.is_obtuse());

        let angle2 = 108.try_into().unwrap();
        assert_eq!(angle, angle2);
    }

    #[test]
    fn from_pair() {
        let angle: AccurateDegree = (7, 59).try_into().unwrap();
        assert_eq!(angle.degrees(), 7);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_triple() {
        let angle: AccurateDegree = (117, 59, 3).try_into().unwrap();
        assert_eq!(angle.degrees(), 117);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_quadruple() {
        let angle: AccurateDegree = (317, 59, 3, 90).try_into().unwrap();
        assert_eq!(angle.degrees(), 317);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.centi_arc_seconds(), 90);
    }

    #[test]
    fn from_ar2() {
        let angle: AccurateDegree = [40, 15].try_into().unwrap();
        assert_eq!(angle.degrees(), 40);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_ar3() {
        let angle: AccurateDegree = [320, 15, 8].try_into().unwrap();
        assert_eq!(angle.degrees(), 320);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 8);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_ar4() {
        let angle: AccurateDegree = [120, 15, 8, 36].try_into().unwrap();
        assert_eq!(angle.degrees(), 120);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 8);
        assert_eq!(angle.centi_arc_seconds(), 36);
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn from_int_overflow() {
        let _angle: AccurateDegree = [500, 15, 8, 36].try_into().unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcMinutes")]
    fn from_ar4_overflow() {
        let _angle: AccurateDegree = [120, 300, 8, 36].try_into().unwrap();
    }

    #[test]
    fn good_fraction_minus_one_is_overflow() {
        let angle = AccurateDegree::with_deg_and_fraction(30, 999_999).unwrap();
        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.deg_fract(), 999_999);
        let as_float: f64 = angle.into();
        assert!((as_float - 30.999_999).abs() < f64::EPSILON);

        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 59);
        // slightly less than the real value, but the degrees is still 30
        assert_eq!(angle.centi_arc_seconds(), 99);

        let parts_with_the_same_degree_value = angle.dms_parts(true);
        assert_eq!(parts_with_the_same_degree_value, (30, 59, 59, 99)); // not really correct

        let parts_with_the_increased_degree = angle.deg_min_sec_cas();
        // this value is closer ...
        assert_eq!(parts_with_the_increased_degree, (31, 0, 0, 0));
        // but inconsistent with the `degrees()` method
        assert!(parts_with_the_increased_degree.0 > angle.degrees())
    }

    #[test]
    fn good_fraction_minus_two() {
        let angle = AccurateDegree::with_deg_and_fraction(30, 999_998).unwrap();
        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.deg_fract(), 999_998);
        let as_float: f64 = angle.into();
        assert!((as_float - 30.999_998).abs() < f64::EPSILON);

        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 59);
        assert_eq!(angle.centi_arc_seconds(), 99);
    }

    #[test]
    #[should_panic(expected = "MicroDegrees")]
    fn bad_fraction() {
        let _a = AccurateDegree::with_deg_and_fraction(30, 10_000_000).unwrap();
    }

    #[test]
    #[should_panic(expected = "MicroDegrees")]
    fn bad_fraction_2() {
        let _a = AccurateDegree::with_deg_and_fraction(30, 15_000_000).unwrap();
    }

    #[test]
    fn test_very_small_angles() {
        for f in 0..1000 {
            let angle = AccurateDegree::with_deg_and_fraction(0, f).unwrap();
            assert_eq!(angle.degrees(), 0);
            assert_eq!(angle.deg_fract(), f);
            assert_eq!(angle.units(), f * 9);
        }
    }

    #[test]
    #[ignore]
    fn test_first_degree_every_fraction_with_step_1() {
        let mut prev = None;
        for f in 0..1_000_000 {
            let angle = AccurateDegree::with_deg_and_fraction(0, f).unwrap();
            assert_eq!(angle.degrees(), 0);
            assert_eq!(angle.deg_fract(), f);

            let as_float: f64 = angle.into();
            assert!((as_float - f64::from(f) / 1_000_000_f64).abs() < f64::EPSILON);

            if let Some(prev) = prev {
                assert!(angle > prev);
                assert_eq!(
                    angle - prev,
                    AccurateDegree::with_deg_and_fraction(0, 1).unwrap()
                );
            }

            prev = Some(angle);
        }
    }

    fn round_trip(deg: u16, min: u8, sec: u8, centi_sec: u8) {
        eprintln!("\n\n================");
        let angle = AccurateDegree::with_dms(deg, min, sec, centi_sec).unwrap();
        dbg!(&angle);

        assert_eq!(angle.degrees(), deg);
        assert_eq!(angle.arc_minutes(), min);
        assert_eq!(angle.arc_seconds(), sec);
        assert_eq!(angle.centi_arc_seconds(), centi_sec);
    }

    #[test]
    #[ignore]
    fn test_round_trip_conversion() {
        for &deg in &[0, 1, 2, 179, 180, 358, 359] {
            for min in 0..60 {
                if (10..50).contains(&min) {
                    continue;
                }
                for sec in 0..60 {
                    if (10..50).contains(&sec) {
                        continue;
                    }
                    for centi in 0..100 {
                        round_trip(deg, min, sec, centi)
                    }
                }
            }
        }

        round_trip(180, 0, 0, 0);
    }

    #[test]
    fn dms_almost_int() {
        let angle = AccurateDegree::with_dms(156, 59, 59, 99).unwrap();

        assert_eq!(angle.degrees(), 156);
        assert_eq!(angle.deg_fract(), 999_997);
    }

    #[test]
    fn print_fraction() {
        let d = AccurateDegree::with_deg_and_fraction(60, 546_718).unwrap();
        assert_eq!(d.to_string(), "60.546718°")
    }

    #[test]
    fn print_fraction_almost_integer() {
        let almost_20 = AccurateDegree::try_from(20).unwrap()
            - AccurateDegree::with_deg_and_fraction(0, 1).unwrap();

        assert_eq!(almost_20.to_string(), "19.999999°")
    }

    #[test]
    fn print_fraction_very_small() {
        let almost_zero = AccurateDegree::with_deg_and_fraction(0, 1).unwrap();
        assert_eq!(almost_zero.to_string(), "0.000001°")
    }

    #[test]
    fn print_zero() {
        let d = AccurateDegree::default();
        assert_eq!(d.to_string(), "0°")
    }

    #[test]
    fn print_zero_as_dms() {
        let d = AccurateDegree::default();
        let s = format!("{:#}", d);
        assert_eq!(s, "0°")
    }

    #[test]
    fn print_right() {
        let d = AccurateDegree::try_from(90).unwrap();
        assert_eq!(d.to_string(), "90°")
    }

    #[test]
    fn print_right_as_dms() {
        let d: AccurateDegree = 90.try_into().unwrap();
        let s = format!("{:#}", d);
        assert_eq!(s, "90°")
    }

    #[test]
    fn print_fraction_as_dms() {
        let d = AccurateDegree::with_deg_and_fraction(60, 546_718).unwrap();
        let s = format!("{:#}", d);
        assert_eq!(s, "60°32′48.18″")
    }

    #[test]
    fn print_fraction_as_dms_without_milli() {
        for f in 0..3 {
            let d = AccurateDegree::with_deg_and_fraction(60, 546_666 + f).unwrap();
            let s = format!("{:#}", d);
            assert_eq!(s, "60°32′48″");
        }
    }

    #[test]
    fn print_fraction_as_dms_without_seconds() {
        for f in 0..3 {
            let d = AccurateDegree::with_deg_and_fraction(60, 533_332 + f).unwrap();
            let s = format!("{:#}", d);
            assert_eq!(s, "60°32′");
        }
    }

    #[test]
    fn print_overflow_fraction_as_dms() {
        let d = AccurateDegree::with_deg_and_fraction(59, 999_999).unwrap();
        let s = format!("{:#}", d);
        assert_eq!(s, "60°")
    }

    #[test]
    fn add() {
        let first = AccurateDegree::with_dms(118, 51, 27, 95).unwrap();
        let second = AccurateDegree::with_dms(47, 38, 19, 75).unwrap();
        let sum = first + second;

        assert_eq!(sum.degrees(), 166);
        assert_eq!(sum.arc_minutes(), 29);
        assert_eq!(sum.arc_seconds(), 47);
        assert_eq!(sum.centi_arc_seconds(), 70);
    }

    #[test]
    fn add_minimal_overflow() {
        let max = AccurateDegree::complete();
        let min = AccurateDegree::with_deg_and_fraction(0, 1).unwrap();

        let add_res = max.checked_add(&min);
        assert!(add_res.is_none());

        // wrapped around
        assert_eq!(
            max + min,
            AccurateDegree::with_deg_and_fraction(0, 1).unwrap()
        );
    }

    #[test]
    fn add_with_wrapping() {
        let first = AccurateDegree::with_dms(256, 18, 0, 60).unwrap();
        let second = (153, 4, 0, 0).try_into().unwrap();

        // wrapped around
        assert!((first + second).almost_equal((49, 22, 0, 60).try_into().unwrap()));
    }

    #[test]
    fn add_no_overflow() {
        let max = AccurateDegree::straight();
        let min = AccurateDegree::with_deg_and_fraction(0, 1).unwrap();

        let res = max
            .checked_sub(&min)
            .and_then(|sub| sub.checked_add(&min))
            .unwrap();
        assert!(res.is_straight());
    }

    #[test]
    fn summing_dms_does_not_accumulate_errors() {
        let min = AccurateDegree::with_dms(0, 0, 0, 1).unwrap();

        let mut acc = AccurateDegree::zero();

        for _ in 0..10 {
            acc = acc + min;
        }

        assert_eq!(acc.centi_arc_seconds(), 10);
    }

    #[test]
    fn sub() {
        let first = AccurateDegree::with_dms(318, 51, 27, 96).unwrap();
        let second = AccurateDegree::with_dms(47, 38, 19, 74).unwrap();
        let sum = first - second;

        assert_eq!(sum.degrees(), 271);
        assert_eq!(sum.arc_minutes(), 13);
        assert_eq!(sum.arc_seconds(), 8);
        assert_eq!(sum.centi_arc_seconds(), 22);
    }

    #[test]
    fn sub_underflow() {
        let first = AccurateDegree::with_dms(47, 38, 19, 74).unwrap();
        let second = AccurateDegree::with_dms(47, 38, 19, 75).unwrap();
        let sum = first.checked_sub(&second);
        assert!(sum.is_none());
    }

    #[test]
    fn sub_with_zero_res() {
        let first = AccurateDegree::with_dms(47, 38, 19, 74).unwrap();
        let second = AccurateDegree::with_dms(47, 38, 19, 74).unwrap();
        let sum = first.checked_sub(&second).unwrap();
        assert!(sum.is_zero());
    }

    #[test]
    fn complementary() {
        let angle: AccurateDegree = 79.888_889.try_into().unwrap();
        dbg!(angle.units);
        let comp = angle.complement().unwrap();
        assert_eq!(comp.degrees(), 10);
        assert_eq!(comp.deg_fract(), 111_111);
    }

    #[test]
    fn complementary_dms() {
        let angle = AccurateDegree::with_dms(47, 38, 19, 74).unwrap();
        let supp = angle.complement().unwrap();
        assert_eq!(supp.degrees(), 42);
        assert_eq!(supp.arc_minutes(), 21);
        assert_eq!(supp.arc_seconds(), 40);
        assert_eq!(supp.centi_arc_seconds(), 26);
    }

    #[test]
    fn complement_of_obtuse_undefined() {
        let angle = AccurateDegree::with_dms(117, 38, 19, 74).unwrap();
        assert!(angle.complement().is_none());
    }

    #[test]
    fn supplementary() {
        let angle: AccurateDegree = 30.98765.try_into().unwrap();
        let supp = angle.supplement().unwrap();
        assert_eq!(supp.degrees(), 149);
        assert_eq!(supp.deg_fract(), 12_350);
    }

    #[test]
    fn supplementary_dms() {
        let angle = AccurateDegree::with_dms(157, 44, 3, 11).unwrap();
        let supp = angle.supplement().unwrap();
        assert_eq!(supp.degrees(), 22);
        assert_eq!(supp.arc_minutes(), 15);
        assert_eq!(supp.arc_seconds(), 56);
        assert_eq!(supp.centi_arc_seconds(), 89);
    }

    #[test]
    fn supplement_of_reflex_undefined() {
        let angle = AccurateDegree::with_dms(190, 38, 19, 74).unwrap();
        assert!(angle.supplement().is_none());
    }

    #[test]
    fn explementary() {
        let angle: AccurateDegree = 130.98765.try_into().unwrap();
        let exp = angle.explement();
        assert_eq!(exp.degrees(), 229);
        assert_eq!(exp.deg_fract(), 12_350);
    }

    #[test]
    fn explementary_dms() {
        let angle = AccurateDegree::with_dms(275, 44, 3, 11).unwrap();
        let exp = angle.explement();
        assert_eq!(exp.degrees(), 84);
        assert_eq!(exp.arc_minutes(), 15);
        assert_eq!(exp.arc_seconds(), 56);
        assert_eq!(exp.centi_arc_seconds(), 89);
    }

    #[test]
    fn explement_of_obtuse_is_reflex() {
        let angle = AccurateDegree::with_dms(95, 38, 19, 74).unwrap();
        let exp = angle.explement();
        assert_eq!(exp.degrees(), 264);
        assert_eq!(exp.arc_minutes(), 21);
        assert_eq!(exp.arc_seconds(), 40);
        assert_eq!(exp.centi_arc_seconds(), 26);
    }
}

#[cfg(test)]
mod parse_tests {
    use super::*;

    #[test]
    fn simple_integer() {
        let s = "54";
        let angle: AccurateDegree = s.parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.deg_fract(), 0);

        assert_eq!(angle, AccurateDegree::with_dms(54, 0, 0, 0).unwrap());
    }

    #[test]
    fn simple_integer_with_degree_sign() {
        let s = "54°";
        let angle: AccurateDegree = s.parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.deg_fract(), 0);

        assert_eq!(angle, AccurateDegree::with_dms(54, 0, 0, 0).unwrap());
    }

    #[test]
    fn simple_decimal() {
        let angle: AccurateDegree = "54.145".parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.deg_fract(), 145_000);
    }

    #[test]
    fn simple_decimal_with_degree_sign() {
        let angle: AccurateDegree = "54.145°".parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.deg_fract(), 145_000);
    }

    #[test]
    fn too_precise_truncation() {
        let angle: AccurateDegree = "54.123456789".parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.deg_fract(), 123_457);
    }

    #[test]
    fn round_down_more_than_6_digits() {
        let angle: AccurateDegree = "18.9999994°".parse().unwrap();
        assert_eq!(angle.degrees(), 18);
        assert_eq!(angle.deg_fract(), 999_999);
    }

    #[test]
    fn round_up_more_than_7_digits() {
        let angle: AccurateDegree = "18.99999995°".parse().unwrap();
        assert_eq!(angle.degrees(), 19);
        assert_eq!(angle.deg_fract(), 0);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn bad_float() {
        let _angle: AccurateDegree = "54.123456.789".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn bad_negative() {
        let _angle: AccurateDegree = "-54.12".parse().unwrap();
    }

    #[test]
    fn big_but_valid() {
        let angle: AccurateDegree = "278.123456".parse().unwrap();
        assert_eq!(angle.degrees(), 278);
        assert_eq!(angle.deg_fract(), 123_456);
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn bad_too_big_for_angle() {
        let _angle: AccurateDegree = "364.123456".parse().unwrap();
    }

    #[test]
    fn simple_deg() {
        let angle: AccurateDegree = "28°".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min() {
        let angle: AccurateDegree = "28°15′".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec() {
        let angle: AccurateDegree = "28°05′33″".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 5);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec_cas() {
        let angle: AccurateDegree = "98°15′33.15″".parse().unwrap();
        assert_eq!(angle.degrees(), 98);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    fn uneven_digits_deg_min_sec_cas() {
        let angle: AccurateDegree = "128°4′16.15″".parse().unwrap();
        assert_eq!(angle.degrees(), 128);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    fn single_digit_deg_min_sec_cas() {
        let angle: AccurateDegree = "1°2′3.4″".parse().unwrap();
        assert_eq!(angle.degrees(), 1);
        assert_eq!(angle.arc_minutes(), 2);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.centi_arc_seconds(), 40);
    }

    #[test]
    fn more_than_straight_is_valid() {
        let angle: AccurateDegree = "228°4′16.15″".parse().unwrap();
        assert_eq!(angle.degrees(), 228);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_deg_digits() {
        let _angle: AccurateDegree = "428°4′16.15″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_min_digits() {
        let _angle: AccurateDegree = "81°72′".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_sec_digits() {
        let _angle: AccurateDegree = "28°10′66.15″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_milli_digits() {
        let _angle: AccurateDegree = "28°40′16.151″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn overflow_in_domain_deg() {
        let _angle: AccurateDegree = "361°40′".parse().unwrap();
    }

    #[test]
    fn space_between_deg_and_min() {
        let angle: AccurateDegree = "81° 12′14″".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn space_between_min_and_sec() {
        let angle: AccurateDegree = "81°12′ 14.98″".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 98);
    }

    #[test]
    fn spaces_between_parts() {
        let angle: AccurateDegree = "81° 12′ 14.7″".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 70);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn spaces_between_parts_and_milliseconds() {
        let _angle: AccurateDegree = "81° 12′ 14. 7″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn skipping_degree_is_not_allowed_in_unicode_mode() {
        let _angle: AccurateDegree = "34 49′8″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn space_between_degree_val_and_sign_not_allowed() {
        let _angle: AccurateDegree = "34 °49′8″".parse().unwrap();
    }
}

#[cfg(test)]
mod parse_ascii_tests {
    use super::*;

    #[test]
    fn simple_deg() {
        let angle: AccurateDegree = "28*".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min() {
        let angle: AccurateDegree = "28*15'".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_with_sign() {
        let angle: AccurateDegree = "28°15'".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec() {
        let angle: AccurateDegree = "28*05'33\"".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 5);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec_cas() {
        let angle: AccurateDegree = "98*15'33.15\"".parse().unwrap();
        assert_eq!(angle.degrees(), 98);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    fn uneven_digits_deg_min_sec_cas() {
        let angle: AccurateDegree = r#"128*4'16.15""#.parse().unwrap();
        assert_eq!(angle.degrees(), 128);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    fn single_digit_deg_min_sec_cas() {
        let angle: AccurateDegree = "1*2'3.4\"".parse().unwrap();
        assert_eq!(angle.degrees(), 1);
        assert_eq!(angle.arc_minutes(), 2);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.centi_arc_seconds(), 40);
    }

    #[test]
    fn more_than_straight_is_valid() {
        let angle: AccurateDegree = "228*4'16.15\"".parse().unwrap();
        assert_eq!(angle.degrees(), 228);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_deg_digits() {
        let _angle: AccurateDegree = "428*4'16.15\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_min_digits() {
        let _angle: AccurateDegree = "81*72'".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_sec_digits() {
        let _angle: AccurateDegree = "28*10'66.15\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_milli_digits() {
        let _angle: AccurateDegree = "28*40'16.151\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn overflow_in_domain_deg() {
        let _angle: AccurateDegree = "361*40'".parse().unwrap();
    }

    #[test]
    fn space_between_deg_and_min() {
        let angle: AccurateDegree = "81* 12'14\"".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn space_between_min_and_sec() {
        let angle: AccurateDegree = "81*12' 14.98\"".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 98);
    }

    #[test]
    fn spaces_between_parts() {
        let angle: AccurateDegree = "81* 12' 14.7\"".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 70);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn spaces_between_parts_and_milliseconds() {
        let _angle: AccurateDegree = "81* 12' 14. 7\"".parse().unwrap();
    }

    #[test]
    fn skipping_degree_is_allowed_in_ascii_mode() {
        let angle: AccurateDegree = "34 49'8\"".parse().unwrap();
        assert_eq!(angle.degrees(), 34);
        assert_eq!(angle.arc_minutes(), 49);
        assert_eq!(angle.arc_seconds(), 8);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn skipping_minutes_sign_is_not_allowed_in_ascii_mode() {
        let _angle: AccurateDegree = "34 49 8\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn skipping_seconds_sign_is_not_allowed_in_ascii_mode() {
        let _angle: AccurateDegree = "34 49'8".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn space_between_degree_val_and_sign_not_allowed() {
        let _angle: AccurateDegree = "34 *49'8\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn mixed_ascii_deg_and_unicode() {
        let _angle: AccurateDegree = "34*49′8″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn mixed_ascii_min_and_unicode() {
        let _angle: AccurateDegree = "34°49'8″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn mixed_ascii_sec_and_unicode() {
        let _angle: AccurateDegree = "34°49′8\"".parse().unwrap();
    }
}
