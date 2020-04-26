//! The angle implementation can be used to store and operate (addition, subtraction)
//! on degrees with their decimal fractions with the hebdo (10^-7) precision.
//! <https://en.wikipedia.org/wiki/Decimal_degrees>
//!
//! It also can be used to operate in terms of or DMS (degrees, minutes, seconds)
//! with the milli (1/1000-th) of arc second precision.
//! However, DMS operations are always approximate and can accumulate an error.
//! E.g. summing up 10 angles of the 1 milliarcsecond will get you an angle of 11 milliarcseconds
//! (see `summing_dms_accumulate_errors` test).

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
    impl_angle_ops, try_from_tuples_and_arrays,
    utils::{div_mod, pow_10, RoundDiv, StripChar},
};

use super::{
    common::{parse_angle_re, UnitsAngle},
    consts::{
        ARC_MINUTE_SIGN, ARC_SECOND_SIGN, DEGREE_SIGN, FULL_TURN_DEG, HALF_TURN_DEG, MAX_DEGREE,
        MINUTES_IN_DEGREE, QUARTER_TURN_DEG, SECONDS_IN_MINUTE,
    },
    errors::{AngleNotInRange, ParseAngleError},
    Angle, AngleNames,
};

/// High-precision (10^-7 degrees) and compact (32 bits) angular type.
///
/// The length of the Earth's equator arc second is roughly 30m,
/// so we need smaller units to represent smaller things.
///
/// The current precision (10^-7 degrees) can represent things about 11 mm on the equator.
/// <https://en.wikipedia.org/wiki/Decimal_degrees#Precision>
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Default, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct DecimalDegree {
    units: u32,
}

impl AngleNames for DecimalDegree {
    fn zero() -> Self {
        Self::default()
    }

    fn right() -> Self {
        Self::try_from(QUARTER_TURN_DEG).expect("Right angle is valid")
    }

    fn straight() -> Self {
        Self::try_from(HALF_TURN_DEG).expect("Straight angle is valid")
    }

    fn complete() -> Self {
        Self::try_from(FULL_TURN_DEG).expect("Complete angle is valid")
    }
}

impl_angle_ops!(DecimalDegree);

impl UnitsAngle for DecimalDegree {
    type Units = u32;

    fn with_units(total_micro_degrees: Self::Units) -> Result<Self, AngleNotInRange> {
        if total_micro_degrees > Self::max_units() {
            return Err(AngleNotInRange::Degrees);
        }

        Ok(Self {
            units: total_micro_degrees,
        })
    }

    fn units(self) -> Self::Units {
        self.units
    }
}

impl Angle for DecimalDegree {
    type NumErr = AngleNotInRange;
    type ParseErr = ParseAngleError;

    fn obtuse_detected() -> Self::NumErr {
        AngleNotInRange::ObtuseAngle
    }

    fn reflex_detected() -> Self::NumErr {
        AngleNotInRange::ReflexAngle
    }
}

impl DecimalDegree {
    // the number of degree's decimal digits
    const PRECISION: u8 = 7;

    // the number of arcseconds's decimal digits
    const SECONDS_FD: usize = 3;
    const THOUSAND: u32 = pow_10(Self::SECONDS_FD);

    // TODO: make the two following `const` when the `pow` becomes stable

    fn units_in_deg() -> u32 {
        10_u32.pow(Self::PRECISION.into())
    }

    fn mas_in_deg() -> u32 {
        let sec_in_min = u32::from(SECONDS_IN_MINUTE);
        let min_in_deg = u32::from(MINUTES_IN_DEGREE);
        let sec_in_deg = sec_in_min * min_in_deg;
        Self::THOUSAND * sec_in_deg
    }

    fn with_deg_and_micro(degrees: u16, micro_degrees: u32) -> Result<Self, AngleNotInRange> {
        let valid_degrees = 0..=MAX_DEGREE;
        if !valid_degrees.contains(&degrees) {
            return Err(AngleNotInRange::Degrees);
        };

        let max_fraction_units = Self::units_in_deg();

        let valid_fraction = if degrees == MAX_DEGREE {
            0..1
        } else {
            0..max_fraction_units
        };

        if !valid_fraction.contains(&micro_degrees) {
            return Err(AngleNotInRange::DegreeFraction);
        }

        let units = u64::from(degrees) * u64::from(max_fraction_units) + u64::from(micro_degrees);
        let units = units.try_into().map_err(|_err| AngleNotInRange::Degrees)?;
        Ok(Self { units })
    }

    /// Degree, minute, second, millisecond
    /// <https://en.wikipedia.org/wiki/Minute_and_second_of_arc>
    ///
    /// # Errors
    /// When some part of the angle is out of scope
    /// (e.g. minutes > 60 or degree > 360), the `AngleNotInRange` returned.
    pub fn with_dms(
        degree: u16,
        minutes: u8,
        seconds: u8,
        milli_seconds: u16,
    ) -> Result<Self, AngleNotInRange> {
        Self::check_dms(degree, minutes, seconds, milli_seconds)?;

        // prevent further multiplication overflow by extending precision
        let sec_in_min = u32::from(SECONDS_IN_MINUTE);

        // max is (3600 * 1000)
        let total_mas = ((u32::from(minutes) * sec_in_min) + u32::from(seconds)) * Self::THOUSAND
            + u32::from(milli_seconds);

        // workaround for bad conversion of 3.6 milli-seconds into 10 micro-degrees
        let num = Self::units_in_deg();
        let denom = Self::mas_in_deg();

        let as_units = (u64::from(total_mas) * u64::from(num)).div_round(u64::from(denom));
        let fraction = as_units
            .try_into()
            .map_err(|_| AngleNotInRange::ArcMinutes)?;
        Self::with_deg_and_micro(degree, fraction)
    }

    fn check_dms(
        degree: u16,
        minutes: u8,
        seconds: u8,
        milli_seconds: u16,
    ) -> Result<(), AngleNotInRange> {
        let valid_degrees = 0..=MAX_DEGREE;
        if !valid_degrees.contains(&degree) {
            return Err(AngleNotInRange::Degrees);
        }

        let (valid_minutes, valid_seconds, valid_milli) = if degree == MAX_DEGREE {
            (0..1, 0..1, 0..1)
        } else {
            (
                0..MINUTES_IN_DEGREE,
                0..SECONDS_IN_MINUTE,
                0..(Self::THOUSAND as u16),
            )
        };

        if !valid_minutes.contains(&minutes) {
            return Err(AngleNotInRange::ArcMinutes);
        }

        if !valid_seconds.contains(&seconds) {
            return Err(AngleNotInRange::ArcSeconds);
        }

        if !valid_milli.contains(&milli_seconds) {
            return Err(AngleNotInRange::ArcMilliSeconds);
        }

        Ok(())
    }

    /// The whole number of degrees in the angle
    pub fn degrees(self) -> u16 {
        let degrees = self.units / Self::units_in_deg();
        degrees as u16
    }

    /// The fractional part of the angle represented in the small units (10^-7 degrees)
    pub fn fract(self) -> u32 {
        self.units % Self::units_in_deg()
    }

    /// The arc minutes component of the angle.
    pub fn arc_minutes(self) -> u8 {
        self.dms_parts(true).1
    }

    /// The arc seconds component of the angle.
    pub fn arc_seconds(self) -> u8 {
        self.dms_parts(true).2
    }

    /// Get the milli arc seconds (1/1000-th of the arc second) component of the angle.
    ///
    /// Use with caution! The overflow of `0.999_999_9` degrees
    /// handled incorrectly to keep the `self.degrees()` value valid.
    /// To get the precise values in such a boundary condition,
    /// use the `self.deg_min_sec_mas()` instead.
    pub fn milli_arc_seconds(self) -> u16 {
        self.dms_parts(true).3
    }

    /// If `keep_degrees` is false, overflow in minutes will be added to degrees
    fn dms_parts(self, keep_degrees: bool) -> (u16, u8, u8, u16) {
        // prevent further multiplication overflow by extending precision
        let fraction_units = u64::from(self.fract());
        let units_in_deg = u64::from(Self::units_in_deg());

        let milli = u64::from(Self::THOUSAND);
        let sec_in_min = u64::from(SECONDS_IN_MINUTE);
        let min_in_deg = u64::from(MINUTES_IN_DEGREE);
        let sec_in_deg = sec_in_min * min_in_deg;
        let milli_in_deg = milli * sec_in_deg;

        let total_milli = (fraction_units * milli_in_deg).div_round(units_in_deg);
        let (total_seconds, mas) = div_mod(total_milli, milli);
        let (total_minutes, sec) = div_mod(total_seconds, sec_in_min);
        let (deg_overflow, minutes) = div_mod(total_minutes, min_in_deg);

        let minutes = minutes.try_into().expect("Overflow in minutes");
        let sec = sec.try_into().expect("Overflow in seconds");
        let mas = mas.try_into().expect("Overflow in milli seconds");

        let mut deg = self.degrees();
        if deg_overflow > 0 {
            assert_eq!(deg_overflow, 1);
            assert_eq!(minutes, 0);
            assert_eq!(sec, 0);
            assert_eq!(mas, 0);
            if keep_degrees {
                // subtract minimal DMS to prevent overflow in degrees
                let min_dms = Self::with_dms(0, 0, 0, 1).expect("Min DMS is valid");
                // `match_degrees=false` to prevent any possibility of the recursive call
                return (self - min_dms).dms_parts(false);
            }
            deg += 1;
        }

        (deg, minutes, sec, mas)
    }

    /// Parts of the angle as in the DMS scheme.
    ///
    /// There is a situation when the degree part not the same as the result of `self.degrees()`.
    /// When the angle's value is too close to whole degree (in terms of internal representation),
    /// but in terms of the DMS, its already the whole angle, e.g.
    ///
    /// for angle `35.9999999` the `degrees()` function returns 35
    /// but the `deg_min_sec_mas()` returns (36, 0, 0, 0) due to rounding rules
    pub fn deg_min_sec_mas(self) -> (u16, u8, u8, u16) {
        self.dms_parts(false)
    }

    /// As the decimal representation is 2.777 times more precise,
    /// a gap may appear when converting to the DMS representation
    pub fn almost_equal(self, rhs: Self) -> bool {
        self.abs_diff(rhs) <= Self { units: 1 }
    }
}

impl TryFrom<f64> for DecimalDegree {
    type Error = AngleNotInRange;

    /// Use with caution: the floating numbers has bad precision in the fraction part
    fn try_from(value: f64) -> Result<Self, Self::Error> {
        if value.is_sign_negative() {
            return Err(AngleNotInRange::Degrees);
        }

        // prevent wrapping around
        let integer = value.floor() as u64;
        let integer = integer.try_into().map_err(|_| AngleNotInRange::Degrees)?;

        let precision = Self::units_in_deg();
        let fraction = (value.fract() * f64::from(precision)).round() as u64;
        let fraction = fraction
            .try_into()
            .map_err(|_| AngleNotInRange::DegreeFraction)?;

        // fraction part of the value rounds up to 1
        if fraction == precision {
            Self::with_deg_and_micro(integer + 1, 0)
        } else {
            Self::with_deg_and_micro(integer, fraction)
        }
    }
}

impl FromStr for DecimalDegree {
    type Err = ParseAngleError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s
            .strip_suffix_char(DEGREE_SIGN)
            .map_or_else(|| Cow::Borrowed(s), Cow::Owned);
        if let Ok(number) = s.parse::<f64>() {
            Ok(Self::try_from(number)?)
        } else {
            Self::parse_dms(&s)
        }
    }
}

lazy_static! {
    static ref RE_UNICODE: Regex = Regex::new(&parse_angle_re(false, DecimalDegree::SECONDS_FD))
        .expect("Unicode regex is valid");
    static ref RE_ASCII: Regex =
        Regex::new(&parse_angle_re(true, DecimalDegree::SECONDS_FD)).expect("ASCII regex is valid");
}

impl DecimalDegree {
    fn parse_dms(s: &str) -> Result<Self, ParseAngleError> {
        let capture = RE_UNICODE
            .captures(s)
            .or_else(|| RE_ASCII.captures(s))
            .ok_or(ParseAngleError::DmsNotation)?;
        let deg = capture.name("deg").ok_or(ParseAngleError::DmsNotation)?;
        let deg = deg.as_str().parse()?;

        dbg!(&capture);
        let min = capture.name("min").map_or("0", |m| m.as_str()).parse()?;
        let sec = capture.name("sec").map_or("0", |m| m.as_str()).parse()?;
        let mas = if let Some(capture) = capture.name("sec_fract") {
            let mas = format!("{:0<width$}", capture.as_str(), width = Self::SECONDS_FD);
            mas.parse()?
        } else {
            0
        };

        let good = Self::with_dms(deg, min, sec, mas)?;
        Ok(good)
    }
}

impl fmt::Display for DecimalDegree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // DMS
        if f.alternate() {
            let (deg, arc_min, arc_sec, mas) = self.deg_min_sec_mas();
            write!(f, "{}{}", deg, DEGREE_SIGN)?;

            if (arc_min != 0) || (arc_sec != 0) || (mas != 0) {
                write!(f, "{}{}", arc_min, ARC_MINUTE_SIGN)?;
            }

            if (arc_sec != 0) || (mas != 0) {
                if mas == 0 {
                    write!(f, "{}{}", arc_sec, ARC_SECOND_SIGN)
                } else {
                    let arc_sec = f64::from(arc_sec) + f64::from(mas) / f64::from(Self::THOUSAND);
                    write!(f, "{}{}", arc_sec, ARC_SECOND_SIGN)
                }
            } else {
                Ok(())
            }
        } else {
            let (deg, fract) = (self.degrees(), self.fract());
            if fract == 0 {
                write!(f, "{}{}", deg, DEGREE_SIGN)
            } else {
                write!(
                    f,
                    "{}.{:0>width$}{}",
                    deg,
                    fract,
                    DEGREE_SIGN,
                    width = Self::PRECISION.into()
                )
            }
        }
    }
}

impl TryFrom<(u16, u8, u8, u16)> for DecimalDegree {
    type Error = AngleNotInRange;

    fn try_from(value: (u16, u8, u8, u16)) -> Result<Self, Self::Error> {
        let (deg, min, sec, milli) = value;
        Self::with_dms(deg, min, sec, milli)
    }
}

impl TryFrom<[u16; 4]> for DecimalDegree {
    type Error = AngleNotInRange;

    fn try_from(value: [u16; 4]) -> Result<Self, Self::Error> {
        let [deg, min, sec, mas] = value;
        let min: u8 = min.try_into().map_err(|_| AngleNotInRange::ArcMinutes)?;
        let sec: u8 = sec.try_into().map_err(|_| AngleNotInRange::ArcSeconds)?;
        Self::with_dms(deg, min, sec, mas)
    }
}

try_from_tuples_and_arrays!((DecimalDegree, AngleNotInRange) <- u16, u8, u8, u16; u16);

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use super::*;

    #[test]
    fn degree_angle_is_32_bits() {
        assert_eq!(size_of::<DecimalDegree>(), 4)
    }

    #[test]
    fn default() {
        let zero_angle = DecimalDegree::default();
        assert!(zero_angle.is_zero());

        assert_eq!(zero_angle.degrees(), 0);
        assert_eq!(zero_angle.fract(), 0);
        assert_eq!(zero_angle.units(), 0);

        assert_eq!(zero_angle.arc_minutes(), 0);
        assert_eq!(zero_angle.arc_seconds(), 0);
        assert_eq!(zero_angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn max_valid_value() {
        let north_pole: DecimalDegree = 180.try_into().unwrap();
        assert!(north_pole.is_straight());
        assert_eq!(north_pole.degrees(), 180);
        assert_eq!(north_pole.fract(), 0);
        assert_eq!(north_pole.units(), 1_800_000_000);

        assert_eq!(north_pole.arc_minutes(), 0);
        assert_eq!(north_pole.arc_seconds(), 0);
        assert_eq!(north_pole.milli_arc_seconds(), 0);

        let north_pole2: DecimalDegree = DecimalDegree::with_dms(180, 0, 0, 0).unwrap();
        assert_eq!(north_pole2, north_pole);
    }

    /// <https://en.wikipedia.org/wiki/Tropic_of_Capricorn>
    #[test]
    fn intermediate() {
        let polar_circle = DecimalDegree::with_deg_and_micro(66, 5_633_334).unwrap();
        assert!(polar_circle.is_acute());
        assert_eq!(polar_circle.degrees(), 66);
        assert_eq!(polar_circle.fract(), 5_633_334);
        assert_eq!(polar_circle.units(), 665_633_334);

        assert_eq!(polar_circle.arc_minutes(), 33);
        assert_eq!(polar_circle.arc_seconds(), 48);
        assert_eq!(polar_circle.milli_arc_seconds(), 0);
    }

    #[test]
    fn bigger_than_straight_is_valid() {
        let angle = DecimalDegree::with_deg_and_micro(200, 0).unwrap();
        assert!(angle.is_reflex());
        assert_eq!(angle.degrees(), 200);
        assert_eq!(angle.fract(), 0);

        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn bigger_than_straight_dms() {
        let angle = DecimalDegree::with_dms(181, 0, 2, 11).unwrap();
        assert!(angle.is_reflex());
        assert_eq!(angle.degrees(), 181);

        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 2);
        assert_eq!(angle.milli_arc_seconds(), 11);
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn bigger_than_complete() {
        let _a = DecimalDegree::with_deg_and_micro(365, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn bigger_than_complete_degree() {
        let _a = DecimalDegree::with_dms(361, 0, 0, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcMinutes")]
    fn bigger_than_complete_minute() {
        let _a = DecimalDegree::with_dms(360, 5, 0, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcSeconds")]
    fn bigger_than_complete_second() {
        let _a = DecimalDegree::with_dms(360, 0, 2, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcMilliSeconds")]
    fn bigger_than_complete_milli_second() {
        let _a = DecimalDegree::with_dms(360, 0, 0, 1).unwrap();
    }

    #[test]
    #[should_panic(expected = "DegreeFraction")]
    fn bigger_than_complete_minimum_fraction() {
        let _a = DecimalDegree::with_deg_and_micro(360, 1).unwrap();
    }

    #[test]
    fn complete() {
        let angle = DecimalDegree::with_deg_and_micro(360, 0).unwrap();
        assert!(angle.is_complete());
        assert_eq!(angle.degrees(), 360);
        assert_eq!(angle.fract(), 0);

        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    #[should_panic(expected = "ArcMinutes")]
    fn bad_minutes() {
        let _a = DecimalDegree::with_dms(30, 60, 60, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcSeconds")]
    fn bad_seconds() {
        let _a = DecimalDegree::with_dms(30, 59, 60, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcSeconds")]
    fn bad_seconds_2() {
        let _a = DecimalDegree::with_dms(30, 59, 100, 0).unwrap();
    }

    #[test]
    fn good_milli_seconds() {
        let angle = DecimalDegree::with_dms(30, 59, 0, 999).unwrap();
        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 999);
    }

    #[test]
    #[should_panic(expected = "ArcMilliSeconds")]
    fn bad_milli_seconds() {
        let _a = DecimalDegree::with_dms(30, 59, 0, 1000).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcMilliSeconds")]
    fn bad_milli_seconds_2() {
        let _a = DecimalDegree::with_dms(30, 59, 0, 1500).unwrap();
    }

    #[test]
    fn from_f64() {
        let angle = DecimalDegree::try_from(23.499_999_9).unwrap();
        assert!(angle.is_acute());

        let angle2 = DecimalDegree::with_deg_and_micro(23, 4_999_999).unwrap();
        assert_eq!(angle, angle2);
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn from_f64_deg_overflow() {
        let _a = DecimalDegree::try_from(425.0).unwrap();
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn from_f64_wrap_around_u16() {
        let angle: DecimalDegree = 65566.5.try_into().unwrap();

        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 30);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn from_u16() {
        let angle: DecimalDegree = 300.try_into().unwrap();
        assert!(angle.is_reflex());

        assert_eq!(angle.degrees(), 300);
        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn from_u8() {
        let angle = DecimalDegree::with_deg_and_micro(108, 0).unwrap();
        assert!(angle.is_obtuse());

        let angle2 = 108.try_into().unwrap();
        assert_eq!(angle, angle2);
    }

    #[test]
    fn from_pair() {
        let angle: DecimalDegree = (7, 59).try_into().unwrap();
        assert_eq!(angle.degrees(), 7);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn from_triple() {
        let angle: DecimalDegree = (117, 59, 3).try_into().unwrap();
        assert_eq!(angle.degrees(), 117);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn from_quadruple() {
        let angle: DecimalDegree = (317, 59, 3, 980).try_into().unwrap();
        assert_eq!(angle.degrees(), 317);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.milli_arc_seconds(), 980);
    }

    #[test]
    fn from_ar2() {
        let angle: DecimalDegree = [40, 15].try_into().unwrap();
        assert_eq!(angle.degrees(), 40);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn from_ar3() {
        let angle: DecimalDegree = [320, 15, 8].try_into().unwrap();
        assert_eq!(angle.degrees(), 320);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 8);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn from_ar4() {
        let angle: DecimalDegree = [120, 15, 8, 365].try_into().unwrap();
        assert_eq!(angle.degrees(), 120);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 8);
        assert_eq!(angle.milli_arc_seconds(), 365);
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn from_int_overflow() {
        let _angle: DecimalDegree = [500, 15, 8, 365].try_into().unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcMinutes")]
    fn from_ar4_overflow() {
        let _angle: DecimalDegree = [120, 300, 8, 365].try_into().unwrap();
    }

    #[test]
    fn good_fraction_minus_one_is_overflow() {
        let angle = DecimalDegree::with_deg_and_micro(30, 9_999_999).unwrap();
        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.fract(), 9_999_999);
        assert_eq!(angle.units(), 309_999_999);

        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 59);
        // slightly less than the real value, but the degrees is still 30
        assert_eq!(angle.milli_arc_seconds(), 999);

        let parts_with_the_same_degree_value = angle.dms_parts(true);
        assert_eq!(parts_with_the_same_degree_value, (30, 59, 59, 999)); // not really correct

        let parts_with_the_increased_degree = angle.deg_min_sec_mas();
        // this value is closer ...
        assert_eq!(parts_with_the_increased_degree, (31, 0, 0, 0));
        // but inconsistent with the `degrees()` method
        assert!(parts_with_the_increased_degree.0 > angle.degrees())
    }

    #[test]
    fn good_fraction_minus_two() {
        let angle = DecimalDegree::with_deg_and_micro(30, 9_999_998).unwrap();
        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.fract(), 9_999_998);
        assert_eq!(angle.units(), 309_999_998);

        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 59);
        assert_eq!(angle.milli_arc_seconds(), 999);
    }

    #[test]
    #[should_panic(expected = "DegreeFraction")]
    fn bad_fraction() {
        let _a = DecimalDegree::with_deg_and_micro(30, 10_000_000).unwrap();
    }

    #[test]
    #[should_panic(expected = "DegreeFraction")]
    fn bad_fraction_2() {
        let _a = DecimalDegree::with_deg_and_micro(30, 15_000_000).unwrap();
    }

    #[test]
    fn test_very_small_angles() {
        for f in 0..1000 {
            let angle = DecimalDegree::with_deg_and_micro(0, f).unwrap();
            assert_eq!(angle.degrees(), 0);
            assert_eq!(angle.fract(), f);
            assert_eq!(angle.units(), f);
        }
    }

    #[test]
    #[ignore]
    fn test_first_degree_every_fraction_with_step_1() {
        let mut prev = None;
        for f in 0..10_000_000 {
            let angle = DecimalDegree::with_deg_and_micro(0, f).unwrap();
            assert_eq!(angle.degrees(), 0);
            assert_eq!(angle.fract(), f);
            if let Some(prev) = prev {
                assert!(angle > prev);
                assert_eq!(
                    angle - prev,
                    DecimalDegree::with_deg_and_micro(0, 1).unwrap()
                );
            }

            prev = Some(angle);
        }
    }

    fn round_trip(deg: u16, min: u8, sec: u8, milli_sec: u16) {
        eprintln!("\n\n================");
        let angle = DecimalDegree::with_dms(deg, min, sec, milli_sec).unwrap();
        dbg!(&angle);

        assert_eq!(angle.degrees(), deg);
        assert_eq!(angle.arc_minutes(), min);
        assert_eq!(angle.arc_seconds(), sec);
        assert_eq!(angle.milli_arc_seconds(), milli_sec);
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
                    for milli in 0..1000 {
                        if (100..500).contains(&milli) {
                            continue;
                        }

                        round_trip(deg, min, sec, milli)
                    }
                }
            }
        }

        round_trip(180, 0, 0, 0);
    }

    #[test]
    fn dms_almost_int() {
        let angle = DecimalDegree::with_dms(156, 59, 59, 999).unwrap();

        assert_eq!(angle.degrees(), 156);
        assert_eq!(angle.fract(), 9_999_997);
    }

    #[test]
    fn print_fraction() {
        let d = DecimalDegree::with_deg_and_micro(60, 5_467_182).unwrap();
        assert_eq!(d.to_string(), "60.5467182°")
    }

    #[test]
    fn print_fraction_almost_integer() {
        let almost_20 =
            DecimalDegree::try_from(20).unwrap() - DecimalDegree::with_deg_and_micro(0, 1).unwrap();

        assert_eq!(almost_20.to_string(), "19.9999999°")
    }

    #[test]
    fn print_fraction_very_small() {
        let almost_zero = DecimalDegree::with_deg_and_micro(0, 1).unwrap();
        assert_eq!(almost_zero.to_string(), "0.0000001°")
    }

    #[test]
    fn print_zero() {
        let d = DecimalDegree::default();
        assert_eq!(d.to_string(), "0°")
    }

    #[test]
    fn print_zero_as_dms() {
        let d = DecimalDegree::default();
        let s = format!("{:#}", d);
        assert_eq!(s, "0°")
    }

    #[test]
    fn print_right() {
        let d = DecimalDegree::try_from(90).unwrap();
        assert_eq!(d.to_string(), "90°")
    }

    #[test]
    fn print_right_as_dms() {
        let d: DecimalDegree = 90.try_into().unwrap();
        let s = format!("{:#}", d);
        assert_eq!(s, "90°")
    }

    #[test]
    fn print_fraction_as_dms() {
        let d = DecimalDegree::with_deg_and_micro(60, 5_467_182).unwrap();
        let s = format!("{:#}", d);
        assert_eq!(s, "60°32′48.186″")
    }

    #[test]
    fn print_fraction_as_dms_without_milli() {
        for f in 0..3 {
            let d = DecimalDegree::with_deg_and_micro(60, 5_466_666 + f).unwrap();
            let s = format!("{:#}", d);
            assert_eq!(s, "60°32′48″");
        }
    }

    #[test]
    fn print_fraction_as_dms_without_seconds() {
        for f in 0..3 {
            let d = DecimalDegree::with_deg_and_micro(60, 5_333_332 + f).unwrap();
            let s = format!("{:#}", d);
            assert_eq!(s, "60°32′");
        }
    }

    #[test]
    fn print_overflow_fraction_as_dms() {
        let d = DecimalDegree::with_deg_and_micro(59, 9_999_999).unwrap();
        let s = format!("{:#}", d);
        assert_eq!(s, "60°")
    }

    #[test]
    fn add() {
        let first = DecimalDegree::with_dms(118, 51, 27, 954).unwrap();
        let second = DecimalDegree::with_dms(47, 38, 19, 746).unwrap();
        let sum = first + second;

        assert_eq!(sum.degrees(), 166);
        assert_eq!(sum.arc_minutes(), 29);
        assert_eq!(sum.arc_seconds(), 47);
        assert_eq!(sum.milli_arc_seconds(), 700);
    }

    #[test]
    fn add_minimal_overflow() {
        let max = DecimalDegree::complete();
        let min = DecimalDegree::with_deg_and_micro(0, 1).unwrap();

        let add_res = max.checked_add(&min);
        assert!(add_res.is_none());

        // wrapped around
        assert_eq!(max + min, DecimalDegree::with_deg_and_micro(0, 1).unwrap());
    }

    #[test]
    fn add_with_wrapping() {
        let first = DecimalDegree::with_dms(256, 18, 0, 600).unwrap();
        let second = (153, 4, 0, 0).try_into().unwrap();

        // wrapped around
        assert!((first + second).almost_equal((49, 22, 0, 600).try_into().unwrap()));
    }

    #[test]
    fn add_no_overflow() {
        let max = DecimalDegree::straight();
        let min = DecimalDegree::with_deg_and_micro(0, 1).unwrap();

        let res = max
            .checked_sub(&min)
            .and_then(|sub| sub.checked_add(&min))
            .unwrap();
        assert!(res.is_straight());
    }

    #[test]
    #[should_panic(expected = "assertion failed")]
    fn summing_dms_accumulate_errors() {
        let min = DecimalDegree::with_dms(0, 0, 0, 1).unwrap();

        let mut acc = DecimalDegree::zero();

        for _ in 0..10 {
            acc = acc + min;
        }

        assert_eq!(acc.milli_arc_seconds(), 10);
    }

    #[test]
    fn sub() {
        let first = DecimalDegree::with_dms(318, 51, 27, 954).unwrap();
        let second = DecimalDegree::with_dms(47, 38, 19, 746).unwrap();
        let sum = first - second;

        assert_eq!(sum.degrees(), 271);
        assert_eq!(sum.arc_minutes(), 13);
        assert_eq!(sum.arc_seconds(), 8);
        assert_eq!(sum.milli_arc_seconds(), 208);
    }

    #[test]
    fn sub_underflow() {
        let first = DecimalDegree::with_dms(47, 38, 19, 746).unwrap();
        let second = DecimalDegree::with_dms(47, 38, 19, 747).unwrap();
        let sum = first.checked_sub(&second);
        assert!(sum.is_none());
    }

    #[test]
    fn sub_with_zero_res() {
        let first = DecimalDegree::with_dms(47, 38, 19, 746).unwrap();
        let second = DecimalDegree::with_dms(47, 38, 19, 746).unwrap();
        let sum = first.checked_sub(&second).unwrap();
        assert!(sum.is_zero());
    }

    #[test]
    fn complementary() {
        let angle: DecimalDegree = 79.888_888_9.try_into().unwrap();
        let supp = angle.complement().unwrap();
        assert_eq!(supp.units(), 101_111_111);
    }

    #[test]
    fn complementary_dms() {
        let angle = DecimalDegree::with_dms(47, 38, 19, 746).unwrap();
        let supp = angle.complement().unwrap();
        assert_eq!(supp.degrees(), 42);
        assert_eq!(supp.arc_minutes(), 21);
        assert_eq!(supp.arc_seconds(), 40);
        assert_eq!(supp.milli_arc_seconds(), 254);
    }

    #[test]
    fn complement_of_obtuse_undefined() {
        let angle = DecimalDegree::with_dms(117, 38, 19, 746).unwrap();
        assert!(angle.complement().is_none());
    }

    #[test]
    fn supplementary() {
        let angle: DecimalDegree = 30.98765.try_into().unwrap();
        let supp = angle.supplement().unwrap();
        assert_eq!(supp.degrees(), 149);
        assert_eq!(supp.units(), 1_490_123_500);
    }

    #[test]
    fn supplementary_dms() {
        let angle = DecimalDegree::with_dms(157, 44, 3, 111).unwrap();
        let supp = angle.supplement().unwrap();
        assert_eq!(supp.degrees(), 22);
        assert_eq!(supp.arc_minutes(), 15);
        assert_eq!(supp.arc_seconds(), 56);
        assert_eq!(supp.milli_arc_seconds(), 889);
    }

    #[test]
    fn supplement_of_reflex_undefined() {
        let angle = DecimalDegree::with_dms(190, 38, 19, 746).unwrap();
        assert!(angle.supplement().is_none());
    }

    #[test]
    fn explementary() {
        let angle: DecimalDegree = 130.98765.try_into().unwrap();
        let exp = angle.explement();
        assert_eq!(exp.degrees(), 229);
        assert_eq!(exp.units(), 2_290_123_500);
    }

    #[test]
    fn explementary_dms() {
        let angle = DecimalDegree::with_dms(275, 44, 3, 111).unwrap();
        let exp = angle.explement();
        assert_eq!(exp.degrees(), 84);
        assert_eq!(exp.arc_minutes(), 15);
        assert_eq!(exp.arc_seconds(), 56);
        assert_eq!(exp.milli_arc_seconds(), 889);
    }

    #[test]
    fn explement_of_obtuse_is_reflex() {
        let angle = DecimalDegree::with_dms(95, 38, 19, 746).unwrap();
        let exp = angle.explement();
        assert_eq!(exp.degrees(), 264);
        assert_eq!(exp.arc_minutes(), 21);
        assert_eq!(exp.arc_seconds(), 40);
        assert_eq!(exp.milli_arc_seconds(), 254);
    }
}

#[cfg(test)]
mod parse_tests {
    use super::*;

    #[test]
    fn simple_integer() {
        let s = "54";
        let angle: DecimalDegree = s.parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.fract(), 0);

        assert_eq!(angle, DecimalDegree::with_dms(54, 0, 0, 0).unwrap());
    }

    #[test]
    fn simple_integer_with_degree_sign() {
        let s = "54°";
        let angle: DecimalDegree = s.parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.fract(), 0);

        assert_eq!(angle, DecimalDegree::with_dms(54, 0, 0, 0).unwrap());
    }

    #[test]
    fn simple_decimal() {
        let angle: DecimalDegree = "54.145".parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.fract(), 1_450_000);
    }

    #[test]
    fn simple_decimal_with_degree_sign() {
        let angle: DecimalDegree = "54.145°".parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.fract(), 1_450_000);
    }

    #[test]
    fn too_precise_truncation() {
        let angle: DecimalDegree = "54.123456789".parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.fract(), 1_234_568);
    }

    #[test]
    fn round_down_more_than_7_digits() {
        let angle: DecimalDegree = "18.99999995°".parse().unwrap();
        assert_eq!(angle.degrees(), 18);
        assert_eq!(angle.fract(), 9_999_999);
    }

    #[test]
    fn round_up_more_than_7_digits() {
        let angle: DecimalDegree = "18.99999996°".parse().unwrap();
        assert_eq!(angle.degrees(), 19);
        assert_eq!(angle.fract(), 0);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn bad_float() {
        let _angle: DecimalDegree = "54.123456.789".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn bad_negative() {
        let _angle: DecimalDegree = "-54.12".parse().unwrap();
    }

    #[test]
    fn big_but_valid() {
        let angle: DecimalDegree = "278.123456".parse().unwrap();
        assert_eq!(angle.degrees(), 278);
        assert_eq!(angle.fract(), 1_234_560);
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn bad_too_big_for_angle() {
        let _angle: DecimalDegree = "364.123456".parse().unwrap();
    }

    #[test]
    fn simple_deg() {
        let angle: DecimalDegree = "28°".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn deg_min() {
        let angle: DecimalDegree = "28°15′".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec() {
        let angle: DecimalDegree = "28°05′33″".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 5);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec_mas() {
        let angle: DecimalDegree = "98°15′33.156″".parse().unwrap();
        assert_eq!(angle.degrees(), 98);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.milli_arc_seconds(), 156);
    }

    #[test]
    fn uneven_digits_deg_min_sec_mas() {
        let angle: DecimalDegree = "128°4′16.15″".parse().unwrap();
        assert_eq!(angle.degrees(), 128);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.milli_arc_seconds(), 150);
    }

    #[test]
    fn single_digit_deg_min_sec_mas() {
        let angle: DecimalDegree = "1°2′3.4″".parse().unwrap();
        assert_eq!(angle.degrees(), 1);
        assert_eq!(angle.arc_minutes(), 2);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.milli_arc_seconds(), 400);
    }

    #[test]
    fn more_than_straight_is_valid() {
        let angle: DecimalDegree = "228°4′16.15″".parse().unwrap();
        assert_eq!(angle.degrees(), 228);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.milli_arc_seconds(), 150);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_deg_digits() {
        let _angle: DecimalDegree = "428°4′16.15″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_min_digits() {
        let _angle: DecimalDegree = "81°72′".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_sec_digits() {
        let _angle: DecimalDegree = "28°10′66.15″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_milli_digits() {
        let _angle: DecimalDegree = "28°40′16.1514″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn overflow_in_domain_deg() {
        let _angle: DecimalDegree = "361°40′".parse().unwrap();
    }

    #[test]
    fn space_between_deg_and_min() {
        let angle: DecimalDegree = "81° 12′14″".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn space_between_min_and_sec() {
        let angle: DecimalDegree = "81°12′ 14.98″".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.milli_arc_seconds(), 980);
    }

    #[test]
    fn spaces_between_parts() {
        let angle: DecimalDegree = "81° 12′ 14.7″".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.milli_arc_seconds(), 700);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn spaces_between_parts_and_milliseconds() {
        let _angle: DecimalDegree = "81° 12′ 14. 7″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn skipping_degree_is_not_allowed_in_unicode_mode() {
        let _angle: DecimalDegree = "34 49′8″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn space_between_degree_val_and_sign_not_allowed() {
        let _angle: DecimalDegree = "34 °49′8″".parse().unwrap();
    }
}

#[cfg(test)]
mod parse_ascii_tests {
    use super::*;

    #[test]
    fn simple_deg() {
        let angle: DecimalDegree = "28*".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn deg_min() {
        let angle: DecimalDegree = "28*15'".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec() {
        let angle: DecimalDegree = "28*05'33\"".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 5);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec_mas() {
        let angle: DecimalDegree = "98*15'33.156\"".parse().unwrap();
        assert_eq!(angle.degrees(), 98);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.milli_arc_seconds(), 156);
    }

    #[test]
    fn uneven_digits_deg_min_sec_mas() {
        let angle: DecimalDegree = r#"128*4'16.15""#.parse().unwrap();
        assert_eq!(angle.degrees(), 128);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.milli_arc_seconds(), 150);
    }

    #[test]
    fn single_digit_deg_min_sec_mas() {
        let angle: DecimalDegree = "1*2'3.4\"".parse().unwrap();
        assert_eq!(angle.degrees(), 1);
        assert_eq!(angle.arc_minutes(), 2);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.milli_arc_seconds(), 400);
    }

    #[test]
    fn more_than_straight_is_valid() {
        let angle: DecimalDegree = "228*4'16.15\"".parse().unwrap();
        assert_eq!(angle.degrees(), 228);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.milli_arc_seconds(), 150);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_deg_digits() {
        let _angle: DecimalDegree = "428*4'16.15\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_min_digits() {
        let _angle: DecimalDegree = "81*72'".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_sec_digits() {
        let _angle: DecimalDegree = "28*10'66.15\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_milli_digits() {
        let _angle: DecimalDegree = "28*40'16.1514\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn overflow_in_domain_deg() {
        let _angle: DecimalDegree = "361*40'".parse().unwrap();
    }

    #[test]
    fn space_between_deg_and_min() {
        let angle: DecimalDegree = "81* 12'14\"".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    fn space_between_min_and_sec() {
        let angle: DecimalDegree = "81*12' 14.98\"".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.milli_arc_seconds(), 980);
    }

    #[test]
    fn spaces_between_parts() {
        let angle: DecimalDegree = "81* 12' 14.7\"".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.milli_arc_seconds(), 700);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn spaces_between_parts_and_milliseconds() {
        let _angle: DecimalDegree = "81* 12' 14. 7\"".parse().unwrap();
    }

    #[test]
    fn skipping_degree_is_allowed_in_ascii_mode() {
        let angle: DecimalDegree = "34 49'8\"".parse().unwrap();
        assert_eq!(angle.degrees(), 34);
        assert_eq!(angle.arc_minutes(), 49);
        assert_eq!(angle.arc_seconds(), 8);
        assert_eq!(angle.milli_arc_seconds(), 0);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn skipping_minutes_sign_is_not_allowed_in_ascii_mode() {
        let _angle: DecimalDegree = "34 49 8\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn skipping_seconds_sign_is_not_allowed_in_ascii_mode() {
        let _angle: DecimalDegree = "34 49'8".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn space_between_degree_val_and_sign_not_allowed() {
        let _angle: DecimalDegree = "34 *49'8\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn mixed_ascii_deg_and_unicode() {
        let _angle: DecimalDegree = "34*49′8″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn mixed_ascii_min_and_unicode() {
        let _angle: DecimalDegree = "34°49'8″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn mixed_ascii_sec_and_unicode() {
        let _angle: DecimalDegree = "34°49′8\"".parse().unwrap();
    }
}
