//! The angle implementation can be used to store and process either:
//!  - degrees with their decimal fractions with the micro (10^-6) precision;
//!  - or DMS (degrees, minutes, seconds) with the centi (1/100-th) of arc second precision.
//!
//! Operands with the different representations are always produce
//! approximate result on the operations of addition, subtraction.
//! But when using the same (DMS+DMS or Decimal+Decimal) representations,
//! the result never loses any value.

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
    try_from_tuples_and_arrays,
    utils::{div_mod, pow_10, RoundDiv, StripChar},
};

use super::{
    consts::{
        ARC_MINUTE_SIGN, ARC_SECOND_SIGN, DEGREE_SIGN, FULL_TURN_DEG, HALF_TURN_DEG, MAX_DEGREE,
        MINUTES_IN_DEGREE, QUARTER_TURN_DEG, SECONDS_IN_MINUTE,
    },
    errors::{AngleNotInRange, ParseAngleError},
    Angle, AngleNames,
};

const SECONDS_FD: usize = 2;
const HUNDRED: u32 = pow_10(SECONDS_FD);

/// Coordinate with the additional precision.
/// E.g. the length of the Earth's equator arc second is roughly 30m,
/// so we need more numbers to represent smaller things.
///
/// The current precision (10^-6 degrees) can represent things about 11mm on the equator.
/// <https://en.wikipedia.org/wiki/Decimal_degrees#Precision>
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Default, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct DegreeAngle {
    units: u32,
}

impl Add for DegreeAngle {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if let Some(sum) = self.checked_add(&rhs) {
            return sum;
        }

        // the sum can overflow u32, so convert everything to u64
        let self_ = u64::from(self.units());
        let rhs = u64::from(rhs.units());
        let max = u64::from(Self::max_units());
        assert!(self_ <= max);
        assert!(rhs <= max);
        assert!(self_ + rhs > max);

        (self_ + rhs - max)
            .try_into()
            .map_err(|_| AngleNotInRange::Degrees)
            .and_then(Self::with_units)
            .expect("Wrapping sum around the max degree is always a valid degree")
    }
}

impl CheckedAdd for DegreeAngle {
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        self.units()
            .checked_add(rhs.units())
            .filter(|&sum_units| sum_units <= Self::max_units())
            .and_then(|units| Self::with_units(units).ok())
    }
}

impl Sub for DegreeAngle {
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

impl CheckedSub for DegreeAngle {
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        self.units()
            .checked_sub(rhs.units())
            .and_then(|units| Self::with_units(units).ok())
    }
}

impl AngleNames for DegreeAngle {
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

impl Angle for DegreeAngle {
    type NumErr = AngleNotInRange;
    type ParseErr = ParseAngleError;

    fn obtuse_detected() -> Self::NumErr {
        AngleNotInRange::ObtuseAngle
    }

    fn reflex_detected() -> Self::NumErr {
        AngleNotInRange::ReflexAngle
    }
}

impl DegreeAngle {
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

    const fn max_units() -> u32 {
        Self::units_in_deg() * (MAX_DEGREE as u32)
    }

    // the number of decimal digits
    const PRECISION: u8 = 6;

    // TODO: make this `const` when the `pow` becomes stable
    fn micro_deg_in_deg() -> u32 {
        10_u32.pow(Self::PRECISION.into())
    }

    fn micro_deg_to_unit_coef() -> u32 {
        let (quot, rem) = div_mod(Self::units_in_deg(), Self::micro_deg_in_deg());
        // should be divided without remainder
        assert_eq!(rem, 0);
        quot
    }

    fn cas_in_deg() -> u32 {
        let centi = HUNDRED;
        let sec_in_min = u32::from(SECONDS_IN_MINUTE);
        let min_in_deg = u32::from(MINUTES_IN_DEGREE);
        let sec_in_deg = sec_in_min * min_in_deg;
        centi * sec_in_deg
    }

    fn cas_to_unit_coef() -> u32 {
        let (quot, rem) = div_mod(Self::units_in_deg(), Self::cas_in_deg());
        // should be divided without remainder
        assert_eq!(rem, 0);
        quot
    }

    fn with_deg_and_micro(degrees: u16, micro_degrees: u32) -> Result<Self, AngleNotInRange> {
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

        if !valid_fraction.contains(&micro_degrees) {
            return Err(AngleNotInRange::MicroDegrees);
        }

        let total_micro =
            u64::from(degrees) * u64::from(max_fraction_units) + u64::from(micro_degrees);
        let total_micro = u32::try_from(total_micro).map_err(|_err| AngleNotInRange::Degrees)?;

        let units = Self::micro_deg_to_unit_coef() * total_micro;
        Ok(Self { units })
    }

    /// Degree, minute, second, centisecond
    /// <https://en.wikipedia.org/wiki/Minute_and_second_of_arc>
    pub fn with_dms(
        degree: u16,
        minutes: u8,
        seconds: u8,
        centi_seconds: u8,
    ) -> Result<Self, AngleNotInRange> {
        Self::check_dms(degree, minutes, seconds, centi_seconds)?;

        // prevent further multiplication overflow by extending precision
        let centi = u64::from(HUNDRED);
        let sec_in_min = u64::from(SECONDS_IN_MINUTE);
        let min_in_deg = u64::from(MINUTES_IN_DEGREE);

        let total_minutes = u64::from(degree) * min_in_deg + u64::from(minutes);
        let total_seconds = (total_minutes * sec_in_min) + u64::from(seconds);
        let total_cas = (total_seconds * centi) + u64::from(centi_seconds);

        let total_cas = u32::try_from(total_cas).map_err(|_err| AngleNotInRange::Degrees)?;
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
                0..(HUNDRED as u8),
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

    fn with_units(units: u32) -> Result<Self, AngleNotInRange> {
        if units > Self::max_units() {
            return Err(AngleNotInRange::Degrees);
        }

        Ok(Self { units })
    }

    pub fn degrees(self) -> u16 {
        let degrees = self.units / Self::units_in_deg();
        degrees as u16
    }

    //noinspection SpellCheckingInspection
    pub fn micro_degrees(self) -> u32 {
        let fract_units = self.units % Self::units_in_deg();
        fract_units.div_round(Self::micro_deg_to_unit_coef())
    }

    /// Get the arc minutes component of the angle.
    pub fn arc_minutes(self) -> u8 {
        self.dms_parts(true).1
    }

    /// Get the arc seconds component of the angle.
    pub fn arc_seconds(self) -> u8 {
        self.dms_parts(true).2
    }

    /// Get the centi arc seconds (1/100-th of the arc second) component of the angle.
    ///
    /// Use with caution! The overflow of `0.999_999` degrees
    /// handled incorrectly to keep the `self.degrees()` value valid.
    /// To get the precise values in such a boundary condition,
    /// use the `self.deg_min_sec_cas()` instead.
    pub fn centi_arc_seconds(self) -> u8 {
        self.dms_parts(true).3
    }

    /// If `precise` is true, overflow in minutes will be added to degrees
    fn dms_parts(self, match_degrees: bool) -> (u16, u8, u8, u8) {
        let centi = HUNDRED;
        let sec_in_min = u32::from(SECONDS_IN_MINUTE);
        let min_in_deg = u32::from(MINUTES_IN_DEGREE);

        let total_cas = self.units.div_round(Self::cas_to_unit_coef());
        let (total_seconds, cas) = div_mod(total_cas, centi);
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
            if match_degrees {
                // subtract minimal DMS to prevent overflow in degrees
                let min_dms = Self::with_dms(0, 0, 0, 1).expect("Min DMS is valid");
                // `match_degrees=false` to prevent any possibility of the recursive call
                return (self - min_dms).dms_parts(false);
            }
        }

        (deg, minutes, sec, cas)
    }

    pub fn deg_min_sec_cas(self) -> (u16, u8, u8, u8) {
        self.dms_parts(false)
    }

    const fn units(self) -> u32 {
        self.units
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

impl TryFrom<f64> for DegreeAngle {
    type Error = AngleNotInRange;

    /// Use with caution: the floating numbers has bad precision in the fraction part
    fn try_from(value: f64) -> Result<Self, Self::Error> {
        if value.is_sign_negative() {
            return Err(AngleNotInRange::Degrees);
        }

        // prevent wrapping around
        let integer = value.floor() as u64;
        let integer = integer.try_into().map_err(|_| AngleNotInRange::Degrees)?;

        let fraction = value.fract();
        let precision = Self::micro_deg_in_deg();
        let micro_degrees = (fraction * f64::from(precision)).round() as u32;

        // fraction part of the value rounds up to 1
        if micro_degrees == precision {
            Self::with_deg_and_micro(integer + 1, 0)
        } else {
            Self::with_deg_and_micro(integer, micro_degrees)
        }
    }
}

impl FromStr for DegreeAngle {
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
    static ref RE_UNICODE: Regex = Regex::new(&format!(r#"(?x) # enables verbose mode
        ^                                           # match the whole line from the start
        (?P<deg>[123]?\d{{1,2}})                        # mandatory degree VALUE (0..=399) - requires more validation!
        °                                               # mandatory degree sign
        (?:\x20?                                        # minutes and seconds group optionally started with the space
            (?P<min>[0-5]?\d)                               # minutes VALUE (0..=59)
            ′                                               # arcminute sign
            (?:\x20?                                        # seconds and centiseconds group optionally started with the space
                (?P<sec>[0-5]?\d)                               # whole seconds VALUE (0..=59)
                (?:                                             # centiseconds with the decimal dot
                    \.(?P<cas>\d{{1,{precision}}})                  # centiseconds VALUE (up to [precision] digits, 0..=99)
                )?                                              # centiseconds are optional
                ″                                            # arcsecond sign
            )?                                              # seconds are optional
        )?                                              # minutes and seconds are optional
        $                                           # match the whole line till the end
        "#, precision=SECONDS_FD)).expect("This regex is valid");

    static ref RE_ASCII: Regex = Regex::new(&format!(r#"(?x) # enables verbose mode
        ^                                           # match the whole line from the start
        (?P<deg>[123]?\d{{1,2}})                        # mandatory degree VALUE (0..=399) - requires more validation!
        \*?                                             # optional degree sign (asterisk)
        (?:\x20?                                        # minutes and seconds group optionally started with the space
            (?P<min>[0-5]?\d)                               # minutes VALUE (0..=59)
            '                                               # arcminute sign
            (?:\x20?                                        # seconds and centiseconds group optionally started with the space
                (?P<sec>[0-5]?\d)                               # whole seconds VALUE (0..=59)
                (?:                                             # centiseconds with the decimal dot
                    \.(?P<cas>\d{{1,{precision}}})                  # centiseconds VALUE (up to [precision] digits, 0..=99)
                )?                                              # centiseconds are optional
                "                                               # arcsecond sign
            )?                                              # seconds are optional
        )?                                              # minutes and seconds are optional
        $                                           # match the whole line till the end
        "#, precision=SECONDS_FD)).expect("This regex is valid");
}

impl DegreeAngle {
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
        let cas = if let Some(capture) = capture.name("cas") {
            let cas = format!("{:0<width$}", capture.as_str(), width = SECONDS_FD);
            cas.parse()?
        } else {
            0
        };
        let good = Self::with_dms(deg, min, sec, cas)?;
        Ok(good)
    }
}

impl fmt::Display for DegreeAngle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // DMS
        if f.alternate() {
            let (deg, arc_min, arc_sec, cas) = self.deg_min_sec_cas();
            write!(f, "{}{}", deg, DEGREE_SIGN)?;

            if (arc_min != 0) || (arc_sec != 0) || (cas != 0) {
                write!(f, "{}{}", arc_min, ARC_MINUTE_SIGN)?;
            }

            if (arc_sec != 0) || (cas != 0) {
                if cas == 0 {
                    write!(f, "{}{}", arc_sec, ARC_SECOND_SIGN)
                } else {
                    let arc_sec = f64::from(arc_sec) + f64::from(cas) / f64::from(HUNDRED);
                    write!(f, "{}{}", arc_sec, ARC_SECOND_SIGN)
                }
            } else {
                Ok(())
            }
        } else {
            let (deg, m_deg) = (self.degrees(), self.micro_degrees());
            if m_deg == 0 {
                write!(f, "{}{}", deg, DEGREE_SIGN)
            } else {
                write!(
                    f,
                    "{}.{:0>width$}{}",
                    deg,
                    m_deg,
                    DEGREE_SIGN,
                    width = Self::PRECISION.into()
                )
            }
        }
    }
}

impl TryFrom<(u16, u8, u8, u8)> for DegreeAngle {
    type Error = AngleNotInRange;

    fn try_from(value: (u16, u8, u8, u8)) -> Result<Self, Self::Error> {
        let (deg, min, sec, centi) = value;
        Self::with_dms(deg, min, sec, centi)
    }
}

impl TryFrom<[u16; 4]> for DegreeAngle {
    type Error = AngleNotInRange;

    fn try_from(value: [u16; 4]) -> Result<Self, Self::Error> {
        let [deg, min, sec, centi] = value;
        let min = min.try_into().map_err(|_| AngleNotInRange::ArcMinutes)?;
        let sec = sec.try_into().map_err(|_| AngleNotInRange::ArcSeconds)?;
        let centi = centi
            .try_into()
            .map_err(|_| AngleNotInRange::ArcCentiSeconds)?;
        Self::with_dms(deg, min, sec, centi)
    }
}

try_from_tuples_and_arrays!((DegreeAngle, AngleNotInRange) <- u16, u8, u8, u8; u16);

#[cfg(test)]
mod tests {
    use std::mem::size_of;

    use super::*;

    #[test]
    fn degree_angle_is_32_bits() {
        assert_eq!(size_of::<DegreeAngle>(), 4)
    }

    #[test]
    fn default() {
        let zero_angle = DegreeAngle::default();
        assert!(zero_angle.is_zero());

        assert_eq!(zero_angle.degrees(), 0);
        assert_eq!(zero_angle.micro_degrees(), 0);
        assert_eq!(zero_angle.units(), 0);

        assert_eq!(zero_angle.arc_minutes(), 0);
        assert_eq!(zero_angle.arc_seconds(), 0);
        assert_eq!(zero_angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn max_valid_value() {
        let north_pole: DegreeAngle = 180.try_into().unwrap();
        assert!(north_pole.is_straight());
        assert_eq!(north_pole.degrees(), 180);
        assert_eq!(north_pole.micro_degrees(), 0);
        assert_eq!(north_pole.units(), 1_620_000_000);

        assert_eq!(north_pole.arc_minutes(), 0);
        assert_eq!(north_pole.arc_seconds(), 0);
        assert_eq!(north_pole.centi_arc_seconds(), 0);

        let north_pole2: DegreeAngle = DegreeAngle::with_dms(180, 0, 0, 0).unwrap();
        assert_eq!(north_pole2, north_pole);
    }

    /// <https://en.wikipedia.org/wiki/Tropic_of_Capricorn>
    #[test]
    fn intermediate() {
        let polar_circle = DegreeAngle::with_deg_and_micro(66, 563_334).unwrap();
        assert!(polar_circle.is_acute());
        assert_eq!(polar_circle.degrees(), 66);
        assert_eq!(polar_circle.micro_degrees(), 563_334);

        assert_eq!(polar_circle.arc_minutes(), 33);
        assert_eq!(polar_circle.arc_seconds(), 48);
        assert_eq!(polar_circle.centi_arc_seconds(), 0);
    }

    #[test]
    fn bigger_than_straight_is_valid() {
        let angle = DegreeAngle::with_deg_and_micro(200, 0).unwrap();
        assert!(angle.is_reflex());
        assert_eq!(angle.degrees(), 200);
        assert_eq!(angle.micro_degrees(), 0);

        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn bigger_than_straight_dms() {
        let angle = DegreeAngle::with_dms(181, 0, 2, 11).unwrap();
        assert!(angle.is_reflex());
        assert_eq!(angle.degrees(), 181);

        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 2);
        assert_eq!(angle.centi_arc_seconds(), 11);
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn bigger_than_complete() {
        let _a = DegreeAngle::with_deg_and_micro(365, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn bigger_than_complete_degree() {
        let _a = DegreeAngle::with_dms(361, 0, 0, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcMinutes")]
    fn bigger_than_complete_minute() {
        let _a = DegreeAngle::with_dms(360, 5, 0, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcSeconds")]
    fn bigger_than_complete_second() {
        let _a = DegreeAngle::with_dms(360, 0, 2, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcCentiSeconds")]
    fn bigger_than_complete_milli_second() {
        let _a = DegreeAngle::with_dms(360, 0, 0, 1).unwrap();
    }

    #[test]
    #[should_panic(expected = "MicroDegrees")]
    fn bigger_than_complete_minimum_fraction() {
        let _a = DegreeAngle::with_deg_and_micro(360, 1).unwrap();
    }

    #[test]
    fn complete() {
        let angle = DegreeAngle::with_deg_and_micro(360, 0).unwrap();
        assert!(angle.is_complete());
        assert_eq!(angle.degrees(), 360);
        assert_eq!(angle.micro_degrees(), 0);

        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    #[should_panic(expected = "ArcMinutes")]
    fn bad_minutes() {
        let _a = DegreeAngle::with_dms(30, 60, 60, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcSeconds")]
    fn bad_seconds() {
        let _a = DegreeAngle::with_dms(30, 59, 60, 0).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcSeconds")]
    fn bad_seconds_2() {
        let _a = DegreeAngle::with_dms(30, 59, 100, 0).unwrap();
    }

    #[test]
    fn good_milli_seconds() {
        let angle = DegreeAngle::with_dms(30, 59, 0, 99).unwrap();
        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 99);
    }

    #[test]
    #[should_panic(expected = "ArcCentiSeconds")]
    fn bad_milli_seconds() {
        let _a = DegreeAngle::with_dms(30, 59, 0, 100).unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcCentiSeconds")]
    fn bad_milli_seconds_2() {
        let _a = DegreeAngle::with_dms(30, 59, 0, 150).unwrap();
    }

    #[test]
    fn from_f64() {
        let angle = DegreeAngle::try_from(23.499_999).unwrap();
        assert!(angle.is_acute());

        let angle2 = DegreeAngle::with_deg_and_micro(23, 499_999).unwrap();
        assert_eq!(angle, angle2);
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn from_f64_deg_overflow() {
        let _a = DegreeAngle::try_from(425.0).unwrap();
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn from_f64_wrap_around_u16() {
        let angle: DegreeAngle = 65566.5.try_into().unwrap();

        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 30);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_u16() {
        let angle: DegreeAngle = 300.try_into().unwrap();
        assert!(angle.is_reflex());

        assert_eq!(angle.degrees(), 300);
        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_u8() {
        let angle = DegreeAngle::with_deg_and_micro(108, 0).unwrap();
        assert!(angle.is_obtuse());

        let angle2 = 108.try_into().unwrap();
        assert_eq!(angle, angle2);
    }

    #[test]
    fn from_pair() {
        let angle: DegreeAngle = (7, 59).try_into().unwrap();
        assert_eq!(angle.degrees(), 7);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_triple() {
        let angle: DegreeAngle = (117, 59, 3).try_into().unwrap();
        assert_eq!(angle.degrees(), 117);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_quadruple() {
        let angle: DegreeAngle = (317, 59, 3, 90).try_into().unwrap();
        assert_eq!(angle.degrees(), 317);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.centi_arc_seconds(), 90);
    }

    #[test]
    fn from_ar2() {
        let angle: DegreeAngle = [40, 15].try_into().unwrap();
        assert_eq!(angle.degrees(), 40);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_ar3() {
        let angle: DegreeAngle = [320, 15, 8].try_into().unwrap();
        assert_eq!(angle.degrees(), 320);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 8);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn from_ar4() {
        let angle: DegreeAngle = [120, 15, 8, 36].try_into().unwrap();
        assert_eq!(angle.degrees(), 120);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 8);
        assert_eq!(angle.centi_arc_seconds(), 36);
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn from_int_overflow() {
        let _angle: DegreeAngle = [500, 15, 8, 36].try_into().unwrap();
    }

    #[test]
    #[should_panic(expected = "ArcMinutes")]
    fn from_ar4_overflow() {
        let _angle: DegreeAngle = [120, 300, 8, 36].try_into().unwrap();
    }

    #[test]
    fn good_fraction_minus_one_is_overflow() {
        let angle = DegreeAngle::with_deg_and_micro(30, 999_999).unwrap();
        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.micro_degrees(), 999_999);

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
        let angle = DegreeAngle::with_deg_and_micro(30, 999_998).unwrap();
        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.micro_degrees(), 999_998);

        assert_eq!(angle.degrees(), 30);
        assert_eq!(angle.arc_minutes(), 59);
        assert_eq!(angle.arc_seconds(), 59);
        assert_eq!(angle.centi_arc_seconds(), 99);
    }

    #[test]
    #[should_panic(expected = "MicroDegrees")]
    fn bad_fraction() {
        let _a = DegreeAngle::with_deg_and_micro(30, 10_000_000).unwrap();
    }

    #[test]
    #[should_panic(expected = "MicroDegrees")]
    fn bad_fraction_2() {
        let _a = DegreeAngle::with_deg_and_micro(30, 15_000_000).unwrap();
    }

    #[test]
    fn test_very_small_angles() {
        for f in 0..1000 {
            let angle = DegreeAngle::with_deg_and_micro(0, f).unwrap();
            assert_eq!(angle.degrees(), 0);
            assert_eq!(angle.micro_degrees(), f);
            assert_eq!(angle.units(), f * 9);
        }
    }

    #[test]
    #[ignore]
    fn test_first_degree_every_fraction_with_step_1() {
        let mut prev = None;
        for f in 0..10_000_000 {
            let angle = DegreeAngle::with_deg_and_micro(0, f).unwrap();
            assert_eq!(angle.degrees(), 0);
            assert_eq!(angle.micro_degrees(), f);
            if let Some(prev) = prev {
                assert!(angle > prev);
                assert_eq!(angle - prev, DegreeAngle::with_deg_and_micro(0, 1).unwrap());
            }

            prev = Some(angle);
        }
    }

    fn round_trip(deg: u16, min: u8, sec: u8, centi_sec: u8) {
        eprintln!("\n\n================");
        let angle = DegreeAngle::with_dms(deg, min, sec, centi_sec).unwrap();
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
        let angle = DegreeAngle::with_dms(156, 59, 59, 99).unwrap();

        assert_eq!(angle.degrees(), 156);
        assert_eq!(angle.micro_degrees(), 999_997);
    }

    #[test]
    fn print_fraction() {
        let d = DegreeAngle::with_deg_and_micro(60, 546_718).unwrap();
        assert_eq!(d.to_string(), "60.546718°")
    }

    #[test]
    fn print_fraction_almost_integer() {
        let almost_20 =
            DegreeAngle::try_from(20).unwrap() - DegreeAngle::with_deg_and_micro(0, 1).unwrap();

        assert_eq!(almost_20.to_string(), "19.999999°")
    }

    #[test]
    fn print_fraction_very_small() {
        let almost_zero = DegreeAngle::with_deg_and_micro(0, 1).unwrap();
        assert_eq!(almost_zero.to_string(), "0.000001°")
    }

    #[test]
    fn print_zero() {
        let d = DegreeAngle::default();
        assert_eq!(d.to_string(), "0°")
    }

    #[test]
    fn print_zero_as_dms() {
        let d = DegreeAngle::default();
        let s = format!("{:#}", d);
        assert_eq!(s, "0°")
    }

    #[test]
    fn print_right() {
        let d = DegreeAngle::try_from(90).unwrap();
        assert_eq!(d.to_string(), "90°")
    }

    #[test]
    fn print_right_as_dms() {
        let d: DegreeAngle = 90.try_into().unwrap();
        let s = format!("{:#}", d);
        assert_eq!(s, "90°")
    }

    #[test]
    fn print_fraction_as_dms() {
        let d = DegreeAngle::with_deg_and_micro(60, 546_718).unwrap();
        let s = format!("{:#}", d);
        assert_eq!(s, "60°32′48.18″")
    }

    #[test]
    fn print_fraction_as_dms_without_milli() {
        for f in 0..3 {
            let d = DegreeAngle::with_deg_and_micro(60, 546_666 + f).unwrap();
            let s = format!("{:#}", d);
            assert_eq!(s, "60°32′48″");
        }
    }

    #[test]
    fn print_fraction_as_dms_without_seconds() {
        for f in 0..3 {
            let d = DegreeAngle::with_deg_and_micro(60, 533_332 + f).unwrap();
            let s = format!("{:#}", d);
            assert_eq!(s, "60°32′");
        }
    }

    #[test]
    fn print_overflow_fraction_as_dms() {
        let d = DegreeAngle::with_deg_and_micro(59, 999_999).unwrap();
        let s = format!("{:#}", d);
        assert_eq!(s, "60°")
    }

    #[test]
    fn add() {
        let first = DegreeAngle::with_dms(118, 51, 27, 95).unwrap();
        let second = DegreeAngle::with_dms(47, 38, 19, 75).unwrap();
        let sum = first + second;

        assert_eq!(sum.degrees(), 166);
        assert_eq!(sum.arc_minutes(), 29);
        assert_eq!(sum.arc_seconds(), 47);
        assert_eq!(sum.centi_arc_seconds(), 70);
    }

    #[test]
    fn add_minimal_overflow() {
        let max = DegreeAngle::complete();
        let min = DegreeAngle::with_deg_and_micro(0, 1).unwrap();

        let add_res = max.checked_add(&min);
        assert!(add_res.is_none());

        // wrapped around
        assert_eq!(max + min, DegreeAngle::with_deg_and_micro(0, 1).unwrap());
    }

    #[test]
    fn add_with_wrapping() {
        let first = DegreeAngle::with_dms(256, 18, 0, 60).unwrap();
        let second = (153, 4, 0, 0).try_into().unwrap();

        // wrapped around
        assert!((first + second).almost_equal((49, 22, 0, 60).try_into().unwrap()));
    }

    #[test]
    fn add_no_overflow() {
        let max = DegreeAngle::straight();
        let min = DegreeAngle::with_deg_and_micro(0, 1).unwrap();

        let res = max
            .checked_sub(&min)
            .and_then(|sub| sub.checked_add(&min))
            .unwrap();
        assert!(res.is_straight());
    }

    #[test]
    fn summing_dms_does_not_accumulate_errors() {
        let min = DegreeAngle::with_dms(0, 0, 0, 1).unwrap();

        let mut acc = DegreeAngle::zero();

        for _ in 0..10 {
            acc = acc + min;
        }

        assert_eq!(acc.centi_arc_seconds(), 10);
    }

    #[test]
    fn sub() {
        let first = DegreeAngle::with_dms(318, 51, 27, 96).unwrap();
        let second = DegreeAngle::with_dms(47, 38, 19, 74).unwrap();
        let sum = first - second;

        assert_eq!(sum.degrees(), 271);
        assert_eq!(sum.arc_minutes(), 13);
        assert_eq!(sum.arc_seconds(), 8);
        assert_eq!(sum.centi_arc_seconds(), 22);
    }

    #[test]
    fn sub_underflow() {
        let first = DegreeAngle::with_dms(47, 38, 19, 74).unwrap();
        let second = DegreeAngle::with_dms(47, 38, 19, 75).unwrap();
        let sum = first.checked_sub(&second);
        assert!(sum.is_none());
    }

    #[test]
    fn sub_with_zero_res() {
        let first = DegreeAngle::with_dms(47, 38, 19, 74).unwrap();
        let second = DegreeAngle::with_dms(47, 38, 19, 74).unwrap();
        let sum = first.checked_sub(&second).unwrap();
        assert!(sum.is_zero());
    }

    #[test]
    fn complementary() {
        let angle: DegreeAngle = 79.888_889.try_into().unwrap();
        dbg!(angle.units);
        let comp = angle.complement().unwrap();
        assert_eq!(comp.degrees(), 10);
        assert_eq!(comp.micro_degrees(), 111_111);
    }

    #[test]
    fn complementary_dms() {
        let angle = DegreeAngle::with_dms(47, 38, 19, 74).unwrap();
        let supp = angle.complement().unwrap();
        assert_eq!(supp.degrees(), 42);
        assert_eq!(supp.arc_minutes(), 21);
        assert_eq!(supp.arc_seconds(), 40);
        assert_eq!(supp.centi_arc_seconds(), 26);
    }

    #[test]
    fn complement_of_obtuse_undefined() {
        let angle = DegreeAngle::with_dms(117, 38, 19, 74).unwrap();
        assert!(angle.complement().is_none());
    }

    #[test]
    fn supplementary() {
        let angle: DegreeAngle = 30.98765.try_into().unwrap();
        let supp = angle.supplement().unwrap();
        assert_eq!(supp.degrees(), 149);
        assert_eq!(supp.micro_degrees(), 12_350);
    }

    #[test]
    fn supplementary_dms() {
        let angle = DegreeAngle::with_dms(157, 44, 3, 11).unwrap();
        let supp = angle.supplement().unwrap();
        assert_eq!(supp.degrees(), 22);
        assert_eq!(supp.arc_minutes(), 15);
        assert_eq!(supp.arc_seconds(), 56);
        assert_eq!(supp.centi_arc_seconds(), 89);
    }

    #[test]
    fn supplement_of_reflex_undefined() {
        let angle = DegreeAngle::with_dms(190, 38, 19, 74).unwrap();
        assert!(angle.supplement().is_none());
    }

    #[test]
    fn explementary() {
        let angle: DegreeAngle = 130.98765.try_into().unwrap();
        let exp = angle.explement();
        assert_eq!(exp.degrees(), 229);
        assert_eq!(exp.micro_degrees(), 12_350);
    }

    #[test]
    fn explementary_dms() {
        let angle = DegreeAngle::with_dms(275, 44, 3, 11).unwrap();
        let exp = angle.explement();
        assert_eq!(exp.degrees(), 84);
        assert_eq!(exp.arc_minutes(), 15);
        assert_eq!(exp.arc_seconds(), 56);
        assert_eq!(exp.centi_arc_seconds(), 89);
    }

    #[test]
    fn explement_of_obtuse_is_reflex() {
        let angle = DegreeAngle::with_dms(95, 38, 19, 74).unwrap();
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
        let angle: DegreeAngle = s.parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.micro_degrees(), 0);

        assert_eq!(angle, DegreeAngle::with_dms(54, 0, 0, 0).unwrap());
    }

    #[test]
    fn simple_integer_with_degree_sign() {
        let s = "54°";
        let angle: DegreeAngle = s.parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.micro_degrees(), 0);

        assert_eq!(angle, DegreeAngle::with_dms(54, 0, 0, 0).unwrap());
    }

    #[test]
    fn simple_decimal() {
        let angle: DegreeAngle = "54.145".parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.micro_degrees(), 145_000);
    }

    #[test]
    fn simple_decimal_with_degree_sign() {
        let angle: DegreeAngle = "54.145°".parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.micro_degrees(), 145_000);
    }

    #[test]
    fn too_precise_truncation() {
        let angle: DegreeAngle = "54.123456789".parse().unwrap();
        assert_eq!(angle.degrees(), 54);
        assert_eq!(angle.micro_degrees(), 123_457);
    }

    #[test]
    fn round_down_more_than_6_digits() {
        let angle: DegreeAngle = "18.9999994°".parse().unwrap();
        assert_eq!(angle.degrees(), 18);
        assert_eq!(angle.micro_degrees(), 999_999);
    }

    #[test]
    fn round_up_more_than_7_digits() {
        let angle: DegreeAngle = "18.99999995°".parse().unwrap();
        assert_eq!(angle.degrees(), 19);
        assert_eq!(angle.micro_degrees(), 0);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn bad_float() {
        let _angle: DegreeAngle = "54.123456.789".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn bad_negative() {
        let _angle: DegreeAngle = "-54.12".parse().unwrap();
    }

    #[test]
    fn big_but_valid() {
        let angle: DegreeAngle = "278.123456".parse().unwrap();
        assert_eq!(angle.degrees(), 278);
        assert_eq!(angle.micro_degrees(), 123_456);
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn bad_too_big_for_angle() {
        let _angle: DegreeAngle = "364.123456".parse().unwrap();
    }

    #[test]
    fn simple_deg() {
        let angle: DegreeAngle = "28°".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min() {
        let angle: DegreeAngle = "28°15′".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec() {
        let angle: DegreeAngle = "28°05′33″".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 5);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec_mas() {
        let angle: DegreeAngle = "98°15′33.15″".parse().unwrap();
        assert_eq!(angle.degrees(), 98);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    fn uneven_digits_deg_min_sec_mas() {
        let angle: DegreeAngle = "128°4′16.15″".parse().unwrap();
        assert_eq!(angle.degrees(), 128);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    fn single_digit_deg_min_sec_mas() {
        let angle: DegreeAngle = "1°2′3.4″".parse().unwrap();
        assert_eq!(angle.degrees(), 1);
        assert_eq!(angle.arc_minutes(), 2);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.centi_arc_seconds(), 40);
    }

    #[test]
    fn more_than_straight_is_valid() {
        let angle: DegreeAngle = "228°4′16.15″".parse().unwrap();
        assert_eq!(angle.degrees(), 228);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_deg_digits() {
        let _angle: DegreeAngle = "428°4′16.15″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_min_digits() {
        let _angle: DegreeAngle = "81°72′".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_sec_digits() {
        let _angle: DegreeAngle = "28°10′66.15″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_milli_digits() {
        let _angle: DegreeAngle = "28°40′16.151″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn overflow_in_domain_deg() {
        let _angle: DegreeAngle = "361°40′".parse().unwrap();
    }

    #[test]
    fn space_between_deg_and_min() {
        let angle: DegreeAngle = "81° 12′14″".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn space_between_min_and_sec() {
        let angle: DegreeAngle = "81°12′ 14.98″".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 98);
    }

    #[test]
    fn spaces_between_parts() {
        let angle: DegreeAngle = "81° 12′ 14.7″".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 70);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn spaces_between_parts_and_milliseconds() {
        let _angle: DegreeAngle = "81° 12′ 14. 7″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn skipping_degree_is_not_allowed_in_unicode_mode() {
        let _angle: DegreeAngle = "34 49′8″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn space_between_degree_val_and_sign_not_allowed() {
        let _angle: DegreeAngle = "34 °49′8″".parse().unwrap();
    }
}

#[cfg(test)]
mod parse_ascii_tests {
    use super::*;

    #[test]
    fn simple_deg() {
        let angle: DegreeAngle = "28*".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 0);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min() {
        let angle: DegreeAngle = "28*15'".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 0);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec() {
        let angle: DegreeAngle = "28*05'33\"".parse().unwrap();
        assert_eq!(angle.degrees(), 28);
        assert_eq!(angle.arc_minutes(), 5);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn deg_min_sec_mas() {
        let angle: DegreeAngle = "98*15'33.15\"".parse().unwrap();
        assert_eq!(angle.degrees(), 98);
        assert_eq!(angle.arc_minutes(), 15);
        assert_eq!(angle.arc_seconds(), 33);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    fn uneven_digits_deg_min_sec_mas() {
        let angle: DegreeAngle = r#"128*4'16.15""#.parse().unwrap();
        assert_eq!(angle.degrees(), 128);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    fn single_digit_deg_min_sec_mas() {
        let angle: DegreeAngle = "1*2'3.4\"".parse().unwrap();
        assert_eq!(angle.degrees(), 1);
        assert_eq!(angle.arc_minutes(), 2);
        assert_eq!(angle.arc_seconds(), 3);
        assert_eq!(angle.centi_arc_seconds(), 40);
    }

    #[test]
    fn more_than_straight_is_valid() {
        let angle: DegreeAngle = "228*4'16.15\"".parse().unwrap();
        assert_eq!(angle.degrees(), 228);
        assert_eq!(angle.arc_minutes(), 4);
        assert_eq!(angle.arc_seconds(), 16);
        assert_eq!(angle.centi_arc_seconds(), 15);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_deg_digits() {
        let _angle: DegreeAngle = "428*4'16.15\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_min_digits() {
        let _angle: DegreeAngle = "81*72'".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_sec_digits() {
        let _angle: DegreeAngle = "28*10'66.15\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn overflow_in_milli_digits() {
        let _angle: DegreeAngle = "28*40'16.151\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "AngleNotInRange(Degrees)")]
    fn overflow_in_domain_deg() {
        let _angle: DegreeAngle = "361*40'".parse().unwrap();
    }

    #[test]
    fn space_between_deg_and_min() {
        let angle: DegreeAngle = "81* 12'14\"".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    fn space_between_min_and_sec() {
        let angle: DegreeAngle = "81*12' 14.98\"".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 98);
    }

    #[test]
    fn spaces_between_parts() {
        let angle: DegreeAngle = "81* 12' 14.7\"".parse().unwrap();
        assert_eq!(angle.degrees(), 81);
        assert_eq!(angle.arc_minutes(), 12);
        assert_eq!(angle.arc_seconds(), 14);
        assert_eq!(angle.centi_arc_seconds(), 70);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn spaces_between_parts_and_milliseconds() {
        let _angle: DegreeAngle = "81* 12' 14. 7\"".parse().unwrap();
    }

    #[test]
    fn skipping_degree_is_allowed_in_ascii_mode() {
        let angle: DegreeAngle = "34 49'8\"".parse().unwrap();
        assert_eq!(angle.degrees(), 34);
        assert_eq!(angle.arc_minutes(), 49);
        assert_eq!(angle.arc_seconds(), 8);
        assert_eq!(angle.centi_arc_seconds(), 0);
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn skipping_minutes_sign_is_not_allowed_in_ascii_mode() {
        let _angle: DegreeAngle = "34 49 8\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn skipping_seconds_sign_is_not_allowed_in_ascii_mode() {
        let _angle: DegreeAngle = "34 49'8".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn space_between_degree_val_and_sign_not_allowed() {
        let _angle: DegreeAngle = "34 *49'8\"".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn mixed_ascii_deg_and_unicode() {
        let _angle: DegreeAngle = "34*49′8″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn mixed_ascii_min_and_unicode() {
        let _angle: DegreeAngle = "34°49'8″".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "DmsNotation")]
    fn mixed_ascii_sec_and_unicode() {
        let _angle: DegreeAngle = "34°49′8\"".parse().unwrap();
    }
}
