pub const MAX_DEGREE: u16 = 360;
pub const MINUTES_IN_DEGREE: u8 = 60;
pub const SECONDS_IN_MINUTE: u8 = 60;

pub const DEGREE_SIGN: char = '°';
pub const ARC_MINUTE_SIGN: char = '′';
pub const ARC_SECOND_SIGN: char = '″';

pub const FULL_TURN_DEG: u16 = MAX_DEGREE;
pub const HALF_TURN_DEG: u16 = FULL_TURN_DEG >> 1;
pub const QUARTER_TURN_DEG: u16 = HALF_TURN_DEG >> 1;

#[doc(hidden)]
#[macro_export]
/// Implement the Angle traits for the type representing degrees
macro_rules! impl_angle_traits {
    ($t:ty) => {
        impl AngleNames for $t {
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

        impl Angle for $t {
            type NumErr = AngleNotInRange;
            type ParseErr = ParseAngleError;

            fn obtuse_err() -> Self::NumErr {
                AngleNotInRange::ObtuseAngle
            }

            fn reflex_err() -> Self::NumErr {
                AngleNotInRange::ReflexAngle
            }

            fn turn_err() -> Self::NumErr {
                AngleNotInRange::Degrees
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
/// Implement the conversion traits for the type representing degrees
macro_rules! impl_conv_traits {
    ($t:ty, $fraction_multiplier_func:ident, $dms_parts_func:ident, $arc_sec_precision:ident) => {
        impl FromStr for $t {
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

        impl TryFrom<f64> for $t {
            type Error = AngleNotInRange;

            /// Use with caution: the floating numbers has bad precision in the fraction part
            fn try_from(value: f64) -> Result<Self, Self::Error> {
                if value.is_sign_negative() {
                    return Err(AngleNotInRange::Degrees);
                }

                // prevent wrapping around
                let integer = value.floor() as u64;
                let integer = integer.try_into().map_err(|_| AngleNotInRange::Degrees)?;

                let precision = Self::$fraction_multiplier_func();
                let fraction = (value.fract() * f64::from(precision)).round() as u64;
                let fraction = fraction
                    .try_into()
                    .map_err(|_| AngleNotInRange::DegreeFraction)?;

                // fraction part of the value rounds up to 1
                if fraction == precision {
                    Self::with_deg_and_fraction(integer + 1, 0)
                } else {
                    Self::with_deg_and_fraction(integer, fraction)
                }
            }
        }

        impl Into<f64> for $t {
            fn into(self) -> f64 {
                let degrees = f64::from(self.degrees());
                let fract =
                    f64::from(self.deg_fract()) / f64::from(Self::$fraction_multiplier_func());
                degrees + fract
            }
        }

        impl $t {
            fn parse_dms(s: &str) -> Result<Self, ParseAngleError> {
                let capture = RE_UNICODE
                    .captures(s)
                    .or_else(|| RE_ASCII.captures(s))
                    .ok_or(ParseAngleError::DmsNotation)?;
                let deg = capture.name("deg").ok_or(ParseAngleError::DmsNotation)?;
                let deg = deg.as_str().parse()?;

                let min = capture.name("min").map_or("0", |m| m.as_str()).parse()?;
                let sec = capture.name("sec").map_or("0", |m| m.as_str()).parse()?;
                let sec_fraction = if let Some(capture) = capture.name("sec_fract") {
                    let sec_fraction =
                        format!("{:0<width$}", capture.as_str(), width = Self::SECONDS_FD);
                    sec_fraction.parse()?
                } else {
                    0
                };

                let good = Self::with_dms(deg, min, sec, sec_fraction)?;
                Ok(good)
            }
        }

        impl fmt::Display for $t {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                // DMS
                if f.alternate() {
                    let (deg, arc_min, arc_sec, sec_fraction) = self.$dms_parts_func();
                    write!(f, "{}{}", deg, DEGREE_SIGN)?;

                    if (arc_min != 0) || (arc_sec != 0) || (sec_fraction != 0) {
                        write!(f, "{}{}", arc_min, ARC_MINUTE_SIGN)?;
                    }

                    if (arc_sec != 0) || (sec_fraction != 0) {
                        if sec_fraction == 0 {
                            write!(f, "{}{}", arc_sec, ARC_SECOND_SIGN)
                        } else {
                            let arc_sec = f64::from(arc_sec)
                                + f64::from(sec_fraction) / f64::from(Self::$arc_sec_precision);
                            write!(f, "{}{}", arc_sec, ARC_SECOND_SIGN)
                        }
                    } else {
                        Ok(())
                    }
                } else {
                    let (deg, m_deg) = (self.degrees(), self.deg_fract());
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
    };
}

/// Construct regular expression to parse Degree-Minute-Second representation of an angle
pub(super) fn parse_dms_re(is_ascii: bool, arc_seconds_fd: usize) -> String {
    let (deg, min, sec) = if is_ascii {
        ("[\\*°]?", '\'', '"')
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
