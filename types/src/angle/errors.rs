use std::{
    error::Error,
    fmt,
    num::{ParseFloatError, ParseIntError},
};

use crate::enum_trivial_from_impl;

#[derive(Debug, Copy, Clone)]
pub enum OutOfRange {
    Degrees,         // deg > 360
    ReflexAngle,     // deg > 180
    ObtuseAngle,     // deg > 90
    ArcMinutes,      // min >= 60
    ArcSeconds,      // sec >= 60
    ArcCentiSeconds, // cas >= 100
    ArcMilliSeconds, // mas >= 1000
    MicroDegrees,    // microdeg >= 10^6
    DegreeFraction,  // microdeg >= 10^7
}

impl fmt::Display for OutOfRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = match self {
            Self::Degrees => "Too big value for degrees part of an angle (max is 360)",
            Self::ReflexAngle => {
                "Only straight angles or less (<=180) are allowed, but reflex one provided"
            }
            Self::ObtuseAngle => {
                "Only right angles or less (<=90) are allowed, but obtuse one provided"
            }
            Self::MicroDegrees => "Micro degrees exceeds maximum",
            Self::DegreeFraction => "Degree fraction exceeds maximum",
            Self::ArcMinutes => "Angle's arc minute value not in range [0..60)",
            Self::ArcSeconds => "Angle's arc second value not in range [0..60)",
            Self::ArcCentiSeconds => "Angle's arc centisecond should be less than 100",
            Self::ArcMilliSeconds => "Angle's arc millisecond should be less than 1000",
        };

        write!(f, "{msg}")
    }
}

impl Error for OutOfRange {}

#[derive(Debug)]
pub enum ParseAngleError {
    Range(OutOfRange),
    Float(ParseFloatError),
    // this variant is practically impossible due to regex digits limitations
    Int(ParseIntError),
    DmsNotation,
}

enum_trivial_from_impl!(OutOfRange => ParseAngleError:Range);
enum_trivial_from_impl!(ParseFloatError => ParseAngleError:Float);
enum_trivial_from_impl!(ParseIntError => ParseAngleError:Int);

impl fmt::Display for ParseAngleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Cannot parse angle: ")?;
        match self {
            Self::Range(inner) => write!(f, "{inner}"),
            Self::Float(inner) => write!(f, "{inner}"),
            Self::Int(inner) => write!(f, "{inner}"),
            Self::DmsNotation => write!(f, "not a Degree-Minute-Second notation"),
        }
    }
}

impl Error for ParseAngleError {}
