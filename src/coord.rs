use std::{convert::TryFrom, error::Error, fmt, str::FromStr};

use crate::{angle::Angle, utils::StripChar};

pub use self::{
    lat::{
        Latitude,
        Pole::{self},
    },
    lon::Longitude,
    point::Point,
};

mod lat;
mod lon;
mod point;

#[derive(Debug)]
pub enum ParseCoordinateError<A: Error> {
    Angle(A),
    EmptyString,
    NoHemisphere,
}

impl<A: Error> From<A> for ParseCoordinateError<A> {
    fn from(err: A) -> Self {
        Self::Angle(err)
    }
}

impl<A: Error> fmt::Display for ParseCoordinateError<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Coordinate parsing failed: ")?;
        match self {
            Self::Angle(inner) => write!(f, "{}", inner),
            Self::EmptyString => write!(f, "empty string provided"),
            Self::NoHemisphere => write!(f, "direction (hemisphere) was not detected"),
        }
    }
}

impl<A: Error> Error for ParseCoordinateError<A> {}

/// Parse the '+' and '-' signs into coordinate's direction
trait FromSign: Sized {
    fn from_sign(sign: char) -> Option<Self>;
}

trait AngleAndDirection<A: Angle>: Sized {
    type Direction;

    fn with_angle_and_direction(angle: A, direction: Self::Direction) -> Result<Self, A::NumErr>;
}

trait ParsedCoordinate<A>: AngleAndDirection<A>
where
    A: Angle + FromStr<Err = <A as Angle>::ParseErr>,
    A::NumErr: Into<A::ParseErr>,
{
    fn with_angle_only(angle: A) -> Option<Self>;

    fn with_str_angle_and_direction(
        angle_str: &str,
        direction: Self::Direction,
    ) -> Result<Self, A::ParseErr> {
        let angle = angle_str.parse()?;
        Ok(Self::with_angle_and_direction(angle, direction).map_err(Into::into)?)
    }

    fn parse(s: &str) -> Result<Self, ParseCoordinateError<A::ParseErr>>
    where
        Self::Direction: TryFrom<char> + FromSign,
    {
        if s.is_empty() {
            return Err(ParseCoordinateError::EmptyString);
        }

        let (mut rest, last) = s.split_last().expect("suffix should be stripped");
        if let Ok(direction) = Self::Direction::try_from(last) {
            // single space is allowed
            if rest.ends_with(' ') {
                assert_eq!(rest.pop(), Some(' '));
            }
            return Self::with_str_angle_and_direction(&rest, direction)
                .map_err(ParseCoordinateError::Angle);
        }

        let (first, mut rest) = s.split_first().expect("prefix should be stripped");
        if let Ok(direction) = Self::Direction::try_from(first) {
            // single space is allowed
            if rest.starts_with(' ') {
                assert_eq!(rest.remove(0), ' ');
            }
            return Self::with_str_angle_and_direction(&rest, direction)
                .map_err(ParseCoordinateError::Angle);
        }

        if let Some(pole) = Self::Direction::from_sign(first) {
            // no space is allowed
            return Self::with_str_angle_and_direction(&rest, pole)
                .map_err(ParseCoordinateError::Angle);
        }

        // for some values neither prefix nor suffix is required
        // only angle's value itself is sufficient
        if let Ok(angle) = s.parse() {
            if let Some(self_) = Self::with_angle_only(angle) {
                return Ok(self_);
            }
        }

        Err(ParseCoordinateError::NoHemisphere)
    }
}

#[macro_export]
/// Allows to implement some `TryFrom` implementations for a type:
/// - TryFrom<T1>
/// - TryFrom<(T1, T2)>
/// - TryFrom<(T1, T2, T3)>
/// - TryFrom<[T; 2]>
/// - TryFrom<[T; 3]>
///
/// by providing only two implementations:
/// - TryFrom<T1, T2, T3, T4)>
/// - TryFrom<[T; 4]>
///
/// Missing parts are filled with 0-s.
///
/// # Examples
/// `try_from_tuples_and_arrays!((Point4D, CoordNotInRange) <- u16, u8, u8, u16; u16)`
/// `try_from_tuples_and_arrays!((GenericPoint<A> where A: Angle, NumErr) <- i16, u8, u8, u16; i16)`
macro_rules! try_from_tuples_and_arrays {
    (($target:ty $(where $T:tt: $Trait:ident)?, $err: ident) <- $t1:ty, $t2:ty, $t3:ty, $t4:ty; $t_max:ty) => {
        impl$(<$T:$Trait>)? TryFrom<$t1> for $target
        $(where
            Self: TryFrom<($t1, $t2, $t3, $t4), Error = <$T as $Trait>::$err>,
            //$T: $Trait + TryFrom<($t1, $t2, $t3, $t4), Error = <$T as $Trait>::$err>,
        )?
        {
            type Error = $($T::)?$err;

            fn try_from(value: $t1) -> Result<Self, Self::Error> {
                Self::try_from((value, 0, 0, 0))
            }
        }

        impl$(<$T:$Trait>)? TryFrom<($t1, $t2)> for $target
        $(where
            Self: TryFrom<($t1, $t2, $t3, $t4), Error = <$T as $Trait>::$err>,
        )?
        {
            type Error = $($T::)?$err;

            fn try_from(value: ($t1, $t2)) -> Result<Self, Self::Error> {
                let (v1, v2) = value;
                Self::try_from((v1, v2, 0, 0))
            }
        }

        impl$(<$T:$Trait>)? TryFrom<($t1, $t2, $t3)> for $target
        $(where
            Self: TryFrom<($t1, $t2, $t3, $t4), Error = <$T as $Trait>::$err>,
        )?
        {
            type Error = $($T::)?$err;

            fn try_from(value: ($t1, $t2, $t3)) -> Result<Self, Self::Error> {
                let (v1, v2, v3) = value;
                Self::try_from((v1, v2, v3, 0))
            }
        }

        impl$(<$T:$Trait>)? TryFrom<[$t_max; 2]> for $target
        $(where
            Self: TryFrom<[$t_max; 4], Error = <$T as $Trait>::$err>,
        )?
        {
            type Error = $($T::)?$err;

            fn try_from(value: [$t_max; 2]) -> Result<Self, Self::Error> {
                let [v1, v2] = value;
                Self::try_from([v1, v2, 0, 0])
            }
        }

        impl$(<$T:$Trait>)? TryFrom<[$t_max; 3]> for $target
        $(where
            Self: TryFrom<[$t_max; 4], Error = <$T as $Trait>::$err>,
        )?
        {
            type Error = $($T::)?$err;

            fn try_from(value: [$t_max; 3]) -> Result<Self, Self::Error> {
                let [v1, v2, v3] = value;
                Self::try_from([v1, v2, v3, 0])
            }
        }
    };
}
