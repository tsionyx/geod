use std::{
    cmp::Ordering,
    convert::{TryFrom, TryInto},
    error::Error,
    fmt,
    ops::{Add, Neg, Sub},
    str::FromStr,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{angle::Angle, bool_enum, try_from_tuples_and_arrays, utils::ToUnsigned};

use super::{AngleAndDirection, ParseCoordinateError, ParsedCoordinate};

bool_enum!(Pole: North and South; parse from 'N':'S' with ParsePoleError);

/// The angle measured between the equatorial plane and the point along the meridian.
/// [Read more](https://en.wikipedia.org/wiki/Latitude).
#[derive(Debug, Ord, PartialOrd, Eq, PartialEq, Copy, Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Latitude<A: Angle>(A);

impl<A: Angle> Latitude<A> {
    /// Construct a northern latitude with some numeric information.
    ///
    /// # Errors
    /// - cannot construct an angle from the given information (overflow of some kind)
    /// - the constructed angle is more than the [right](trait.AngleNames.html#tymethod.right) angle.
    ///   Valid latitude is in the range `0 <= lat <= 90 deg`.
    pub fn north<T>(angle: T) -> Result<Self, A::NumErr>
    where
        T: TryInto<A, Error = A::NumErr>,
    {
        angle
            .try_into()
            .and_then(|angle| Self::with_angle_and_direction(angle, North))
    }

    /// Construct a southern latitude with some numeric information.
    ///
    /// # Errors
    /// - cannot construct an angle from the given information (overflow of some kind)
    /// - the constructed angle is more than the [right](trait.AngleNames.html#tymethod.right) angle.
    ///   Valid latitude is in the range `0 <= lat <= 90 deg`.
    pub fn south<T>(angle: T) -> Result<Self, A::NumErr>
    where
        T: TryInto<A, Error = A::NumErr>,
    {
        angle
            .try_into()
            .and_then(|angle| Self::with_angle_and_direction(angle, South))
    }

    /// The central latitude of the sphere equidistant from the poles
    pub fn equator() -> Self {
        Self(A::right())
    }

    /// Angle between the latitude and the equator (absolute value of the latitude).
    pub fn angle_from_equator(self) -> A {
        let from_south_pole = self.0;
        let right = A::right();

        right.abs_diff(from_south_pole)
    }

    /// Which pole are closer to the given latitude
    pub fn hemisphere(self) -> Option<Pole> {
        match self.cmp(&Self::equator()) {
            Ordering::Less => Some(South),
            Ordering::Equal => None,
            Ordering::Greater => Some(North),
        }
    }

    /// Is the given latitude belongs to a pole
    pub fn is_pole(self) -> bool {
        self == North.into() || self == South.into()
    }
}

impl<A: Angle> Default for Latitude<A> {
    fn default() -> Self {
        Self::equator()
    }
}

impl<A: Angle> AngleAndDirection<A> for Latitude<A> {
    type Direction = Pole;

    fn with_angle_and_direction(angle: A, hemisphere: Self::Direction) -> Result<Self, A::NumErr> {
        let angle = angle.and_not_obtuse()?;

        let angle = match hemisphere {
            North => angle.checked_add(&A::right()),
            South => angle.complement(),
        }
        .expect("Latitude is valid");

        assert!(angle <= A::straight());
        Ok(Self(angle))
    }
}

impl<A: Angle> ParsedCoordinate<A> for Latitude<A>
where
    A: FromStr<Err = <A as Angle>::ParseErr>,
    A::ParseErr: From<A::NumErr>,
{
    fn with_angle_only(angle: A) -> Option<Self> {
        if angle.is_zero() {
            Some(Self::equator())
        } else {
            None
        }
    }
}

impl<A: Angle> From<Pole> for Latitude<A> {
    fn from(pole: Pole) -> Self {
        let angle = match pole {
            North => A::straight(),
            South => A::zero(),
        };
        Self(angle)
    }
}

impl<A: Angle> Neg for Latitude<A> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let angle = self.angle_from_equator();
        let opposite_pole = match self.hemisphere() {
            Some(pole) => -pole,
            // just a convention for equator, it means nothing when constructing a Latitude
            None => North,
        };
        Self::with_angle_and_direction(angle, opposite_pole)
            .expect("Cannot construct the opposite latitude")
    }
}

impl<A: Angle> TryFrom<f64> for Latitude<A> {
    type Error = A::NumErr;

    fn try_from(value: f64) -> Result<Self, Self::Error> {
        let (value, is_north) = value.unsigned_abs();
        let angle = value.try_into()?;
        Self::with_angle_and_direction(angle, is_north.into())
    }
}

impl<A: Angle> TryFrom<(i16, u8, u8, u16)> for Latitude<A>
where
    A: TryFrom<(u16, u8, u8, u16), Error = <A as Angle>::NumErr>,
{
    type Error = A::NumErr;

    fn try_from(value: (i16, u8, u8, u16)) -> Result<Self, Self::Error> {
        let (deg, min, sec, milli) = value;

        let (deg, sign) = deg.unsigned_abs();
        let angle = (deg, min, sec, milli).try_into()?;

        Self::with_angle_and_direction(angle, sign.into())
    }
}

mod partial_try_from {
    use std::convert::{TryFrom, TryInto};

    use crate::angle::{dd::DecimalDegree, dms_dd::AccurateDegree, AngleNotInRange};

    use super::{Angle, Latitude};

    impl TryFrom<[i16; 4]> for Latitude<AccurateDegree> {
        type Error = <AccurateDegree as Angle>::NumErr;

        fn try_from(value: [i16; 4]) -> Result<Self, Self::Error> {
            let [deg, min, sec, centi] = value;
            let min = min.try_into().map_err(|_| AngleNotInRange::ArcMinutes)?;
            let sec = sec.try_into().map_err(|_| AngleNotInRange::ArcSeconds)?;
            let centi: u8 = centi
                .try_into()
                .map_err(|_| AngleNotInRange::ArcCentiSeconds)?;
            Self::try_from((deg, min, sec, u16::from(centi)))
        }
    }

    impl TryFrom<[i16; 4]> for Latitude<DecimalDegree> {
        type Error = <DecimalDegree as Angle>::NumErr;

        fn try_from(value: [i16; 4]) -> Result<Self, Self::Error> {
            let [deg, min, sec, mas] = value;
            let min: u8 = min.try_into().map_err(|_| AngleNotInRange::ArcMinutes)?;
            let sec: u8 = sec.try_into().map_err(|_| AngleNotInRange::ArcSeconds)?;
            let mas: u16 = mas
                .try_into()
                .map_err(|_| AngleNotInRange::ArcMilliSeconds)?;
            Self::try_from((deg, min, sec, mas))
        }
    }
}

try_from_tuples_and_arrays!((Latitude<A> where A: Angle, NumErr) <- i16, u8, u8, u16; i16);

impl<A: Angle> Add<A> for Latitude<A> {
    type Output = Result<Self, A::NumErr>;

    /// Represent the north movement
    fn add(self, rhs: A) -> Self::Output {
        let angle = self.0.checked_add(&rhs).ok_or_else(A::turn_err)?;

        // farther north than the north pole
        let angle = angle.and_not_reflex()?;
        Ok(Self(angle))
    }
}

impl<A: Angle> Sub<A> for Latitude<A> {
    type Output = Result<Self, A::NumErr>;

    /// Represent the south movement
    fn sub(self, rhs: A) -> Self::Output {
        // farther south than the south pole
        let angle = self.0.checked_sub(&rhs).ok_or_else(A::turn_err)?;

        assert!(!angle.is_reflex());
        Ok(Self(angle))
    }
}

impl<A: Angle> FromStr for Latitude<A>
where
    A::ParseErr: From<A::NumErr>,
{
    type Err = ParseCoordinateError<A::ParseErr>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl<A: Angle> fmt::Display for Latitude<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let angle = self.angle_from_equator();
        if f.alternate() {
            write!(f, "{:#}", angle)?;

            if let Some(hemisphere) = self.hemisphere() {
                write!(f, "{:#}", hemisphere)
            } else {
                Ok(())
            }
        } else {
            if let Some(South) = self.hemisphere() {
                write!(f, "-")?;
            }
            write!(f, "{}", angle)
        }
    }
}

#[cfg(test)]
mod tests_accur {
    use std::mem::size_of;

    use crate::angle::{dms_dd::AccurateDegree, AngleNames};

    use super::*;

    #[test]
    fn size_lat() {
        assert_eq!(size_of::<Latitude<AccurateDegree>>(), 4);
    }

    /// From south to north
    /// <https://en.wikipedia.org/wiki/Circle_of_latitude>
    fn common_earth_parallels() -> Vec<Latitude<AccurateDegree>> {
        let south_pole = South.into();
        let antarctic_circle = Latitude::with_angle_and_direction(
            AccurateDegree::with_dms(66, 33, 48, 0).unwrap(),
            South,
        )
        .unwrap();
        let capricorn_tropic = [-23, 26, 12].try_into().unwrap();
        let cancer_tropic = Latitude::north((23, 26, 12, 0)).unwrap();
        let equator = Latitude::equator();
        let arctic_circle = (66, 33, 48).try_into().unwrap();
        let north_pole = North.into();

        vec![
            south_pole,
            antarctic_circle,
            capricorn_tropic,
            equator,
            cancer_tropic,
            arctic_circle,
            north_pole,
        ]
    }

    #[test]
    fn ordering() {
        let from_south_no_north = common_earth_parallels();

        // assert!(from_south_no_north.is_sorted());
        let mut sorted = from_south_no_north.clone();
        sorted.sort();
        assert_eq!(from_south_no_north, sorted);
    }

    #[test]
    fn south_less_than_north() {
        let parallels = common_earth_parallels();

        for (first, second) in common_earth_parallels().into_iter().skip(1).zip(parallels) {
            dbg!(first);
            dbg!(second);
            assert!(first > second);
        }
    }

    #[test]
    fn parallels_symmetry() {
        let parallels = common_earth_parallels();
        // equator is in both
        let half = parallels.len() / 2;
        let (southern, northern) = if parallels.len() % 2 == 1 {
            // overlay in the middle
            (&parallels[..=half], &parallels[half..])
        } else {
            parallels.split_at(parallels.len() / 2)
        };
        assert_eq!(southern.len(), northern.len());

        for (&s, &n) in southern.iter().rev().zip(northern) {
            dbg!(s);
            dbg!(n);
            if s != Latitude::equator() {
                assert_eq!(s.hemisphere(), Some(South));
                assert_eq!(n.hemisphere(), Some(North));
            }
            assert_eq!(s.angle_from_equator(), n.angle_from_equator());
            assert_eq!(-s, n);
        }
    }

    #[test]
    fn equal_equators() {
        let equator = Latitude::equator();
        let equator1 = Latitude::with_angle_and_direction(AccurateDegree::zero(), South).unwrap();
        let equator2 = Latitude::with_angle_and_direction(AccurateDegree::zero(), North).unwrap();
        let equator3 = 0.try_into().unwrap();

        assert_eq!(equator, equator1);
        assert_eq!(equator1, equator2);
        assert_eq!(equator2, equator3);
        assert!(equator3.angle_from_equator().is_zero());
    }

    #[test]
    fn good_latitude_max() {
        let l: Latitude<AccurateDegree> = 90.try_into().unwrap();
        assert_eq!(Latitude::from(North), l)
    }

    #[test]
    #[should_panic(expected = "ObtuseAngle")]
    fn bad_latitude_max() {
        let _l = Latitude::<AccurateDegree>::try_from(91).unwrap();
    }

    #[test]
    #[should_panic(expected = "ObtuseAngle")]
    fn bad_latitude_overflow() {
        let angle: AccurateDegree = 100.try_into().unwrap();
        let _l = Latitude::with_angle_and_direction(angle, North).unwrap();
    }

    #[test]
    fn good_latitude_min() {
        let l = (-90).try_into().unwrap();
        assert_eq!(Latitude::from(South), l);

        let l2: Latitude<AccurateDegree> = 90.try_into().unwrap();
        assert_eq!(l, -l2);
    }

    #[test]
    #[should_panic(expected = "ObtuseAngle")]
    fn bad_latitude_min() {
        let _l = Latitude::<AccurateDegree>::try_from(-91).unwrap();
    }

    #[test]
    #[should_panic(expected = "ObtuseAngle")]
    fn bad_latitude_underflow() {
        let angle = AccurateDegree::with_dms(150, 0, 0, 0).unwrap();
        let _l = Latitude::with_angle_and_direction(angle, South).unwrap();
    }

    #[test]
    fn from_f64_north() {
        let l = Latitude::<AccurateDegree>::try_from(41.622_512).unwrap();
        assert_eq!(l.hemisphere(), Some(North));
        assert!(l
            .angle_from_equator()
            .almost_equal(AccurateDegree::with_dms(41, 37, 21, 4).unwrap()));

        let l2 = Latitude::north(41.622_512).unwrap();
        assert_eq!(l, l2);
    }

    #[test]
    fn from_f64_south() {
        let l: Latitude<AccurateDegree> = (-84.120_456).try_into().unwrap();
        assert_eq!(l.hemisphere(), Some(South));
        assert!(l
            .angle_from_equator()
            .almost_equal(AccurateDegree::with_dms(84, 7, 13, 64).unwrap()));

        let l2 = Latitude::south(84.120_456).unwrap();
        assert_eq!(l, l2);
    }

    #[test]
    #[should_panic(expected = "ObtuseAngle")]
    fn from_f64_overflow() {
        let _l = Latitude::<AccurateDegree>::try_from(91.622_512).unwrap();
    }
}

#[cfg(test)]
mod parse_tests_accur {
    use crate::angle::{dms_dd::AccurateDegree, AngleNames};

    use super::*;

    #[test]
    fn simple_degree() {
        let l: Latitude<AccurateDegree> = "15° N".parse().unwrap();

        assert_eq!(l.hemisphere(), Some(North));
        assert_eq!(
            l.angle_from_equator(),
            AccurateDegree::try_from(15).unwrap()
        );
    }

    #[test]
    fn suffix_decimal() {
        let l: Latitude<AccurateDegree> = "34.1551784° N".parse().unwrap();
        let l_ascii: Latitude<AccurateDegree> = "34.1551784N".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(North));
        assert_eq!(
            l.angle_from_equator(),
            AccurateDegree::try_from(34.155_178_4).unwrap()
        );
    }

    #[test]
    fn suffix_with_space() {
        let l: Latitude<AccurateDegree> = "34°16′22″ N".parse().unwrap();
        let l_ascii: Latitude<AccurateDegree> = "34* 16' 22\" N".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(North));
        assert_eq!(
            l.angle_from_equator(),
            AccurateDegree::with_dms(34, 16, 22, 0).unwrap()
        );
    }

    #[test]
    fn suffix_no_space() {
        let l: Latitude<AccurateDegree> = "43° 20′ 7.15″S".parse().unwrap();
        let l_ascii: Latitude<AccurateDegree> = "43 20'7.15\"S".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(South));
        assert_eq!(
            l.angle_from_equator(),
            AccurateDegree::with_dms(43, 20, 7, 15).unwrap()
        );
    }

    #[test]
    fn prefix_decimal() {
        let l: Latitude<AccurateDegree> = "S 34.0045°".parse().unwrap();
        let l_ascii: Latitude<AccurateDegree> = "S34.0045".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(South));
        assert_eq!(
            l.angle_from_equator(),
            AccurateDegree::try_from(34.0045).unwrap()
        );
    }

    #[test]
    fn prefix_with_space() {
        let l: Latitude<AccurateDegree> = "N 34°16′0″".parse().unwrap();
        let l_ascii: Latitude<AccurateDegree> = "N 34* 16'".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(North));
        assert_eq!(
            l.angle_from_equator(),
            AccurateDegree::with_dms(34, 16, 0, 0).unwrap()
        );
    }

    #[test]
    fn prefix_no_space() {
        let l: Latitude<AccurateDegree> = "S89° 0′ 2.44″".parse().unwrap();
        let l_ascii: Latitude<AccurateDegree> = "S89 0'2.44\"".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(South));
        assert_eq!(
            l.angle_from_equator(),
            AccurateDegree::with_dms(89, 0, 2, 44).unwrap()
        );
    }

    #[test]
    fn prefix_sign_decimal() {
        let l: Latitude<AccurateDegree> = "-34.0045°".parse().unwrap();
        let l_ascii: Latitude<AccurateDegree> = "-34.0045".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(South));
        assert_eq!(
            l.angle_from_equator(),
            AccurateDegree::try_from(34.0045).unwrap()
        );
    }

    #[test]
    fn prefix_sign_with_space() {
        let l: Latitude<AccurateDegree> = "+34°16′0″".parse().unwrap();
        let l_ascii: Latitude<AccurateDegree> = "+34 16'".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(North));
        assert_eq!(
            l.angle_from_equator(),
            AccurateDegree::with_dms(34, 16, 0, 0).unwrap()
        );
    }

    #[test]
    fn prefix_sign_no_space() {
        let l: Latitude<AccurateDegree> = "-89° 0′ 2.44″".parse().unwrap();
        let l_ascii: Latitude<AccurateDegree> = "-89*0'2.44\"".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(South));
        assert_eq!(
            l.angle_from_equator(),
            AccurateDegree::with_dms(89, 0, 2, 44).unwrap()
        );
    }

    #[test]
    fn equator_does_not_require_pole() {
        let eq: Latitude<AccurateDegree> = "0°".parse().unwrap();
        let eq2: Latitude<AccurateDegree> = "0".parse().unwrap();
        let eq3: Latitude<AccurateDegree> = "0 0'".parse().unwrap();
        assert_eq!(eq, eq2);
        assert_eq!(eq2, eq3);
        assert!(eq.angle_from_equator().is_zero());
    }
}

#[cfg(test)]
mod bad_parse_tests_accur {
    use crate::angle::dms_dd::AccurateDegree;

    use super::*;

    #[test]
    #[should_panic(expected = "NoHemisphere")]
    fn no_prefix_no_suffix() {
        let _l: Latitude<AccurateDegree> = "15°".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "EmptyString")]
    fn empty() {
        let _l: Latitude<AccurateDegree> = "".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(DmsNotation)")]
    fn bad_sign() {
        let _l: Latitude<AccurateDegree> = "--89° 16′".parse().unwrap();
    }

    #[test]
    // if cannot parse the float, fallback to DMS, therefore
    // not a `Float`, but `DmsNotation` variant
    #[should_panic(expected = "Angle(DmsNotation)")]
    fn bad_float() {
        let _l: Latitude<AccurateDegree> = "-15.46.11".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(AngleNotInRange(ObtuseAngle))")]
    fn too_big_angle_north() {
        let _l: Latitude<AccurateDegree> = "+100°16′".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(AngleNotInRange(ObtuseAngle))")]
    fn too_big_angle_south() {
        let _l: Latitude<AccurateDegree> = "-92".parse().unwrap();
    }

    #[test]
    fn round_more_than_7_digits() {
        let l: Latitude<AccurateDegree> = "-18.99999995°".parse().unwrap();
        // 90 - 18.9999999 = 70.0000001
        assert_eq!(l.0, AccurateDegree::try_from(71.000_000_1).unwrap());
    }

    #[test]
    #[should_panic(expected = "NoHemisphere")]
    fn bad_hemisphere() {
        let _l: Latitude<AccurateDegree> = "18.15Z°".parse().unwrap();
    }
}

#[cfg(test)]
mod tests_dec {
    use std::mem::size_of;

    use crate::angle::{dd::DecimalDegree, AngleNames};

    use super::*;

    #[test]
    fn size_lat() {
        assert_eq!(size_of::<Latitude<DecimalDegree>>(), 4);
    }

    /// From south to north
    /// <https://en.wikipedia.org/wiki/Circle_of_latitude>
    fn common_earth_parallels() -> Vec<Latitude<DecimalDegree>> {
        let south_pole = South.into();
        let antarctic_circle = Latitude::with_angle_and_direction(
            DecimalDegree::with_dms(66, 33, 48, 0).unwrap(),
            South,
        )
        .unwrap();
        let capricorn_tropic = [-23, 26, 12].try_into().unwrap();
        let cancer_tropic = Latitude::north((23, 26, 12, 0)).unwrap();
        let equator = Latitude::equator();
        let arctic_circle = (66, 33, 48).try_into().unwrap();
        let north_pole = North.into();

        vec![
            south_pole,
            antarctic_circle,
            capricorn_tropic,
            equator,
            cancer_tropic,
            arctic_circle,
            north_pole,
        ]
    }

    #[test]
    fn ordering() {
        let from_south_no_north = common_earth_parallels();

        // assert!(from_south_no_north.is_sorted());
        let mut sorted = from_south_no_north.clone();
        sorted.sort();
        assert_eq!(from_south_no_north, sorted);
    }

    #[test]
    fn south_less_than_north() {
        let parallels = common_earth_parallels();

        for (first, second) in common_earth_parallels().into_iter().skip(1).zip(parallels) {
            dbg!(first);
            dbg!(second);
            assert!(first > second);
        }
    }

    #[test]
    fn parallels_symmetry() {
        let parallels = common_earth_parallels();
        // equator is in both
        let half = parallels.len() / 2;
        let (southern, northern) = if parallels.len() % 2 == 1 {
            // overlay in the middle
            (&parallels[..=half], &parallels[half..])
        } else {
            parallels.split_at(parallels.len() / 2)
        };
        assert_eq!(southern.len(), northern.len());

        for (&s, &n) in southern.iter().rev().zip(northern) {
            dbg!(s);
            dbg!(n);
            if s != Latitude::equator() {
                assert_eq!(s.hemisphere(), Some(South));
                assert_eq!(n.hemisphere(), Some(North));
            }
            assert_eq!(s.angle_from_equator(), n.angle_from_equator());
            assert_eq!(-s, n);
        }
    }

    #[test]
    fn equal_equators() {
        let equator = Latitude::equator();
        let equator1 = Latitude::with_angle_and_direction(DecimalDegree::zero(), South).unwrap();
        let equator2 = Latitude::with_angle_and_direction(DecimalDegree::zero(), North).unwrap();
        let equator3 = 0.try_into().unwrap();

        assert_eq!(equator, equator1);
        assert_eq!(equator1, equator2);
        assert_eq!(equator2, equator3);
        assert!(equator3.angle_from_equator().is_zero());
    }

    #[test]
    fn good_latitude_max() {
        let l: Latitude<DecimalDegree> = 90.try_into().unwrap();
        assert_eq!(Latitude::from(North), l)
    }

    #[test]
    #[should_panic(expected = "ObtuseAngle")]
    fn bad_latitude_max() {
        let _l = Latitude::<DecimalDegree>::try_from(91).unwrap();
    }

    #[test]
    #[should_panic(expected = "ObtuseAngle")]
    fn bad_latitude_overflow() {
        let angle: DecimalDegree = 100.try_into().unwrap();
        let _l = Latitude::with_angle_and_direction(angle, North).unwrap();
    }

    #[test]
    fn good_latitude_min() {
        let l = (-90).try_into().unwrap();
        assert_eq!(Latitude::from(South), l);

        let l2: Latitude<DecimalDegree> = 90.try_into().unwrap();
        assert_eq!(l, -l2);
    }

    #[test]
    #[should_panic(expected = "ObtuseAngle")]
    fn bad_latitude_min() {
        let _l = Latitude::<DecimalDegree>::try_from(-91).unwrap();
    }

    #[test]
    #[should_panic(expected = "ObtuseAngle")]
    fn bad_latitude_underflow() {
        let angle = DecimalDegree::with_dms(150, 0, 0, 0).unwrap();
        let _l = Latitude::with_angle_and_direction(angle, South).unwrap();
    }

    #[test]
    fn from_f64_north() {
        let l = Latitude::<DecimalDegree>::try_from(41.622_512).unwrap();
        assert_eq!(l.hemisphere(), Some(North));
        assert!(l
            .angle_from_equator()
            .almost_equal(DecimalDegree::with_dms(41, 37, 21, 43).unwrap()));

        let l2 = Latitude::north(41.622_512).unwrap();
        assert_eq!(l, l2);
    }

    #[test]
    fn from_f64_south() {
        let l: Latitude<DecimalDegree> = (-84.120_456).try_into().unwrap();
        assert_eq!(l.hemisphere(), Some(South));
        assert!(l
            .angle_from_equator()
            .almost_equal(DecimalDegree::with_dms(84, 7, 13, 642).unwrap()));

        let l2 = Latitude::south(84.120_456).unwrap();
        assert_eq!(l, l2);
    }

    #[test]
    #[should_panic(expected = "ObtuseAngle")]
    fn from_f64_overflow() {
        let _l = Latitude::<DecimalDegree>::try_from(91.622_512).unwrap();
    }
}

#[cfg(test)]
mod parse_tests_dec {
    use crate::angle::{dd::DecimalDegree, AngleNames};

    use super::*;

    #[test]
    fn simple_degree() {
        let l: Latitude<DecimalDegree> = "15° N".parse().unwrap();

        assert_eq!(l.hemisphere(), Some(North));
        assert_eq!(l.angle_from_equator(), DecimalDegree::try_from(15).unwrap());
    }

    #[test]
    fn suffix_decimal() {
        let l: Latitude<DecimalDegree> = "34.1551784° N".parse().unwrap();
        let l_ascii: Latitude<DecimalDegree> = "34.1551784N".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(North));
        assert_eq!(
            l.angle_from_equator(),
            DecimalDegree::try_from(34.155_178_4).unwrap()
        );
    }

    #[test]
    fn suffix_with_space() {
        let l: Latitude<DecimalDegree> = "34°16′22″ N".parse().unwrap();
        let l_ascii: Latitude<DecimalDegree> = "34* 16' 22\" N".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(North));
        assert_eq!(
            l.angle_from_equator(),
            DecimalDegree::with_dms(34, 16, 22, 0).unwrap()
        );
    }

    #[test]
    fn suffix_no_space() {
        let l: Latitude<DecimalDegree> = "43° 20′ 7.15″S".parse().unwrap();
        let l_ascii: Latitude<DecimalDegree> = "43 20'7.15\"S".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(South));
        assert_eq!(
            l.angle_from_equator(),
            DecimalDegree::with_dms(43, 20, 7, 150).unwrap()
        );
    }

    #[test]
    fn prefix_decimal() {
        let l: Latitude<DecimalDegree> = "S 34.0045°".parse().unwrap();
        let l_ascii: Latitude<DecimalDegree> = "S34.0045".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(South));
        assert_eq!(
            l.angle_from_equator(),
            DecimalDegree::try_from(34.0045).unwrap()
        );
    }

    #[test]
    fn prefix_with_space() {
        let l: Latitude<DecimalDegree> = "N 34°16′0″".parse().unwrap();
        let l_ascii: Latitude<DecimalDegree> = "N 34* 16'".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(North));
        assert_eq!(
            l.angle_from_equator(),
            DecimalDegree::with_dms(34, 16, 0, 0).unwrap()
        );
    }

    #[test]
    fn prefix_no_space() {
        let l: Latitude<DecimalDegree> = "S89° 0′ 2.44″".parse().unwrap();
        let l_ascii: Latitude<DecimalDegree> = "S89 0'2.44\"".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(South));
        assert_eq!(
            l.angle_from_equator(),
            DecimalDegree::with_dms(89, 0, 2, 440).unwrap()
        );
    }

    #[test]
    fn prefix_sign_decimal() {
        let l: Latitude<DecimalDegree> = "-34.0045°".parse().unwrap();
        let l_ascii: Latitude<DecimalDegree> = "-34.0045".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(South));
        assert_eq!(
            l.angle_from_equator(),
            DecimalDegree::try_from(34.0045).unwrap()
        );
    }

    #[test]
    fn prefix_sign_with_space() {
        let l: Latitude<DecimalDegree> = "+34°16′0″".parse().unwrap();
        let l_ascii: Latitude<DecimalDegree> = "+34 16'".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(North));
        assert_eq!(
            l.angle_from_equator(),
            DecimalDegree::with_dms(34, 16, 0, 0).unwrap()
        );
    }

    #[test]
    fn prefix_sign_no_space() {
        let l: Latitude<DecimalDegree> = "-89° 0′ 2.44″".parse().unwrap();
        let l_ascii: Latitude<DecimalDegree> = "-89*0'2.44\"".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.hemisphere(), Some(South));
        assert_eq!(
            l.angle_from_equator(),
            DecimalDegree::with_dms(89, 0, 2, 440).unwrap()
        );
    }

    #[test]
    fn equator_does_not_require_pole() {
        let eq: Latitude<DecimalDegree> = "0°".parse().unwrap();
        let eq2: Latitude<DecimalDegree> = "0".parse().unwrap();
        let eq3: Latitude<DecimalDegree> = "0 0'".parse().unwrap();
        assert_eq!(eq, eq2);
        assert_eq!(eq2, eq3);
        assert!(eq.angle_from_equator().is_zero());
    }
}

#[cfg(test)]
mod bad_parse_tests_dec {
    use crate::angle::dd::DecimalDegree;

    use super::*;

    #[test]
    #[should_panic(expected = "NoHemisphere")]
    fn no_prefix_no_suffix() {
        let _l: Latitude<DecimalDegree> = "15°".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "EmptyString")]
    fn empty() {
        let _l: Latitude<DecimalDegree> = "".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(DmsNotation)")]
    fn bad_sign() {
        let _l: Latitude<DecimalDegree> = "--89° 16′".parse().unwrap();
    }

    #[test]
    // if cannot parse the float, fallback to DMS, therefore
    // not a `Float`, but `DmsNotation` variant
    #[should_panic(expected = "Angle(DmsNotation)")]
    fn bad_float() {
        let _l: Latitude<DecimalDegree> = "-15.46.11".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(AngleNotInRange(ObtuseAngle))")]
    fn too_big_angle_north() {
        let _l: Latitude<DecimalDegree> = "+100°16′".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(AngleNotInRange(ObtuseAngle))")]
    fn too_big_angle_south() {
        let _l: Latitude<DecimalDegree> = "-92".parse().unwrap();
    }

    #[test]
    fn round_more_than_7_digits() {
        let l: Latitude<DecimalDegree> = "-18.99999995°".parse().unwrap();
        // 90 - 18.9999999 = 70.0000001
        assert_eq!(l.0, DecimalDegree::try_from(71.000_000_1).unwrap());
    }

    #[test]
    #[should_panic(expected = "NoHemisphere")]
    fn bad_hemisphere() {
        let _l: Latitude<DecimalDegree> = "18.15Z°".parse().unwrap();
    }
}

#[cfg(test)]
mod arith_tests {
    use super::*;
    use crate::angle::{dd::DecimalDegree, dms_dd::AccurateDegree};

    #[test]
    fn simply_north() {
        let l: Latitude<AccurateDegree> = (35, 12).try_into().unwrap();
        assert_eq!(l.hemisphere(), Some(North));

        let move_north = (12, 16, 5).try_into().unwrap();
        let l2 = (l + move_north).unwrap();
        assert_eq!(l2.hemisphere(), Some(North));
        assert_eq!(
            l2.angle_from_equator(),
            AccurateDegree::with_dms(47, 28, 5, 0).unwrap()
        )
    }

    #[test]
    fn cross_the_equator_while_going_north() {
        let l: Latitude<DecimalDegree> = (-35, 12).try_into().unwrap();
        assert_eq!(l.hemisphere(), Some(South));

        let move_north = (47, 16, 5).try_into().unwrap();
        let l2 = (l + move_north).unwrap();
        assert_eq!(l2.hemisphere(), Some(North));
        assert_eq!(
            l2.angle_from_equator(),
            DecimalDegree::with_dms(12, 4, 5, 0).unwrap()
        )
    }

    #[test]
    #[should_panic(expected = "ReflexAngle")]
    fn go_beyond_north_pole() {
        let l: Latitude<DecimalDegree> = (-35, 12).try_into().unwrap();
        assert_eq!(l.hemisphere(), Some(South));

        let move_north = (140, 56, 11).try_into().unwrap();
        let _l2 = (l + move_north).unwrap();
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn go_beyond_north_pole_bad_angle() {
        let l: Latitude<DecimalDegree> = (65, 33).try_into().unwrap();
        assert_eq!(l.hemisphere(), Some(North));

        let move_north = (300, 56, 11).try_into().unwrap();
        let _l2 = (l + move_north).unwrap();
    }

    #[test]
    fn simply_south() {
        let l: Latitude<DecimalDegree> = (-10, 8, 49, 25).try_into().unwrap();
        assert_eq!(l.hemisphere(), Some(South));

        let move_south = (32, 33, 40).try_into().unwrap();
        let l2 = (l - move_south).unwrap();
        assert_eq!(l2.hemisphere(), Some(South));
        assert_eq!(
            l2.angle_from_equator(),
            DecimalDegree::with_dms(42, 42, 29, 25).unwrap()
        )
    }

    #[test]
    fn cross_the_equator_while_going_south() {
        let l: Latitude<AccurateDegree> = (15, 31, 59).try_into().unwrap();
        assert_eq!(l.hemisphere(), Some(North));

        let move_south = (81, 51, 8).try_into().unwrap();
        let l2 = (l - move_south).unwrap();
        assert_eq!(l2.hemisphere(), Some(South));
        assert_eq!(
            l2.angle_from_equator(),
            AccurateDegree::with_dms(66, 19, 9, 0).unwrap()
        )
    }

    #[test]
    #[should_panic(expected = "Degrees")]
    fn go_beyond_south_pole() {
        let l: Latitude<DecimalDegree> = (-35, 12).try_into().unwrap();
        assert_eq!(l.hemisphere(), Some(South));

        let move_south = (60, 56, 11).try_into().unwrap();
        let _l2 = (l - move_south).unwrap();
    }
}
