use std::{
    cmp::Ordering,
    convert::{TryFrom, TryInto},
    error::Error,
    fmt,
    ops::Neg,
    str::FromStr,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::{angle::Angle, bool_enum, try_from_tuples_and_arrays, utils::ToUnsigned};

use super::{AngleAndDirection, ParseCoordinateError, ParsedCoordinate};

bool_enum!(RotationalDirection: East and West; parse from 'E':'W' with ParseDirectionError);

/// The angle measured on the equatorial plane between the meridian of the point
/// and the prime meridian (Greenwich, UK).
/// [Read more](https://en.wikipedia.org/wiki/Longitude).
#[derive(Debug, Copy, Clone, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct Longitude<A: Angle>(A);

impl<A: Angle> Longitude<A> {
    fn new(mut angle: A) -> Self {
        if angle.is_complete() {
            angle = A::zero();
        }
        Self(angle)
    }

    /// Construct an eastern longitude with some numeric information.
    ///
    /// # Errors
    /// - cannot construct an angle from the given information (overflow of some kind)
    /// - the constructed angle is more than the [straight](trait.AngleNames.html#tymethod.straight) angle.
    ///   Valid longitude is in the range `0 <= lon <= 180 deg`.
    pub fn east<T>(to_angle: T) -> Result<Self, A::NumErr>
    where
        T: TryInto<A, Error = A::NumErr>,
    {
        to_angle
            .try_into()
            .and_then(|angle| Self::with_angle_and_direction(angle, East))
    }

    /// Construct a western longitude with some numeric information.
    ///
    /// # Errors
    /// - cannot construct an angle from the given information (overflow of some kind)
    /// - the constructed angle is more than the [straight](trait.AngleNames.html#tymethod.straight) angle.
    ///   Valid longitude is in the range `0 <= lon <= 180 deg`.
    pub fn west<T>(to_angle: T) -> Result<Self, A::NumErr>
    where
        T: TryInto<A, Error = A::NumErr>,
    {
        to_angle
            .try_into()
            .and_then(|angle| Self::with_angle_and_direction(angle, West))
    }

    /// The chosen by convention [0-meridian](https://en.wikipedia.org/wiki/Prime_meridian)
    pub fn prime() -> Self {
        Self(A::zero())
    }

    /// The longitude opposite to the prime
    pub fn anti_meridian() -> Self {
        Self(A::straight())
    }

    /// Angle between the longitude and the prime meridian (absolute value of the longitude).
    pub fn angle(self) -> A {
        let angle = self.0;
        if angle.is_reflex() {
            angle.explement()
        } else {
            angle
        }
    }

    /// In which direction (from the prime) should we move to reach the longitude faster
    pub fn direction(self) -> Option<RotationalDirection> {
        if self == Self::prime() || self == Self::anti_meridian() {
            return None;
        }

        if self.0 < Self::anti_meridian().0 {
            Some(East)
        } else {
            Some(West)
        }
    }

    /// Diametrically opposite meridian
    /// which together with the current one defines
    /// the hemisphere (great circle)
    pub fn opposite(self) -> Self {
        let angle = self.0;
        let opp_angle = if angle >= A::straight() {
            angle.checked_sub(&A::straight())
        } else {
            angle.checked_add(&A::straight())
        }
        .expect("Opposite is valid");

        Self::new(opp_angle)
    }
}

impl<A: Angle> PartialEq for Longitude<A> {
    fn eq(&self, other: &Self) -> bool {
        // 0 == 360
        self.0.turn_eq(other.0)
    }
}

impl<A: Angle> PartialOrd for Longitude<A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == other {
            return Some(Ordering::Equal);
        }

        let (a, b) = (self.angle(), other.angle());

        match (self.direction(), other.direction()) {
            (Some(East), Some(West)) | (Some(West), Some(East)) => None,
            (Some(East), Some(East)) | (Some(West), Some(West)) => a.partial_cmp(&b),

            (None, _) => {
                if a.is_zero() {
                    Some(Ordering::Less)
                } else {
                    assert!(a.is_straight());
                    Some(Ordering::Greater)
                }
            }
            (_, None) => {
                if b.is_zero() {
                    Some(Ordering::Greater)
                } else {
                    assert!(b.is_straight());
                    Some(Ordering::Less)
                }
            }
        }
    }
}

impl<A: Angle> Default for Longitude<A> {
    fn default() -> Self {
        Self::prime()
    }
}

impl<A: Angle> AngleAndDirection<A> for Longitude<A> {
    type Direction = RotationalDirection;

    fn with_angle_and_direction(angle: A, direction: Self::Direction) -> Result<Self, A::NumErr> {
        let angle = angle.and_not_reflex()?;

        let angle = match direction {
            East => angle,
            West => angle.explement(),
        };
        Ok(Self::new(angle))
    }
}

impl<A: Angle> ParsedCoordinate<A> for Longitude<A>
where
    A: Angle + FromStr<Err = <A as Angle>::ParseErr>,
    A::ParseErr: From<A::NumErr>,
{
    fn with_angle_only(angle: A) -> Option<Self> {
        if angle.is_zero() {
            Some(Self::prime())
        } else if angle.is_straight() {
            Some(Self::anti_meridian())
        } else {
            None
        }
    }
}

impl<A: Angle> Neg for Longitude<A> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(self.0.explement())
    }
}

impl<A: Angle> TryFrom<f64> for Longitude<A> {
    type Error = A::NumErr;

    fn try_from(value: f64) -> Result<Self, Self::Error> {
        let (value, is_east) = value.unsigned_abs();
        let angle = value.try_into()?;
        Self::with_angle_and_direction(angle, is_east.into())
    }
}

impl<A: Angle> TryFrom<(i16, u8, u8, u16)> for Longitude<A>
where
    A: TryFrom<(u16, u8, u8, u16), Error = <A as Angle>::NumErr>,
{
    type Error = A::NumErr;

    fn try_from(value: (i16, u8, u8, u16)) -> Result<Self, Self::Error> {
        let (deg, min, sec, milli) = value;

        let (deg, is_east) = deg.unsigned_abs();
        let angle = (deg, min, sec, milli).try_into()?;

        Self::with_angle_and_direction(angle, is_east.into())
    }
}

mod partial_try_from {
    use std::convert::{TryFrom, TryInto};

    use crate::angle::{dd::DecimalDegree, dms_dd::AccurateDegree, AngleNotInRange};

    use super::{Angle, Longitude};

    //impl<A: Angle> TryFrom<[i16; 4]> for Longitude<A>
    //where A: TryFrom<(u16, u8, u8, u16), Error = <A as Angle>::NumErr>,
    impl TryFrom<[i16; 4]> for Longitude<AccurateDegree> {
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

    impl TryFrom<[i16; 4]> for Longitude<DecimalDegree> {
        type Error = <DecimalDegree as Angle>::NumErr;

        fn try_from(value: [i16; 4]) -> Result<Self, Self::Error> {
            let [deg, min, sec, mas] = value;
            let min = min.try_into().map_err(|_| AngleNotInRange::ArcMinutes)?;
            let sec = sec.try_into().map_err(|_| AngleNotInRange::ArcSeconds)?;
            let mas = mas
                .try_into()
                .map_err(|_| AngleNotInRange::ArcMilliSeconds)?;
            Self::try_from((deg, min, sec, mas))
        }
    }
}

try_from_tuples_and_arrays!((Longitude<A> where A: Angle, NumErr) <- i16, u8, u8, u16; i16);

impl<A: Angle> FromStr for Longitude<A>
where
    A::ParseErr: From<A::NumErr>,
{
    type Err = ParseCoordinateError<A::ParseErr>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

impl<A: Angle> fmt::Display for Longitude<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let angle = self.angle();

        if f.alternate() {
            write!(f, "{:#}", angle)?;

            if let Some(direction) = self.direction() {
                write!(f, "{:#}", direction)
            } else {
                Ok(())
            }
        } else {
            if let Some(West) = self.direction() {
                write!(f, "-")?
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
    fn size_long() {
        assert_eq!(size_of::<Longitude<AccurateDegree>>(), 4);
    }

    fn east_meridians() -> Vec<Longitude<AccurateDegree>> {
        let greenwich = Longitude::prime();
        let deg_20 = Longitude::east(20).unwrap();
        let deg_45 = (45, 20, 15, 18).try_into().unwrap();
        let deg_60 = Longitude::east(60.145).unwrap();
        let deg_75 = -(Longitude::west((75, 43, 21, 18)).unwrap());
        let deg_90 = [90, 20].try_into().unwrap();
        let deg_130 = 130.try_into().unwrap();
        let deg_160_1 = Longitude::with_angle_and_direction(
            AccurateDegree::with_dms(160, 15, 1, 84).unwrap(),
            East,
        )
        .unwrap();
        let deg_180 = Longitude::anti_meridian();

        vec![
            greenwich, deg_20, deg_45, deg_60, deg_75, deg_90, deg_130, deg_160_1, deg_180,
        ]
    }

    #[test]
    fn east() {
        let longs = east_meridians();
        for (i, (first, second)) in longs.iter().zip(&longs[1..]).enumerate() {
            dbg!(first);
            dbg!(second);

            if i > 0 {
                assert_eq!(first.direction(), Some(East));
            }
            if i < longs.len() - 2 {
                assert_eq!(second.direction(), Some(East));
            }
            assert!(first < second);
        }
    }

    fn west_meridians() -> Vec<Longitude<AccurateDegree>> {
        east_meridians().into_iter().map(|lon| -lon).collect()
    }

    #[test]
    fn west() {
        let longs = west_meridians();
        for (i, (first, second)) in longs.iter().zip(&longs[1..]).enumerate() {
            dbg!(first);
            dbg!(second);

            if i > 0 {
                assert_eq!(first.direction(), Some(West));
            }
            if i < longs.len() - 2 {
                assert_eq!(second.direction(), Some(West));
            }
            assert!(first < second);
        }
    }

    #[test]
    fn east_and_west_are_non_comparable() {
        let len = east_meridians().len();
        for e in &east_meridians()[1..len - 1] {
            for w in &west_meridians()[1..len - 1] {
                dbg!(e);
                dbg!(w);
                assert!(e.partial_cmp(w).is_none());
            }
        }
    }

    #[test]
    fn prime_is_always_less() {
        let p = Longitude::<AccurateDegree>::prime();
        east_meridians()
            .iter()
            .skip(1)
            .chain(&west_meridians()[1..])
            .for_each(|&non_zero| {
                dbg!(non_zero);
                assert!(non_zero > p);
                assert!(p < non_zero);
            });
    }

    #[test]
    fn anti_is_always_greater() {
        let anti = Longitude::<AccurateDegree>::anti_meridian();
        east_meridians()
            .iter()
            .rev()
            .skip(1)
            .chain(west_meridians().iter().rev().skip(1))
            .for_each(|&not_180| {
                dbg!(not_180);
                assert!(not_180 < anti);
                assert!(anti > not_180);
            });
    }

    #[test]
    fn neg_prime_is_prime() {
        let p = Longitude::<AccurateDegree>::prime();
        assert_eq!(p, -p);
    }

    #[test]
    fn equal_prime() {
        let prime = Longitude::prime();
        let prime1 = Longitude::east(0).unwrap();
        let prime2 = Longitude::west(0).unwrap();
        let prime3 = Longitude::with_angle_only(AccurateDegree::zero()).unwrap();
        let prime4 = Longitude::with_angle_and_direction(
            AccurateDegree::with_dms(0, 0, 0, 0).unwrap(),
            East,
        )
        .unwrap();
        let prime5 = Longitude::with_angle_and_direction(AccurateDegree::complete(), West).unwrap();
        let prime6 = Longitude::anti_meridian().opposite();

        assert_eq!(prime, prime1);
        assert_eq!(prime1, prime2);
        assert_eq!(prime2, prime3);
        assert_eq!(prime3, prime4);
        assert_eq!(prime4, prime5);
        assert_eq!(prime5, prime6);
        assert!(prime.direction().is_none());
    }

    #[test]
    fn equal_anti_meridian() {
        let anti = Longitude::anti_meridian();
        let anti1 = Longitude::east(180).unwrap();
        let anti2 = Longitude::west(180.0).unwrap();
        let anti3 = Longitude::with_angle_and_direction(AccurateDegree::straight(), East).unwrap();
        let anti4 = Longitude::with_angle_and_direction(AccurateDegree::straight(), West).unwrap();
        let anti5 = Longitude::with_angle_only(AccurateDegree::straight()).unwrap();

        assert_eq!(anti, anti1);
        assert_eq!(anti1, anti2);
        assert_eq!(anti2, anti3);
        assert_eq!(anti3, anti4);
        assert_eq!(anti4, anti5);
        assert!(anti.direction().is_none());
    }

    #[test]
    #[should_panic(expected = "ReflexAngle")]
    fn bad_longitude_east() {
        let _l = Longitude::<AccurateDegree>::east(200).unwrap();
    }

    #[test]
    #[should_panic(expected = "ReflexAngle")]
    fn bad_longitude_east_2() {
        let _l = Longitude::<AccurateDegree>::try_from([200, 0]).unwrap();
    }

    #[test]
    fn good_longitude_west() {
        let l: Longitude<AccurateDegree> = [-180, 0].try_into().unwrap();
        assert_eq!(l, Longitude::anti_meridian())
    }

    #[test]
    #[should_panic(expected = "ReflexAngle")]
    fn bad_longitude_west() {
        let _l = Longitude::<AccurateDegree>::try_from([-200, 0]).unwrap();
    }

    #[test]
    fn opposite_longitudes() {
        let l = Longitude::<AccurateDegree>::east((50, 14, 21)).unwrap();
        let opp = l.opposite();
        assert_eq!(opp, Longitude::west([129, 45, 39]).unwrap());
    }

    #[test]
    fn prime_and_anti_are_opposed_meridians() {
        let p = Longitude::<AccurateDegree>::prime();
        let a = Longitude::anti_meridian();
        assert_eq!(p.opposite(), a);
        assert_eq!(a.opposite(), p)
    }

    #[test]
    fn west_0_is_prime() {
        let p = Longitude::<AccurateDegree>::west(0).unwrap();
        let a = Longitude::anti_meridian();
        assert_eq!(p.opposite(), a);
        assert_eq!(a.opposite(), p);
        assert_eq!(p.angle(), AccurateDegree::zero())
    }

    #[test]
    fn from_f64_east() {
        let l: Longitude<AccurateDegree> = 41.622_512.try_into().unwrap();
        assert_eq!(l.direction(), Some(East));
        assert!(l
            .angle()
            .almost_equal(AccurateDegree::with_dms(41, 37, 21, 4).unwrap()));
    }

    #[test]
    fn from_f64_west() {
        let l = Longitude::<AccurateDegree>::try_from(-84.120_456).unwrap();
        assert_eq!(l.direction(), Some(West));
        assert!(l
            .angle()
            .almost_equal(AccurateDegree::with_dms(84, 7, 13, 64).unwrap()));
    }

    #[test]
    #[should_panic(expected = "ReflexAngle")]
    fn from_f64_overflow() {
        let _l = Longitude::<AccurateDegree>::try_from(190.622_512).unwrap();
    }
}

#[cfg(test)]
mod parse_tests_accur {
    use crate::angle::{dms_dd::AccurateDegree, AngleNames};

    use super::*;

    #[test]
    fn simple_degree() {
        let l: Longitude<AccurateDegree> = "15° E".parse().unwrap();

        assert_eq!(l.direction(), Some(East));
        assert_eq!(l.angle(), AccurateDegree::try_from(15).unwrap());
    }

    #[test]
    fn suffix_decimal() {
        let l: Longitude<AccurateDegree> = "34.1551784° E".parse().unwrap();
        let l_ascii: Longitude<AccurateDegree> = "34.1551784E".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(East));
        assert_eq!(l.angle(), AccurateDegree::try_from(34.155_178_4).unwrap());
    }

    #[test]
    fn suffix_with_space() {
        let l: Longitude<AccurateDegree> = "34°16′22″ E".parse().unwrap();
        let l_ascii: Longitude<AccurateDegree> = "34* 16' 22\" E".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(East));
        assert_eq!(l.angle(), AccurateDegree::with_dms(34, 16, 22, 0).unwrap());
    }

    #[test]
    fn suffix_no_space() {
        let l: Longitude<AccurateDegree> = "43° 20′ 7.15″W".parse().unwrap();
        let l_ascii: Longitude<AccurateDegree> = "43 20'7.15\"W".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(West));
        assert_eq!(l.angle(), AccurateDegree::with_dms(43, 20, 7, 15).unwrap());
    }

    #[test]
    fn prefix_decimal() {
        let l: Longitude<AccurateDegree> = "W 34.0045°".parse().unwrap();
        let l_ascii: Longitude<AccurateDegree> = "W34.0045".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(West));
        assert_eq!(l.angle(), AccurateDegree::try_from(34.0045).unwrap());
    }

    #[test]
    fn prefix_with_space() {
        let l: Longitude<AccurateDegree> = "E 34°16′0″".parse().unwrap();
        let l_ascii: Longitude<AccurateDegree> = "E 34* 16'".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(East));
        assert_eq!(l.angle(), AccurateDegree::with_dms(34, 16, 0, 0).unwrap());
    }

    #[test]
    fn prefix_no_space() {
        let l: Longitude<AccurateDegree> = "W89° 0′ 2.44″".parse().unwrap();
        let l_ascii: Longitude<AccurateDegree> = "W89 0'2.44\"".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(West));
        assert_eq!(l.angle(), AccurateDegree::with_dms(89, 0, 2, 44).unwrap());
    }

    #[test]
    fn prefix_sign_decimal() {
        let l: Longitude<AccurateDegree> = "-34.0045°".parse().unwrap();
        let l_ascii: Longitude<AccurateDegree> = "-34.0045".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(West));
        assert_eq!(l.angle(), AccurateDegree::try_from(34.0045).unwrap());
    }

    #[test]
    fn prefix_sign_with_space() {
        let l: Longitude<AccurateDegree> = "+34°16′0″".parse().unwrap();
        let l_ascii: Longitude<AccurateDegree> = "+34 16'".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(East));
        assert_eq!(l.angle(), AccurateDegree::with_dms(34, 16, 0, 0).unwrap());
    }

    #[test]
    fn prefix_sign_no_space() {
        let l: Longitude<AccurateDegree> = "-89° 0′ 2.44″".parse().unwrap();
        let l_ascii: Longitude<AccurateDegree> = "-89*0'2.44\"".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(West));
        assert_eq!(l.angle(), AccurateDegree::with_dms(89, 0, 2, 44).unwrap());
    }

    #[test]
    fn prime_does_not_require_pole() {
        let p1: Longitude<AccurateDegree> = "0°".parse().unwrap();
        let p2: Longitude<AccurateDegree> = "0".parse().unwrap();
        let p3: Longitude<AccurateDegree> = "0 0'0\"".parse().unwrap();
        assert_eq!(p1, p2);
        assert_eq!(p2, p3);
        assert!(p1.angle().is_zero());
    }

    #[test]
    fn anti_does_not_require_pole() {
        let p1: Longitude<AccurateDegree> = "180°".parse().unwrap();
        let p2: Longitude<AccurateDegree> = "180.0".parse().unwrap();
        let p3: Longitude<AccurateDegree> = "180 0'0\"".parse().unwrap();
        assert_eq!(p1, p2);
        assert_eq!(p2, p3);
        assert!(p1.angle().is_straight());
    }
}

#[cfg(test)]
mod bad_parse_tests_accur {
    use crate::angle::dms_dd::AccurateDegree;

    use super::*;

    #[test]
    #[should_panic(expected = "NoHemisphere")]
    fn no_prefix_no_suffix() {
        let _l: Longitude<AccurateDegree> = "15°".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "EmptyString")]
    fn empty() {
        let _l: Longitude<AccurateDegree> = "".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(DmsNotation)")]
    fn bad_sign() {
        let _l: Longitude<AccurateDegree> = "--89° 16′".parse().unwrap();
    }

    #[test]
    // if cannot parse the float, fallback to DMS, therefore
    // not a `Float`, but `DmsNotation` variant
    #[should_panic(expected = "Angle(DmsNotation)")]
    fn bad_float() {
        let _l: Longitude<AccurateDegree> = "-15.46.11".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(AngleNotInRange(ReflexAngle))")]
    fn too_big_angle_east() {
        let _l: Longitude<AccurateDegree> = "+190°16′".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(AngleNotInRange(ReflexAngle))")]
    fn too_big_angle_west() {
        let _l: Longitude<AccurateDegree> = "-181".parse().unwrap();
    }

    #[test]
    fn round_more_than_7_digits() {
        let l: Longitude<AccurateDegree> = "-18.99999995°".parse().unwrap();
        // 90 - 18.9999999 = 70.0000001
        assert_eq!(
            l.angle().complement().unwrap(),
            AccurateDegree::try_from(71.000_000_1).unwrap()
        );
    }

    #[test]
    #[should_panic(expected = "NoHemisphere")]
    fn bad_direction() {
        let _l: Longitude<AccurateDegree> = "Z18.15°".parse().unwrap();
    }

    #[test]
    fn more_than_right_angle() {
        let l_east: Longitude<AccurateDegree> = "+123* 34' 42\"".parse().unwrap();
        let l_west: Longitude<AccurateDegree> = "-123 34' 42\"".parse().unwrap();

        assert_eq!(l_east, -l_west);
        assert_eq!(-l_east, l_west);

        assert_eq!(l_east.angle().degrees(), 123);
    }
}

#[cfg(test)]
mod tests_dec {
    use std::mem::size_of;

    use crate::angle::{dd::DecimalDegree, AngleNames};

    use super::*;

    #[test]
    fn size_long() {
        assert_eq!(size_of::<Longitude<DecimalDegree>>(), 4);
    }

    fn east_meridians() -> Vec<Longitude<DecimalDegree>> {
        let greenwich = Longitude::prime();
        let deg_20 = Longitude::east(20).unwrap();
        let deg_45 = (45, 20, 15, 180).try_into().unwrap();
        let deg_60 = Longitude::east(60.145).unwrap();
        let deg_75 = -(Longitude::west((75, 43, 21, 183)).unwrap());
        let deg_90 = [90, 20].try_into().unwrap();
        let deg_130 = 130.try_into().unwrap();
        let deg_160_1 = Longitude::with_angle_and_direction(
            DecimalDegree::with_dms(160, 15, 1, 845).unwrap(),
            East,
        )
        .unwrap();
        let deg_180 = Longitude::anti_meridian();

        vec![
            greenwich, deg_20, deg_45, deg_60, deg_75, deg_90, deg_130, deg_160_1, deg_180,
        ]
    }

    #[test]
    fn east() {
        let longs = east_meridians();
        for (i, (first, second)) in longs.iter().zip(&longs[1..]).enumerate() {
            dbg!(first);
            dbg!(second);

            if i > 0 {
                assert_eq!(first.direction(), Some(East));
            }
            if i < longs.len() - 2 {
                assert_eq!(second.direction(), Some(East));
            }
            assert!(first < second);
        }
    }

    fn west_meridians() -> Vec<Longitude<DecimalDegree>> {
        east_meridians().into_iter().map(|lon| -lon).collect()
    }

    #[test]
    fn west() {
        let longs = west_meridians();
        for (i, (first, second)) in longs.iter().zip(&longs[1..]).enumerate() {
            dbg!(first);
            dbg!(second);

            if i > 0 {
                assert_eq!(first.direction(), Some(West));
            }
            if i < longs.len() - 2 {
                assert_eq!(second.direction(), Some(West));
            }
            assert!(first < second);
        }
    }

    #[test]
    fn east_and_west_are_non_comparable() {
        let len = east_meridians().len();
        for e in &east_meridians()[1..len - 1] {
            for w in &west_meridians()[1..len - 1] {
                dbg!(e);
                dbg!(w);
                assert!(e.partial_cmp(w).is_none());
            }
        }
    }

    #[test]
    fn prime_is_always_less() {
        let p = Longitude::<DecimalDegree>::prime();
        east_meridians()
            .iter()
            .skip(1)
            .chain(&west_meridians()[1..])
            .for_each(|&non_zero| {
                dbg!(non_zero);
                assert!(non_zero > p);
                assert!(p < non_zero);
            });
    }

    #[test]
    fn anti_is_always_greater() {
        let anti = Longitude::<DecimalDegree>::anti_meridian();
        east_meridians()
            .iter()
            .rev()
            .skip(1)
            .chain(west_meridians().iter().rev().skip(1))
            .for_each(|&not_180| {
                dbg!(not_180);
                assert!(not_180 < anti);
                assert!(anti > not_180);
            });
    }

    #[test]
    fn neg_prime_is_prime() {
        let p = Longitude::<DecimalDegree>::prime();
        assert_eq!(p, -p);
    }

    #[test]
    fn equal_prime() {
        let prime = Longitude::prime();
        let prime1 = Longitude::east(0).unwrap();
        let prime2 = Longitude::west(0).unwrap();
        let prime3 = Longitude::with_angle_only(DecimalDegree::zero()).unwrap();
        let prime4 =
            Longitude::with_angle_and_direction(DecimalDegree::with_dms(0, 0, 0, 0).unwrap(), East)
                .unwrap();
        let prime5 = Longitude::with_angle_and_direction(DecimalDegree::complete(), West).unwrap();
        let prime6 = Longitude::anti_meridian().opposite();

        assert_eq!(prime, prime1);
        assert_eq!(prime1, prime2);
        assert_eq!(prime2, prime3);
        assert_eq!(prime3, prime4);
        assert_eq!(prime4, prime5);
        assert_eq!(prime5, prime6);
        assert!(prime.direction().is_none());
    }

    #[test]
    fn equal_anti_meridian() {
        let anti = Longitude::anti_meridian();
        let anti1 = Longitude::east(180).unwrap();
        let anti2 = Longitude::west(180.0).unwrap();
        let anti3 = Longitude::with_angle_and_direction(DecimalDegree::straight(), East).unwrap();
        let anti4 = Longitude::with_angle_and_direction(DecimalDegree::straight(), West).unwrap();
        let anti5 = Longitude::with_angle_only(DecimalDegree::straight()).unwrap();

        assert_eq!(anti, anti1);
        assert_eq!(anti1, anti2);
        assert_eq!(anti2, anti3);
        assert_eq!(anti3, anti4);
        assert_eq!(anti4, anti5);
        assert!(anti.direction().is_none());
    }

    #[test]
    #[should_panic(expected = "ReflexAngle")]
    fn bad_longitude_east() {
        let _l = Longitude::<DecimalDegree>::east(200).unwrap();
    }

    #[test]
    #[should_panic(expected = "ReflexAngle")]
    fn bad_longitude_east_2() {
        let _l = Longitude::<DecimalDegree>::try_from([200, 0]).unwrap();
    }

    #[test]
    fn good_longitude_west() {
        let l: Longitude<DecimalDegree> = [-180, 0].try_into().unwrap();
        assert_eq!(l, Longitude::anti_meridian())
    }

    #[test]
    #[should_panic(expected = "ReflexAngle")]
    fn bad_longitude_west() {
        let _l = Longitude::<DecimalDegree>::try_from([-200, 0]).unwrap();
    }

    #[test]
    fn opposite_longitudes() {
        let l = Longitude::<DecimalDegree>::east((50, 14, 21)).unwrap();
        let opp = l.opposite();
        assert_eq!(opp, Longitude::west([129, 45, 39]).unwrap());
    }

    #[test]
    fn prime_and_anti_are_opposed_meridians() {
        let p = Longitude::<DecimalDegree>::prime();
        let a = Longitude::anti_meridian();
        assert_eq!(p.opposite(), a);
        assert_eq!(a.opposite(), p)
    }

    #[test]
    fn west_0_is_prime() {
        let p = Longitude::<DecimalDegree>::west(0).unwrap();
        let a = Longitude::anti_meridian();
        assert_eq!(p.opposite(), a);
        assert_eq!(a.opposite(), p);
        assert_eq!(p.angle(), DecimalDegree::zero())
    }

    #[test]
    fn from_f64_east() {
        let l: Longitude<DecimalDegree> = 41.622_512.try_into().unwrap();
        assert_eq!(l.direction(), Some(East));
        assert!(l
            .angle()
            .almost_equal(DecimalDegree::with_dms(41, 37, 21, 43).unwrap()));
    }

    #[test]
    fn from_f64_west() {
        let l = Longitude::<DecimalDegree>::try_from(-84.120_456).unwrap();
        assert_eq!(l.direction(), Some(West));
        assert!(l
            .angle()
            .almost_equal(DecimalDegree::with_dms(84, 7, 13, 642).unwrap()));
    }

    #[test]
    #[should_panic(expected = "ReflexAngle")]
    fn from_f64_overflow() {
        let _l = Longitude::<DecimalDegree>::try_from(190.622_512).unwrap();
    }
}

#[cfg(test)]
mod parse_tests_dec {
    use crate::angle::{dd::DecimalDegree, AngleNames};

    use super::*;

    #[test]
    fn simple_degree() {
        let l: Longitude<DecimalDegree> = "15° E".parse().unwrap();

        assert_eq!(l.direction(), Some(East));
        assert_eq!(l.angle(), DecimalDegree::try_from(15).unwrap());
    }

    #[test]
    fn suffix_decimal() {
        let l: Longitude<DecimalDegree> = "34.1551784° E".parse().unwrap();
        let l_ascii: Longitude<DecimalDegree> = "34.1551784E".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(East));
        assert_eq!(l.angle(), DecimalDegree::try_from(34.155_178_4).unwrap());
    }

    #[test]
    fn suffix_with_space() {
        let l: Longitude<DecimalDegree> = "34°16′22″ E".parse().unwrap();
        let l_ascii: Longitude<DecimalDegree> = "34* 16' 22\" E".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(East));
        assert_eq!(l.angle(), DecimalDegree::with_dms(34, 16, 22, 0).unwrap());
    }

    #[test]
    fn suffix_no_space() {
        let l: Longitude<DecimalDegree> = "43° 20′ 7.15″W".parse().unwrap();
        let l_ascii: Longitude<DecimalDegree> = "43 20'7.15\"W".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(West));
        assert_eq!(l.angle(), DecimalDegree::with_dms(43, 20, 7, 150).unwrap());
    }

    #[test]
    fn prefix_decimal() {
        let l: Longitude<DecimalDegree> = "W 34.0045°".parse().unwrap();
        let l_ascii: Longitude<DecimalDegree> = "W34.0045".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(West));
        assert_eq!(l.angle(), DecimalDegree::try_from(34.0045).unwrap());
    }

    #[test]
    fn prefix_with_space() {
        let l: Longitude<DecimalDegree> = "E 34°16′0″".parse().unwrap();
        let l_ascii: Longitude<DecimalDegree> = "E 34* 16'".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(East));
        assert_eq!(l.angle(), DecimalDegree::with_dms(34, 16, 0, 0).unwrap());
    }

    #[test]
    fn prefix_no_space() {
        let l: Longitude<DecimalDegree> = "W89° 0′ 2.44″".parse().unwrap();
        let l_ascii: Longitude<DecimalDegree> = "W89 0'2.44\"".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(West));
        assert_eq!(l.angle(), DecimalDegree::with_dms(89, 0, 2, 440).unwrap());
    }

    #[test]
    fn prefix_sign_decimal() {
        let l: Longitude<DecimalDegree> = "-34.0045°".parse().unwrap();
        let l_ascii: Longitude<DecimalDegree> = "-34.0045".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(West));
        assert_eq!(l.angle(), DecimalDegree::try_from(34.0045).unwrap());
    }

    #[test]
    fn prefix_sign_with_space() {
        let l: Longitude<DecimalDegree> = "+34°16′0″".parse().unwrap();
        let l_ascii: Longitude<DecimalDegree> = "+34 16'".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(East));
        assert_eq!(l.angle(), DecimalDegree::with_dms(34, 16, 0, 0).unwrap());
    }

    #[test]
    fn prefix_sign_no_space() {
        let l: Longitude<DecimalDegree> = "-89° 0′ 2.44″".parse().unwrap();
        let l_ascii: Longitude<DecimalDegree> = "-89*0'2.44\"".parse().unwrap();
        assert_eq!(l_ascii, l);

        assert_eq!(l.direction(), Some(West));
        assert_eq!(l.angle(), DecimalDegree::with_dms(89, 0, 2, 440).unwrap());
    }

    #[test]
    fn prime_does_not_require_pole() {
        let p1: Longitude<DecimalDegree> = "0°".parse().unwrap();
        let p2: Longitude<DecimalDegree> = "0".parse().unwrap();
        let p3: Longitude<DecimalDegree> = "0 0'0\"".parse().unwrap();
        assert_eq!(p1, p2);
        assert_eq!(p2, p3);
        assert!(p1.angle().is_zero());
    }

    #[test]
    fn anti_does_not_require_pole() {
        let p1: Longitude<DecimalDegree> = "180°".parse().unwrap();
        let p2: Longitude<DecimalDegree> = "180.0".parse().unwrap();
        let p3: Longitude<DecimalDegree> = "180 0'0\"".parse().unwrap();
        assert_eq!(p1, p2);
        assert_eq!(p2, p3);
        assert!(p1.angle().is_straight());
    }
}

#[cfg(test)]
mod bad_parse_tests_dec {
    use crate::angle::dd::DecimalDegree;

    use super::*;

    #[test]
    #[should_panic(expected = "NoHemisphere")]
    fn no_prefix_no_suffix() {
        let _l: Longitude<DecimalDegree> = "15°".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "EmptyString")]
    fn empty() {
        let _l: Longitude<DecimalDegree> = "".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(DmsNotation)")]
    fn bad_sign() {
        let _l: Longitude<DecimalDegree> = "--89° 16′".parse().unwrap();
    }

    #[test]
    // if cannot parse the float, fallback to DMS, therefore
    // not a `Float`, but `DmsNotation` variant
    #[should_panic(expected = "Angle(DmsNotation)")]
    fn bad_float() {
        let _l: Longitude<DecimalDegree> = "-15.46.11".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(AngleNotInRange(ReflexAngle))")]
    fn too_big_angle_east() {
        let _l: Longitude<DecimalDegree> = "+190°16′".parse().unwrap();
    }

    #[test]
    #[should_panic(expected = "Angle(AngleNotInRange(ReflexAngle))")]
    fn too_big_angle_west() {
        let _l: Longitude<DecimalDegree> = "-181".parse().unwrap();
    }

    #[test]
    fn round_more_than_7_digits() {
        let l: Longitude<DecimalDegree> = "-18.99999995°".parse().unwrap();
        // 90 - 18.9999999 = 70.0000001
        assert_eq!(
            l.angle().complement().unwrap(),
            DecimalDegree::try_from(71.000_000_1).unwrap()
        );
    }

    #[test]
    #[should_panic(expected = "NoHemisphere")]
    fn bad_direction() {
        let _l: Longitude<DecimalDegree> = "Z18.15°".parse().unwrap();
    }

    #[test]
    fn more_than_right_angle() {
        let l_east: Longitude<DecimalDegree> = "+123* 34' 42\"".parse().unwrap();
        let l_west: Longitude<DecimalDegree> = "-123 34' 42\"".parse().unwrap();

        assert_eq!(l_east, -l_west);
        assert_eq!(-l_east, l_west);

        assert_eq!(l_east.angle().degrees(), 123);
    }
}
