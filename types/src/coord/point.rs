use std::{
    convert::{TryFrom, TryInto},
    fmt,
};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use crate::angle::Angle;

use super::{
    lat::{
        Latitude,
        Pole::{North, South},
    },
    lon::Longitude,
};

#[derive(Debug)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
/// The point on the surface of an ellipsoid, represented as the pair (latitude, longitude)
pub struct Point<A: Angle> {
    lat: Latitude<A>,
    lon: Longitude<A>,
}

impl<A: Angle> Point<A> {
    /// Construct a point from the given latitude and longitude
    pub fn new(lat: Latitude<A>, lon: Longitude<A>) -> Self {
        Self { lat, lon }
    }

    /// Construct a point on the surface with some numeric information about
    /// latitude and longitude.
    ///
    /// # Errors
    /// An overflow of some kind can appear when constructing latitude or longitude from the given numbers.
    pub fn with_coordinates<Lat, Lon>(lat: Lat, lon: Lon) -> Result<Self, A::NumErr>
    where
        Latitude<A>: TryFrom<Lat, Error = A::NumErr>,
        Longitude<A>: TryFrom<Lon, Error = A::NumErr>,
    {
        let lat = lat.try_into()?;
        let lon = lon.try_into()?;
        Ok(Self { lat, lon })
    }

    /// Construct a north pole point (lat=90, lon=0 (by convention)).
    pub fn north_pole() -> Self {
        // All longitude values reach singularity on a pole, so put it zero
        Self::new(North.into(), Longitude::prime())
    }

    /// Construct a south pole point (lat=-90, lon=0 (by convention)).
    pub fn south_pole() -> Self {
        // All longitude values reach singularity on a pole, so put it zero
        Self::new(South.into(), Longitude::prime())
    }

    /// Is the point represents a pole?
    /// All the longitudes at pole are singular, so the longitude of the pole can be any meridian.
    pub fn is_pole(&self) -> bool {
        self.lat.is_pole()
    }

    /// The diametrically opposite point
    pub fn antipodal(&self) -> Self {
        Self {
            lat: -self.lat,
            lon: self.lon.opposite(),
        }
    }
}

impl<A: Angle> PartialEq for Point<A> {
    fn eq(&self, other: &Self) -> bool {
        if self.lat == other.lat {
            // meridians at the poles do not matter
            if self.lat.is_pole() {
                return true;
            }

            if self.lon == other.lon {
                return true;
            }
        }

        false
    }
}

impl<A: Angle> fmt::Display for Point<A>
where
    A: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "Lat: {:#}, Long: {:#}", self.lat, self.lon)
        } else {
            write!(f, "({},{})", self.lat, self.lon)
        }
    }
}

#[cfg(test)]
mod tests_accur {
    use crate::angle::{dms_dd::AccurateDegree, AngleNames};

    use super::super::{
        lon::RotationalDirection::{East, West},
        AngleAndDirection,
    };
    use super::*;

    #[test]
    fn south_pole() {
        let sp = Point::<AccurateDegree>::south_pole();
        assert_eq!(sp.lat.hemisphere(), Some(South));
        assert!(sp.lat.angle_from_equator().is_right());

        assert!(sp.lon.angle().is_zero());
        assert!(sp.lon.direction().is_none());

        assert_eq!(format!("{}", sp), "(-90°,0°)");
        assert_eq!(format!("{:#}", sp), "Lat: 90°S, Long: 0°");
    }

    #[test]
    fn origin_point() {
        let origin = Point::<AccurateDegree>::new(Latitude::equator(), Longitude::prime());
        assert!(origin.lat.hemisphere().is_none());
        assert!(origin.lat.angle_from_equator().is_zero());

        assert!(origin.lon.angle().is_zero());
        assert!(origin.lon.direction().is_none());

        assert_eq!(format!("{}", origin), "(0°,0°)");
        assert_eq!(format!("{:#}", origin), "Lat: 0°, Long: 0°");
    }

    #[test]
    fn north_east() {
        let saint_petersburg = Point::new(
            Latitude::with_angle_and_direction(
                AccurateDegree::with_dms(59, 56, 15, 0).unwrap(),
                North,
            )
            .unwrap(),
            Longitude::east((30, 18, 31, 0)).unwrap(),
        );
        let saint_petersburg2 = Point::with_coordinates([59, 56, 15], (30, 18, 31)).unwrap();
        assert_eq!(saint_petersburg, saint_petersburg2);

        assert_eq!(saint_petersburg.lat.hemisphere(), Some(North));
        assert_eq!(
            saint_petersburg.lat.angle_from_equator(),
            AccurateDegree::with_dms(59, 56, 15, 0).unwrap()
        );

        assert_eq!(
            saint_petersburg.lon.angle(),
            AccurateDegree::with_dms(30, 18, 31, 0).unwrap()
        );
        assert_eq!(saint_petersburg.lon.direction(), Some(East));

        assert_eq!(format!("{}", saint_petersburg), "(59.937500°,30.308611°)");
        assert_eq!(
            format!("{:#}", saint_petersburg),
            "Lat: 59°56′15″N, Long: 30°18′31″E"
        );
    }

    #[test]
    fn south_west() {
        let santiago = Point::new(
            Latitude::with_angle_and_direction(
                AccurateDegree::with_dms(33, 27, 0, 0).unwrap(),
                South,
            )
            .unwrap(),
            Longitude::west([70, 40, 0, 0]).unwrap(),
        );
        let santiago2 = Point::with_coordinates((-33, 27), [-70, 40]).unwrap();
        assert_eq!(santiago, santiago2);

        assert_eq!(santiago.lat.hemisphere(), Some(South));
        assert_eq!(
            santiago.lat.angle_from_equator(),
            AccurateDegree::with_dms(33, 27, 0, 0).unwrap()
        );

        assert_eq!(
            santiago.lon.angle(),
            AccurateDegree::with_dms(70, 40, 0, 0).unwrap()
        );
        assert_eq!(santiago.lon.direction(), Some(West));

        assert_eq!(format!("{}", santiago), "(-33.450000°,-70.666667°)");
        assert_eq!(format!("{:#}", santiago), "Lat: 33°27′S, Long: 70°40′W");
    }

    #[test]
    fn lat3_long4() {
        let point =
            Point::<AccurateDegree>::with_coordinates((-33, 27, 44), [70, 40, 15, 76]).unwrap();
        assert_eq!(point.lat.hemisphere(), Some(South));
        assert_eq!(
            point.lat.angle_from_equator(),
            AccurateDegree::with_dms(33, 27, 44, 0).unwrap()
        );

        assert_eq!(
            point.lon.angle(),
            AccurateDegree::with_dms(70, 40, 15, 76).unwrap()
        );
        assert_eq!(point.lon.direction(), Some(East));

        assert_eq!(format!("{}", point), "(-33.462222°,70.671044°)");
        assert_eq!(
            format!("{:#}", point),
            "Lat: 33°27′44″S, Long: 70°40′15.76″E"
        );
    }

    #[test]
    fn lat4_long3() {
        let point =
            Point::<AccurateDegree>::with_coordinates((33, 27, 44, 33), [-167, 11, 2, 4]).unwrap();
        assert_eq!(point.lat.hemisphere(), Some(North));
        assert_eq!(
            point.lat.angle_from_equator(),
            AccurateDegree::with_dms(33, 27, 44, 33).unwrap()
        );

        assert_eq!(
            point.lon.angle(),
            AccurateDegree::with_dms(167, 11, 2, 4).unwrap()
        );
        assert_eq!(point.lon.direction(), Some(West));

        assert_eq!(format!("{}", point), "(33.462314°,-167.183900°)");
        assert_eq!(
            format!("{:#}", point),
            "Lat: 33°27′44.33″N, Long: 167°11′2.04″W"
        );
    }

    #[test]
    fn from_f64_east_long() {
        let l = Longitude::<AccurateDegree>::try_from(66.914_142).unwrap();
        assert_eq!(l.direction(), Some(East));
        assert!(l
            .angle()
            .almost_equal(AccurateDegree::with_dms(66, 54, 50, 91).unwrap()));
    }

    #[test]
    fn from_f64_west_long() {
        let l: Longitude<_> = (-122.427_478_3).try_into().unwrap();
        assert!(Longitude::with_angle_and_direction(
            AccurateDegree::with_dms(122, 25, 38, 92).unwrap(),
            West,
        )
        .unwrap()
        .angle()
        .almost_equal(l.angle()));
    }
}

#[cfg(test)]
mod tests_dec {
    use crate::angle::{dd::DecimalDegree, AngleNames};

    use super::super::{
        lon::RotationalDirection::{East, West},
        AngleAndDirection,
    };
    use super::*;

    #[test]
    fn south_pole() {
        let sp = Point::<DecimalDegree>::south_pole();
        assert_eq!(sp.lat.hemisphere(), Some(South));
        assert!(sp.lat.angle_from_equator().is_right());

        assert!(sp.lon.angle().is_zero());
        assert!(sp.lon.direction().is_none());

        assert_eq!(format!("{}", sp), "(-90°,0°)");
        assert_eq!(format!("{:#}", sp), "Lat: 90°S, Long: 0°");
    }

    #[test]
    fn origin_point() {
        let origin = Point::<DecimalDegree>::new(Latitude::equator(), Longitude::prime());
        assert!(origin.lat.hemisphere().is_none());
        assert!(origin.lat.angle_from_equator().is_zero());

        assert!(origin.lon.angle().is_zero());
        assert!(origin.lon.direction().is_none());

        assert_eq!(format!("{}", origin), "(0°,0°)");
        assert_eq!(format!("{:#}", origin), "Lat: 0°, Long: 0°");
    }

    #[test]
    fn north_east() {
        let saint_petersburg = Point::new(
            Latitude::with_angle_and_direction(
                DecimalDegree::with_dms(59, 56, 15, 0).unwrap(),
                North,
            )
            .unwrap(),
            Longitude::east((30, 18, 31, 0)).unwrap(),
        );
        let saint_petersburg2 = Point::with_coordinates([59, 56, 15], (30, 18, 31)).unwrap();
        assert_eq!(saint_petersburg, saint_petersburg2);

        assert_eq!(saint_petersburg.lat.hemisphere(), Some(North));
        assert_eq!(
            saint_petersburg.lat.angle_from_equator(),
            DecimalDegree::with_dms(59, 56, 15, 0).unwrap()
        );

        assert_eq!(
            saint_petersburg.lon.angle(),
            DecimalDegree::with_dms(30, 18, 31, 0).unwrap()
        );
        assert_eq!(saint_petersburg.lon.direction(), Some(East));

        assert_eq!(format!("{}", saint_petersburg), "(59.9375000°,30.3086111°)");
        assert_eq!(
            format!("{:#}", saint_petersburg),
            "Lat: 59°56′15″N, Long: 30°18′31″E"
        );
    }

    #[test]
    fn south_west() {
        let santiago = Point::new(
            Latitude::with_angle_and_direction(
                DecimalDegree::with_dms(33, 27, 0, 0).unwrap(),
                South,
            )
            .unwrap(),
            Longitude::west([70, 40, 0, 0]).unwrap(),
        );
        let santiago2 = Point::with_coordinates((-33, 27), [-70, 40]).unwrap();
        assert_eq!(santiago, santiago2);

        assert_eq!(santiago.lat.hemisphere(), Some(South));
        assert_eq!(
            santiago.lat.angle_from_equator(),
            DecimalDegree::with_dms(33, 27, 0, 0).unwrap()
        );

        assert_eq!(
            santiago.lon.angle(),
            DecimalDegree::with_dms(70, 40, 0, 0).unwrap()
        );
        assert_eq!(santiago.lon.direction(), Some(West));

        assert_eq!(format!("{}", santiago), "(-33.4500000°,-70.6666667°)");
        assert_eq!(format!("{:#}", santiago), "Lat: 33°27′S, Long: 70°40′W");
    }

    #[test]
    fn lat3_long4() {
        let point =
            Point::<DecimalDegree>::with_coordinates((-33, 27, 44), [70, 40, 15, 758]).unwrap();
        assert_eq!(point.lat.hemisphere(), Some(South));
        assert_eq!(
            point.lat.angle_from_equator(),
            DecimalDegree::with_dms(33, 27, 44, 0).unwrap()
        );

        assert_eq!(
            point.lon.angle(),
            DecimalDegree::with_dms(70, 40, 15, 758).unwrap()
        );
        assert_eq!(point.lon.direction(), Some(East));

        assert_eq!(format!("{}", point), "(-33.4622222°,70.6710439°)");
        assert_eq!(
            format!("{:#}", point),
            "Lat: 33°27′44″S, Long: 70°40′15.758″E"
        );
    }

    #[test]
    fn lat4_long3() {
        let point =
            Point::<DecimalDegree>::with_coordinates((33, 27, 44, 333), [-167, 11, 2, 45]).unwrap();
        assert_eq!(point.lat.hemisphere(), Some(North));
        assert_eq!(
            point.lat.angle_from_equator(),
            DecimalDegree::with_dms(33, 27, 44, 333).unwrap()
        );

        assert_eq!(
            point.lon.angle(),
            DecimalDegree::with_dms(167, 11, 2, 45).unwrap()
        );
        assert_eq!(point.lon.direction(), Some(West));

        assert_eq!(format!("{}", point), "(33.4623147°,-167.1839014°)");
        assert_eq!(
            format!("{:#}", point),
            "Lat: 33°27′44.333″N, Long: 167°11′2.045″W"
        );
    }

    #[test]
    fn from_f64_east_long() {
        let l = Longitude::<DecimalDegree>::try_from(66.914_142).unwrap();
        assert_eq!(l.direction(), Some(East));
        assert!(l
            .angle()
            .almost_equal(DecimalDegree::with_dms(66, 54, 50, 911).unwrap()));
    }

    #[test]
    fn from_f64_west_long() {
        let l = (-122.427_478_3).try_into().unwrap();
        assert_eq!(
            Longitude::with_angle_and_direction(
                DecimalDegree::with_dms(122, 25, 38, 922).unwrap(),
                West,
            )
            .unwrap(),
            l
        );
    }
}

#[cfg(test)]
mod tests_arith {
    use crate::{AccurateDegree, DecimalDegree};

    use super::*;

    #[test]
    fn simple_antipodal() {
        let p = Point::<DecimalDegree>::with_coordinates([-32, 46, 10], (3, 1, 11)).unwrap();
        assert_eq!(
            p.antipodal(),
            Point::with_coordinates((32, 46, 10), (-176, 58, 49)).unwrap()
        );
    }

    #[test]
    fn poles_are_antipods() {
        let np = Point::<AccurateDegree>::north_pole();
        let sp = Point::south_pole();

        assert_eq!(np.antipodal(), sp);
        assert_eq!(sp.antipodal(), np);
    }

    #[test]
    fn equator_antipodal_is_on_equator() {
        let p = Point::<DecimalDegree>::with_coordinates(0, (15, 34)).unwrap();
        assert_eq!(
            p.antipodal(),
            Point::with_coordinates(0, (-164, 26)).unwrap()
        );
    }
}
