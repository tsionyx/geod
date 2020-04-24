pub(crate) const MAX_DEGREE: u16 = 360;
pub(crate) const MINUTES_IN_DEGREE: u8 = 60;
pub(crate) const SECONDS_IN_MINUTE: u8 = 60;

pub(crate) const DEGREE_SIGN: char = '°';
pub(crate) const ARC_MINUTE_SIGN: char = '′';
pub(crate) const ARC_SECOND_SIGN: char = '″';

pub(crate) const FULL_TURN_DEG: u16 = MAX_DEGREE;
pub(crate) const HALF_TURN_DEG: u16 = FULL_TURN_DEG >> 1;
pub(crate) const QUARTER_TURN_DEG: u16 = HALF_TURN_DEG >> 1;
