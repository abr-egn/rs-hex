use super::{Hex, Delta, Direction};

use std::ops::Div;

/// The delta from the center of one group to the next at the given zoom level.
///
/// Zoom levels:
///     0   => single hex
///     1   => seven hex group (six sides plus center)
///     2   => seven groups of zoom 1
///     ...
pub fn offset(level: u32) -> Delta {
    let increment = level.div(2);
    let scale = (7 as i32).pow(increment);
    scale * if level % 2 == 0 {
        Direction::XY.delta()
    } else {
        Delta {dx: 2, dy: -3}
    }
}

/// A Gosper island with a given center and zoom level.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
pub struct Island { pub center: Hex, pub level: u32 }

impl Island {
    pub fn split(&self) -> Option<(Island, Vec<(Direction, Island)>)> {
        None
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn empty() { }
}
