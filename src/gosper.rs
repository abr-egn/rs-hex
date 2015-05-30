use super::{Hex, Delta, Direction, Rotation, Iter};

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
        if self.level == 0 {
            return None;
        }
        let middle = Island {center: self.center, level: self.level-1};
        let split_offset = offset(self.level-1);
        let side = |n| {
            let mut center = self.center + split_offset;
            for _ in (0..n) {
                center = center.rotate_around(self.center, Rotation::CW);
            }
            center
        };
        let side_dirs = vec![Direction::XY, Direction::XZ, Direction::YZ,
                             Direction::YX, Direction::ZX, Direction::ZY];
        let sides = (0..6).map(|n| Island {center: side(n), level: self.level-1});
        Some((middle, side_dirs.into_iter().zip(sides).collect()))
    }

    pub fn hexes(&self) -> Iter {
        if self.level == 0 {
            return Box::new(Some(self.center).into_iter());
        }
        let (middle, sides) = self.split().unwrap();
        Box::new(middle.hexes().chain(sides.into_iter().flat_map(|(_, s)| s.hexes())))
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn empty() { }
}  // mod tests
