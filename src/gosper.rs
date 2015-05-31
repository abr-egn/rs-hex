use super::{Hex, Delta, Direction, Rotation, Iter, ORIGIN};

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

/// Gosper Space Partition: coordinate addressing for nested Gosper islands.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
pub struct GSP { pub coord: Hex, pub level: u32 }

fn fold_path(xy: Delta, h: Hex) -> Delta {
    // TODO: use std::iter::iterate when it's stable
    let xz = xy.rotate(Rotation::CW);
    let yz = xz.rotate(Rotation::CW);
    let yx = yz.rotate(Rotation::CW);
    let zx = yx.rotate(Rotation::CW);
    let zy = zx.rotate(Rotation::CW);
    let dir_delta = |dir| match dir {
        Direction::XY   => xy,
        Direction::XZ   => xz,
        Direction::YZ   => yz,
        Direction::YX   => yx,
        Direction::ZX   => zx,
        Direction::ZY   => zy,
    };
    let steps = h.path();
    let trans = steps.into_iter().map(|(d, m)| dir_delta(d) * (m as i32));
    // TODO: use sum() when std::num::Zero is stable
    let mut ret = Delta {dx: 0, dy: 0};
    for d in trans {
        ret = ret + d;
    }
    ret
}

impl GSP {
    pub fn absolute(&self) -> Island {
        if self.level == 0 {
            return Island {center: self.coord, level: 0};
        }
        Island {center: ORIGIN + fold_path(offset(self.level), self.coord), level: self.level}
    }

    fn delta(&self) -> Delta {
        if self.level % 2 == 0 { Delta {dx: 3, dy: -2} } else { Delta {dx: 2, dy: -3} }
    }

    fn path_delta(&self) -> Delta { fold_path(self.delta(), self.coord) }

    pub fn smaller(&self) -> Option<GSP> {
        if self.level == 0 {
            return None;
        }
        Some(GSP {coord: ORIGIN + self.path_delta(), level: self.level-1})
    }

    pub fn larger(&self) -> (GSP, Option<Direction>) {
        let Delta {dx, dy} = self.path_delta();
        let ix = ((dx as f32) / 7.0).round() as i32;
        let iy = ((dy as f32) / 7.0).round() as i32;
        let d = Delta {dx: dx - (ix*7), dy: dy - (iy*7)};
        let mut ret_dir = None;
        if d != (Delta {dx: 0, dy: 0}) {
            let mut ref_d = self.delta();
            for dir in [Direction::XY, Direction::XZ, Direction::YZ,
                        Direction::YX, Direction::ZX, Direction::ZY].iter() {
                if d == ref_d {
                    ret_dir = Some(*dir);
                    break;
                }
                ref_d = ref_d.rotate(Rotation::CW);
            }
            if ret_dir.is_none() { panic!("Invalid delta {:?}", d); }
        }
        (GSP {coord: Hex {x: ix, y: iy}, level: self.level+1}, ret_dir)
    }
}

#[cfg(test)]
mod tests {
    extern crate quickcheck;
    extern crate rand;

    use super::{Island};

    use self::quickcheck::quickcheck;

    use std::collections::HashSet;

    impl quickcheck::Arbitrary for Island {
        fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
            let center = quickcheck::Arbitrary::arbitrary(g);
            let level = g.gen_range(0, 5);
            Island {center: center, level: level}
        }
        fn shrink(&self) -> Box<Iterator<Item=Island>> {
            let level = self.level;
            let shrink_center = self.center.shrink().map(move |h| Island {center: h, level: level});
            if level == 0 {
                Box::new(shrink_center)
            } else {
                Box::new(Some(Island {center: self.center, level: self.level-1}).into_iter().chain(shrink_center))
            }
        }
    }

    // Number of hexes in a Gosper island is 7^level
    #[test]
    fn island_size() {
        fn prop(i: Island) -> bool { i.hexes().count() == (7 as usize).pow(i.level) }
        quickcheck(prop as fn(Island) -> bool);
    }

    // All hexes in a Gosper island are unique
    #[test]
    fn island_unique() {
        fn prop(i: Island) -> bool {
            let hs: HashSet<_> = i.hexes().collect();
            hs.len() == (7 as usize).pow(i.level)
        }
        quickcheck(prop as fn(Island) -> bool);
    }
}  // mod tests
