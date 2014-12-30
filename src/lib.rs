#[deriving(PartialEq, Eq, Copy, Clone, Default)]
pub struct Hex { pub x: int, pub y: int, pub z: int }
#[deriving(PartialEq, Eq, Copy, Clone, Default)]
pub struct Delta { pub dx: int, pub dy: int, pub dz: int }

impl Add<Delta, Hex> for Hex {
  fn add(self, Delta {dx, dy, dz}: Delta) -> Hex {
    Hex {x: self.x+dx, y: self.y+dy, z: self.z+dz}
  }
}

impl Sub<Hex, Delta> for Hex {
  fn sub(self, Hex {x, y, z}: Hex) -> Delta {
    Delta {dx: self.x-x, dy: self.y-y, dz: self.z-z}
  }
}

impl Mul<int, Delta> for Delta {
  fn mul(self, f: int) -> Delta {
    Delta {dx: self.dx*f, dy: self.dy*f, dz: self.dz*f}
  }
}

impl Hex {
  pub fn distance_to(self, other: Hex) -> uint {
    use std::num::SignedInt;    // for .abs()

    let Delta {dx, dy, dz} = self - other;
    let mut values = [dx.abs() as uint, dy.abs() as uint, dz.abs() as uint];
    values.sort();
    values[0]+values[1]
  }
  pub fn line(self, dir: Direction, dist: uint) -> Vec<Hex> {
    std::iter::range_inclusive(1, dist).map(|d| self + dir.delta()*(d as int)).collect()
  }
  pub fn neighbors(self) -> Vec<Hex> {
    Direction::all().map(|d| self + d.delta()).collect()
  }
}

#[deriving(PartialEq, Eq, Copy, Clone)]
pub enum Direction { XY, XZ, YZ, YX, ZX, ZY }

impl Direction {
  pub fn all() -> std::slice::Iter<'static, Direction> { DIRECTIONS.iter() }
  pub fn delta(self) -> Delta {
    match self {
      Direction::XY => Delta {dx: 1, dy:-1, dz: 0},
      Direction::XZ => Delta {dx: 1, dy: 0, dz:-1},
      Direction::YZ => Delta {dx: 0, dy: 1, dz:-1},
      Direction::YX => Delta {dx:-1, dy: 1, dz: 0},
      Direction::ZX => Delta {dx:-1, dy: 0, dz: 1},
      Direction::ZY => Delta {dx: 0, dy:-1, dz: 1}
    }
  }
}

static DIRECTIONS: [Direction, ..6] = [Direction::XY, Direction::XZ, Direction::YZ, Direction::YX, Direction::ZX, Direction::ZY];

#[deriving(Copy, Clone)]
pub struct DirIter {
  inner: std::slice::Iter<'static, Direction>
}

impl Iterator<Direction> for DirIter {
  fn next(&mut self) -> Option<Direction> {
    match self.inner.next() {
      None => None,
      Some(&d) => Some(d)
    }
  }
}

#[deriving(PartialEq, Eq, Copy, Clone)]
pub struct Region { center: Hex, radius: uint }

impl Region {
  pub fn contains(self, h: Hex) -> bool { self.center.distance_to(h) <= self.radius }
  pub fn ring(self) -> Vec<Hex> {
    let sides = [(Direction::XY, Direction::YZ),
                 (Direction::XZ, Direction::YX),
                 (Direction::YZ, Direction::ZX),
                 (Direction::YX, Direction::ZY),
                 (Direction::ZX, Direction::XY),
                 (Direction::ZY, Direction::XZ)];
    let mut hexes = vec![];
    for &(start, dir) in sides.iter() {
      hexes.push_all((self.center + start.delta()*(self.radius as int)).line(dir, self.radius).as_slice());
    }
    hexes
  }
  pub fn area(self) -> Vec<Hex> {
    let mut hexes = vec![];
    for r in std::iter::range_inclusive(0, self.radius) {
      let tmp = Region {center: self.center, radius: r};
      hexes.push_all(tmp.ring().as_slice());
    }
    hexes
  }
}
