#[deriving(PartialEq, Eq, Copy)]
pub struct Hex { pub x: int, pub y: int, pub z: int }
#[deriving(PartialEq, Eq, Copy)]
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

pub fn distance(a: Hex, b: Hex) -> uint {
  use std::num::SignedInt;    // for .abs()

  let Delta {dx, dy, dz} = a - b;
  let mut values = [dx.abs() as uint, dy.abs() as uint, dz.abs() as uint];
  values.sort();
  values[0]+values[1]
}

#[deriving(PartialEq, Eq, Copy)]
pub enum Direction { XY, XZ, YZ, YX, ZX, ZY }

static DIRECTIONS: [Direction, ..6] = [Direction::XY, Direction::XZ, Direction::YZ, Direction::YX, Direction::ZX, Direction::ZY];

#[deriving(Copy)]
pub struct DirIter {
  inner: std::slice::Iter<'static, Direction>
}

impl Direction {
  pub fn all() -> std::slice::Iter<'static, Direction> { DIRECTIONS.iter() }
}

impl Iterator<Direction> for DirIter {
  fn next(&mut self) -> Option<Direction> {
    match self.inner.next() {
      None => None,
      Some(&d) => Some(d)
    }
  }
}
/*

impl Direction {
  pub fn delta(self) -> Delta {
    match self {
      XY => Delta {dx: 1, dy:-1, dz: 0},
      XZ => Delta {dx: 1, dy: 0, dz:-1},
      YZ => Delta {dx: 0, dy: 1, dz:-1},
      YX => Delta {dx:-1, dy: 1, dz: 0},
      ZX => Delta {dx:-1, dy: 0, dz: 1},
      ZY => Delta {dx: 0, dy:-1, dz: 1}
    }
  }
}

#[deriving(Eq, TotalEq, ToStr, Clone)]
pub struct Region { center: Hex, radius: uint }

impl Region {
  pub fn contains(self, h: Hex) -> bool { distance(self.center, h) <= self.radius }
  pub fn ring(self) -> ~[Hex] {
    let sides = [(XY, YZ), (XZ, YX), (YZ, ZX), (YX, ZY), (ZX, XY), (ZY, XZ)];
    let mut hexes = ~[];
    for &(start, dir) in sides.iter() {
      hexes.push_all_move(line(self.center + start.delta()*(self.radius as int), dir, self.radius));
    }
    hexes
  }
  pub fn area(self) -> ~[Hex] {
    let mut hexes = ~[];
    for r in std::iter::range_inclusive(0, self.radius) {
      let tmp = Region {center: self.center, radius: r};
      hexes.push_all_move(tmp.ring());
    }
    hexes
  }
}

impl Hex {
  pub fn neighbors(self) -> ~[Hex] {
    Direction::all().map(|d| self + d.delta()).collect()
  }
}

pub fn line(start: Hex, dir: Direction, dist: uint) -> ~[Hex] {
  std::iter::range_inclusive(1, dist).map(|d| start + dir.delta()*(d as int)).collect()
}
*/
