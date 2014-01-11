#[desc = "Hex grids"];
#[license = "MIT"];

#[deriving(Eq, Zero, ToStr)]
pub struct Hex { x: int, y: int, z: int }
#[deriving(Eq, Zero, ToStr)]
pub struct Delta { dx: int, dy: int, dz: int }

impl Add<Delta, Hex> for Hex {
  fn add(&self, &Delta {dx, dy, dz}: &Delta) -> Hex {
    Hex {x: self.x+dx, y: self.y+dy, z: self.z+dz}
  }
}

impl Sub<Hex, Delta> for Hex {
  fn sub(&self, &Hex {x, y, z}: &Hex) -> Delta {
    Delta {dx: self.x-x, dy: self.y-y, dz: self.z-z}
  }
}

impl Mul<int, Delta> for Delta {
  fn mul(&self, &f: &int) -> Delta {
    Delta {dx: self.dx*f, dy: self.dy*f, dz: self.dz*f}
  }
}

pub fn distance(a: Hex, b: Hex) -> int {
  use std::num::abs;

  let Delta {dx, dy, dz} = a - b;
  let mut values = [abs(dx), abs(dy), abs(dz)];
  values.sort();
  values[0]+values[1]
}

#[deriving(Eq, ToStr)]
pub enum Direction { XY, XZ, YZ, YX, ZX, ZY }

struct DirIter { next: Option<Direction> }

impl Direction {
  pub fn all() -> DirIter { DirIter { next: Some(XY) } }
}

impl Iterator<Direction> for DirIter {
  fn next(&mut self) -> Option<Direction> {
    let val = self.next;
    self.next = match val {
      None => None,
      Some(o) => match o {
        XY => Some(XZ),
        XZ => Some(YZ),
        YZ => Some(YX),
        YX => Some(ZX),
        ZX => Some(ZY),
        ZY => None
      }
    };
    val
  }
}

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

#[deriving(Eq, ToStr)]
pub struct Region { center: Hex, radius: int }

impl Region {
  pub fn contains(self, h: Hex) -> bool { distance(self.center, h) <= self.radius }
  pub fn ring(self) -> ~[Hex] {
    let sides = [(XY, YZ), (XZ, YZ), (YZ, ZX), (YX, ZY), (ZX, XY), (ZY, XZ)];
    sides.flat_map(|&(start, dir)| line(self.center + start.delta()*self.radius, dir, self.radius))
  }
}

impl Hex {
  pub fn neighbors(self) -> ~[Hex] {
    Direction::all().map(|d| self + d.delta()).collect()
  }
}

pub fn line(start: Hex, dir: Direction, dist: int) -> ~[Hex] {
  std::iter::range(1, dist).map(|d| start + dir.delta()*d).collect()
}
