#[cfg(test)]
extern crate quickcheck;
#[cfg(test)] #[allow(unstable)]
extern crate rand;

use std::ops::{Add,Sub,Mul};

#[derive(PartialEq, Eq, Copy, Clone, Default, Show)]
pub struct Hex { pub x: i32, pub y: i32, pub z: i32 }
#[derive(PartialEq, Eq, Copy, Clone, Default, Show)]
pub struct Delta { pub dx: i32, pub dy: i32, pub dz: i32 }

pub static ORIGIN: Hex = Hex { x: 0, y: 0, z: 0 };

impl Add<Delta> for Hex {
  type Output = Hex;

  fn add(self, Delta {dx, dy, dz}: Delta) -> Hex {
    Hex {x: self.x+dx, y: self.y+dy, z: self.z+dz}
  }
}

impl Sub for Hex {
  type Output = Delta; 

  fn sub(self, Hex {x, y, z}: Hex) -> Delta {
    Delta {dx: self.x-x, dy: self.y-y, dz: self.z-z}
  }
}

impl Mul<i32> for Delta {
  type Output = Delta;

  fn mul(self, f: i32) -> Delta {
    Delta {dx: self.dx*f, dy: self.dy*f, dz: self.dz*f}
  }
}

pub struct Iter {
  i: Box<Iterator<Item=Hex> + 'static>
}

impl Iterator for Iter {
  type Item = Hex;
  fn next(&mut self) -> Option<Hex> { self.i.next() }
  fn size_hint(&self) -> (usize, Option<usize>) { self.i.size_hint() }
}

pub struct IterSize {
  i: Box<ExactSizeIterator<Item=Hex> + 'static>
}

impl Iterator for IterSize {
  type Item = Hex;
  fn next(&mut self) -> Option<Hex> { self.i.next() }
  fn size_hint(&self) -> (usize, Option<usize>) { self.i.size_hint() }
}

impl ExactSizeIterator for IterSize {
  #[allow(unstable)]
  fn len(&self) -> usize { self.i.len() }
}

impl Hex {
  #[allow(unstable)]
  pub fn distance_to(&self, other: Hex) -> u32 {
    use std::num::SignedInt;    // for .abs()

    let Delta {dx, dy, dz} = *self - other;
    let mut values = [dx.abs() as u32, dy.abs() as u32, dz.abs() as u32];
    values.sort();
    values[0]+values[1]
  }
  pub fn line(&self, dir: Direction, dist: u32) -> Iter {
    let h = *self;
    Iter { i: Box::new(
      (1..dist+1).map(move |d| h + dir.delta()*(d as i32))
    ) }
  }
  pub fn neighbors(&self) -> IterSize {
    let h = *self;
    IterSize { i: Box::new(
      Direction::all().map(move |d| h + d.delta())
    ) }
  }
}

#[derive(PartialEq, Eq, Copy, Clone)]
pub enum Direction { XY, XZ, YZ, YX, ZX, ZY }

impl Direction {
  // TODO: implement all() in terms of Range / Step?
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

static DIRECTIONS: [Direction; 6] = [Direction::XY, Direction::XZ, Direction::YZ, Direction::YX, Direction::ZX, Direction::ZY];

#[derive(PartialEq, Eq, Copy, Clone)]
pub struct Region { center: Hex, radius: u32 }

static RING_SIDES: [(Direction, Direction); 6] =
  [(Direction::XY, Direction::YZ),
   (Direction::XZ, Direction::YX),
   (Direction::YZ, Direction::ZX),
   (Direction::YX, Direction::ZY),
   (Direction::ZX, Direction::XY),
   (Direction::ZY, Direction::XZ)];

impl Region {
  pub fn contains(&self, h: Hex) -> bool { self.center.distance_to(h) <= self.radius }
  pub fn ring(&self) -> Iter {
    let copy = *self;
    Iter { i: Box::new(
      RING_SIDES.iter().flat_map(move |&(start, dir)| (copy.center + start.delta()*(copy.radius as i32)).line(dir, copy.radius))
    ) }
  }
  pub fn area(&self) -> Iter {
    let copy = *self;
    Iter { i: Box::new(
      (0..copy.radius+1).flat_map(move |r| {
        let tmp = Region {center: copy.center, radius: r};
        tmp.ring()
      })
    ) }
  }
}

#[cfg(test)]
mod tests {

use super::Hex;

use quickcheck;
use quickcheck::quickcheck;
use rand::Rng;

impl quickcheck::Arbitrary for Hex {
  #[allow(unstable)]
  fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
    let x = g.gen_range(-1000, 1000);
    let y = g.gen_range(-1000, 1000);
    Hex {x: x, y: y, z: 0-(x+y)}
  }
  fn shrink(&self) -> Box<quickcheck::Shrinker<Self> + 'static> {
    let xy = (self.x, self.y).shrink();
    let out = xy.map(|(x, y)| Hex {x: x, y: y, z: 0-(x+y)});
    Box::new(out)
  }
}

#[test]
fn six_neighbors() {
  fn prop(h: Hex) -> bool { h.neighbors().count() == 6 }
  quickcheck(prop as fn(Hex) -> bool);
}

}
