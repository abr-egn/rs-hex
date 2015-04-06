#[cfg(test)]
extern crate quickcheck;
// If this (or the corresponding cargo [dependencies] line) is omitted, test
// compilation barfs with 'source trait is private' for rand::Rng methods on
// quickcheck::Gen.
#[cfg(test)]
extern crate rand;

use std::ops::{Add,Sub,Mul};

#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
pub struct Hex { pub x: i32, pub y: i32, pub z: i32 }
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
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
  fn len(&self) -> usize { self.i.len() }
}

impl Hex {
  pub fn distance_to(&self, other: Hex) -> u32 {
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

#[derive(PartialEq, Eq, Copy, Clone, Hash)]
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

#[derive(PartialEq, Eq, Copy, Clone, Hash)]
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
use super::Direction;

use std::collections::HashSet;

use quickcheck;
use quickcheck::quickcheck;

impl quickcheck::Arbitrary for Hex {
  fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
    let x = g.gen_range(-1000, 1000);
    let y = g.gen_range(-1000, 1000);
    Hex {x: x, y: y, z: 0-(x+y)}
  }
  fn shrink(&self) -> Box<Iterator<Item=Hex> + 'static> {
    let xy = (self.x, self.y).shrink();
    let out = xy.map(|(x, y)| Hex {x: x, y: y, z: 0-(x+y)});
    Box::new(out)
  }
}

// Every hex has six neighbors.
#[test]
fn six_neighbors() {
  fn prop(h: Hex) -> bool { h.neighbors().count() == 6 }
  quickcheck(prop as fn(Hex) -> bool);
}

// The neighbors of the neighbors of every hex include the original hex.
#[test]
fn transitive_neighbors() {
  fn prop(h: Hex) -> bool {
    h.neighbors().all(|n| n.neighbors().any(|nn| nn == h))
  }
  quickcheck(prop as fn(Hex) -> bool);
}

// The neighbors of the neighbors of every hex have two hexes in common with
// the original set of neighbors.
#[test]
fn overlap_neighbors() {
  fn prop(h: Hex) -> bool {
    let ns: HashSet<Hex> = h.neighbors().collect();
    ns.iter().all(|n| {
      let nns: HashSet<Hex> = n.neighbors().collect();
      ns.intersection(&nns).count() == 2
    })
  }
  quickcheck(prop as fn(Hex) -> bool);
}

// The distance from a hex to its neighbors is 1.
#[test]
fn neighbor_distance() {
  fn prop(h: Hex) -> bool { h.neighbors().all(|n| h.distance_to(n) == 1) }
  quickcheck(prop as fn(Hex) -> bool);
}

impl quickcheck::Arbitrary for Direction {
  // Should be able to derive(Rand) for Direction and just do { g.gen() } for
  // this, but derive(Rand) is deprecated in favor of a derive_rand macro in
  // an external crate (wtf?).
  fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
    let n = g.gen_range(0, 6);
    Direction::all().nth(n).unwrap().clone()
  }
}

#[derive(Clone)]
struct SmallPositiveInt(u32);

impl quickcheck::Arbitrary for SmallPositiveInt {
  fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
    SmallPositiveInt(g.gen_range(1, 1000))
  }
  fn shrink(&self) -> Box<Iterator<Item=SmallPositiveInt> + 'static> {
    match *self {
      SmallPositiveInt(1) => quickcheck::empty_shrinker(),
      SmallPositiveInt(n) => quickcheck::single_shrinker(SmallPositiveInt(n/2))
    }
  }
}

// TODO: continue porting from tests/lib.rs at line_length

}
