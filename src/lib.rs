use std::ops::{Add,Sub,Mul};

/// A hex-grid coordinate, using cubic notation.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
pub struct Hex { pub x: i32, pub y: i32, pub z: i32 }
/// The difference between two `Hex` coordinates.
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

pub type Iter = Box<Iterator<Item=Hex> + 'static>;
pub type IterSize = Box<ExactSizeIterator<Item=Hex> + 'static>;

impl Hex {
  /// Returns the "shortest path" distance to `other`.
  ///
  /// # Examples
  ///
  /// ```
  /// use hex::{Hex, ORIGIN};
  /// assert_eq!(ORIGIN.distance_to(Hex {x:1,y:1,z:-2}), 2);
  /// ```
  pub fn distance_to(&self, other: Hex) -> u32 {
    let Delta {dx, dy, dz} = *self - other;
    let mut values = [dx.abs() as u32, dy.abs() as u32, dz.abs() as u32];
    values.sort();
    values[0]+values[1]
  }
  /// A straight line of `dist` hexes, not including this one.
  ///
  /// # Examples
  ///
  /// ```
  /// use hex::{Hex, Direction, ORIGIN};
  /// assert_eq!(ORIGIN.line(Direction::XY, 5).last().unwrap(), Hex {x:5,y:-5,z:0});
  /// ```
  pub fn line(&self, dir: Direction, dist: u32) -> IterSize {
    let h = *self;
    Box::new(
      (1..dist+1).map(move |d| h + dir.delta()*(d as i32))
    )
  }
  /// The six neighbor coordinates.
  ///
  /// # Examples
  ///
  /// ```
  /// use hex::{Hex, ORIGIN};
  /// assert!(ORIGIN.neighbors().all(|h| ORIGIN.distance_to(h) == 1));
  /// ```
  pub fn neighbors(&self) -> IterSize {
    let h = *self;
    Box::new(
      Direction::all().map(move |d| h + d.delta())
    )
  }
}

/// The six cardinal directions of movement, named as `<increment coordinate><decrement coordinate>`.
#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug)]
pub enum Direction { XY, XZ, YZ, YX, ZX, ZY }

impl Direction {
  // TODO: implement all() in terms of Range / Step?
  /// All `Direction`s, in convenient `Iterator` format.
  pub fn all() -> std::slice::Iter<'static, Direction> { DIRECTIONS.iter() }
  /// Returns the `Delta` corresponding to a single move in this `Direction`.
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

/// A hexagonal region of given center and radius.
///
/// A zero-radius region is a single hex.
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
  /// Whether the given `Hex` is contained in this region.
  pub fn contains(&self, h: Hex) -> bool { self.center.distance_to(h) <= self.radius }
  /// The outer ring of `Hex`es of this region.
  pub fn ring(&self) -> Iter {
    let copy = *self;
    Box::new(
      RING_SIDES.iter().flat_map(move |&(start, dir)| (copy.center + start.delta()*(copy.radius as i32)).line(dir, copy.radius))
    )
  }
  /// All `Hex`es contained in this region.
  pub fn area(&self) -> Iter {
    let copy = *self;
    Box::new(
      (0..copy.radius+1).flat_map(move |r| {
        let tmp = Region {center: copy.center, radius: r};
        tmp.ring()
      })
    )
  }
}

#[cfg(test)]
mod tests {

extern crate quickcheck;
// If this (or the corresponding cargo [dependencies] line) is omitted, test
// compilation barfs with 'source trait is private' for rand::Rng methods on
// quickcheck::Gen.
extern crate rand;

use super::Hex;
use super::Direction;

use std::collections::HashSet;

use self::quickcheck::quickcheck;

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

#[derive(Clone, Debug)]
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

#[test]
fn line_length() {
  fn prop(p: (Hex, Direction, SmallPositiveInt)) -> bool {
    let (h, d, SmallPositiveInt(i)) = p;
    h.line(d, i).len() == (i as usize)
  }
  quickcheck(prop as fn((Hex, Direction, SmallPositiveInt)) -> bool);
}

// TODO: continue porting from tests/lib.rs at line_delta

}  // mod tests
