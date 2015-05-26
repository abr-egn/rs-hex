use std::ops::{Add,Sub,Mul};

/// A hex-grid coordinate, using cubic notation.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
pub struct Hex { pub x: i32, pub y: i32 }
impl Hex {
  pub fn x(&self) -> i32 { self.x }
  pub fn y(&self) -> i32 { self.y }
  pub fn z(&self) -> i32 { 0 - (self.x + self.y) }
}

/// The difference between two `Hex` coordinates.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
pub struct Delta { pub dx: i32, pub dy: i32 }
impl Delta {
  pub fn dx(&self) -> i32 { self.dx }
  pub fn dy(&self) -> i32 { self.dy }
  pub fn dz(&self) -> i32 { 0 - (self.dx + self.dy) }
}

pub static ORIGIN: Hex = Hex {x: 0, y: 0};

impl Add<Delta> for Hex {
  type Output = Hex;

  fn add(self, Delta {dx, dy}: Delta) -> Hex {
    Hex {x: self.x+dx, y: self.y+dy}
  }
}

impl Sub for Hex {
  type Output = Delta; 

  fn sub(self, Hex {x, y}: Hex) -> Delta {
    Delta {dx: self.x-x, dy: self.y-y}
  }
}

impl Mul<i32> for Delta {
  type Output = Delta;

  fn mul(self, f: i32) -> Delta {
    Delta {dx: self.dx*f, dy: self.dy*f}
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
  /// assert_eq!(ORIGIN.distance_to(Hex {x:1,y:1}), 2);
  /// ```
  pub fn distance_to(&self, other: Hex) -> u32 {
    let d = *self - other;
    let mut values = [d.dx().abs() as u32, d.dy().abs() as u32, d.dz().abs() as u32];
    values.sort();
    values[0]+values[1]
  }
  /// A straight line of `dist` hexes, not including this one.
  ///
  /// # Examples
  ///
  /// ```
  /// use hex::{Hex, Direction, ORIGIN};
  /// assert_eq!(ORIGIN.line(Direction::XY, 5).last().unwrap(), Hex {x:5,y:-5});
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
      Direction::XY => Delta {dx: 1, dy:-1},
      Direction::XZ => Delta {dx: 1, dy: 0},
      Direction::YZ => Delta {dx: 0, dy: 1},
      Direction::YX => Delta {dx:-1, dy: 1},
      Direction::ZX => Delta {dx:-1, dy: 0},
      Direction::ZY => Delta {dx: 0, dy:-1},
    }
  }
}

static DIRECTIONS: [Direction; 6] = [Direction::XY, Direction::XZ, Direction::YZ, Direction::YX, Direction::ZX, Direction::ZY];

/// A hexagonal region of given center and radius.
///
/// A zero-radius region is a single hex.
#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug)]
pub struct Region { pub center: Hex, pub radius: u32 }

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
  ///
  /// # Examples
  ///
  /// ```
  /// use hex::{Region, ORIGIN};
  /// assert_eq!(Region{center:ORIGIN,radius:0}.ring().count(), 1);
  /// assert_eq!(Region{center:ORIGIN,radius:1}.ring().count(), 6);
  /// ```
  pub fn ring(&self) -> Iter {
    let copy = *self;
    if self.radius == 0 {
      // TODO: better idiom for singleton iterator
      return Box::new((0..1).map(move |_| copy.center));
    }
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
extern crate rand;

use super::Hex;
use super::Direction;
use super::Region;

use std::collections::HashSet;

use self::quickcheck::quickcheck;

impl quickcheck::Arbitrary for Hex {
  fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
    let x = g.gen_range(-1000, 1000);
    let y = g.gen_range(-1000, 1000);
    Hex {x: x, y: y}
  }
  fn shrink(&self) -> Box<Iterator<Item=Hex> + 'static> {
    let xy = (self.x, self.y).shrink();
    let out = xy.map(|(x, y)| Hex {x: x, y: y});
    Box::new(out)
  }
}

// A hex has six neighbors.
#[test]
fn six_neighbors() {
  fn prop(h: Hex) -> bool { h.neighbors().count() == 6 }
  quickcheck(prop as fn(Hex) -> bool);
}

// The neighbors of the neighbors of a hex include that hex.
#[test]
fn transitive_neighbors() {
  fn prop(h: Hex) -> bool {
    h.neighbors().all(|n| n.neighbors().any(|nn| nn == h))
  }
  quickcheck(prop as fn(Hex) -> bool);
}

// The neighbors of the neighbors of a hex have two hexes in common with
// the neighbors of that hex.
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

// The number of hexes generated by a line iterator is the given length.
#[test]
fn line_length() {
  fn prop(p: (Hex, Direction, SmallPositiveInt)) -> bool {
    let (h, d, SmallPositiveInt(i)) = p;
    h.line(d, i).len() == (i as usize)
  }
  quickcheck(prop as fn((Hex, Direction, SmallPositiveInt)) -> bool);
}

// The difference between subsequent hexes in a line is always the directional delta.
#[test]
fn line_delta() {
  fn prop(p: (Hex, Direction, SmallPositiveInt)) -> bool {
    let (h, d, SmallPositiveInt(i)) = p;
    let mut prev = h;
    h.line(d, i).all(|pt| {
      let cmp = (pt - prev) == d.delta();
      prev = pt;
      cmp
    })
  }
  quickcheck(prop as fn((Hex, Direction, SmallPositiveInt)) -> bool);
}

#[derive(Clone, Debug)]
struct SmallNonNegativeInt(u32);

impl quickcheck::Arbitrary for SmallNonNegativeInt {
  fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
    SmallNonNegativeInt(g.gen_range(0, 1000))
  }
  fn shrink(&self) -> Box<Iterator<Item=SmallNonNegativeInt> + 'static> {
    match *self {
      SmallNonNegativeInt(0) => quickcheck::empty_shrinker(),
      SmallNonNegativeInt(1) => quickcheck::single_shrinker(SmallNonNegativeInt(0)),
      SmallNonNegativeInt(n) => quickcheck::single_shrinker(SmallNonNegativeInt(n/2)),
    }
  }
}

impl quickcheck::Arbitrary for Region {
  fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
    let center: Hex = quickcheck::Arbitrary::arbitrary(g);
    let SmallNonNegativeInt(radius)  = quickcheck::Arbitrary::arbitrary(g);
    Region { center: center, radius: radius }
  }
  fn shrink(&self) -> Box<Iterator<Item=Region> + 'static> {
    Box::new(self.center.shrink().zip(SmallNonNegativeInt(self.radius).shrink()).map(
      |(c, SmallNonNegativeInt(r))| { Region { center: c, radius: r} }))
  }
}

// A region contains its center point.
#[test]
fn contains_center() {
  fn prop(p: Region) -> bool { p.contains(p.center) }
  quickcheck(prop as fn(Region) -> bool);
}

// A region with center P and radius P.distance_to(P') contains P'.
#[test]
fn contains_other() {
  fn prop(p1: Hex, p2: Hex) -> bool {
    let r = Region { center: p1, radius: p1.distance_to(p2) };
    r.contains(p2)
  }
  quickcheck(prop as fn(Hex, Hex) -> bool);
}

// Number of hexes in a ring matches the expected function of radius.
#[test]
fn ring_len() {
  fn expected(r: u32) -> usize {
    match r {
      0 => 1,
      x => (x as usize)*6,
    }
  }
  fn prop(r: Region) -> bool { r.ring().count() == expected(r.radius) }
  quickcheck(prop as fn(Region) -> bool);
}

// The distance from hexes in a ring to the ring center is the radius of the ring.
#[test]
fn ring_distance() {
  fn prop(r: Region) -> bool {
    r.ring().all(|h| {
      let dist = r.center.distance_to(h);
      dist == r.radius
    })
  }
  quickcheck(prop as fn(Region) -> bool);
}

}  // mod tests
