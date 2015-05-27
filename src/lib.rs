use std::cmp;
use std::ops::{Add,Sub,Mul};

/// A hex-grid coordinate, using cubic notation.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
pub struct Hex { pub x: i32, pub y: i32 }

/// The difference between two `Hex` coordinates.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
pub struct Delta { pub dx: i32, pub dy: i32 }

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
  pub fn x(&self) -> i32 { self.x }
  pub fn y(&self) -> i32 { self.y }
  pub fn z(&self) -> i32 { 0 - (self.x + self.y) }
  /// The distance to the other hex as a straight-line path.
  ///
  /// # Examples
  ///
  /// ```
  /// use hex::{Hex, ORIGIN};
  /// assert_eq!(ORIGIN.distance_to(ORIGIN), 0);
  /// assert_eq!(ORIGIN.distance_to(Hex{x:1,y:0}), 1);
  /// assert_eq!(ORIGIN.distance_to(Hex{x:1,y:1}), 2);
  /// assert_eq!(ORIGIN.distance_to(Hex{x:1,y:2}), 3);
  /// ```
  pub fn distance_to(&self, other: Hex) -> i32 { (*self - other).length() }
  /// A sequence of hexes along the given direction, including `self`.
  ///
  /// # Examples
  ///
  /// ```
  /// use hex::{Hex, Direction, ORIGIN};
  /// assert_eq!(ORIGIN.axis(Direction::XY).nth(5).unwrap(), Hex {x:5,y:-5});
  /// ```
  pub fn axis(&self, dir: Direction) -> Iter {
    let h = *self;
    Box::new(
      (0..).map(move |d| h + dir.delta()*d)
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

impl Delta {
  pub fn dx(&self) -> i32 { self.dx }
  pub fn dy(&self) -> i32 { self.dy }
  pub fn dz(&self) -> i32 { 0 - (self.dx + self.dy) }
  /// The length of this translation, i.e. the number of hexes a line of this length would have.
  ///
  /// # Examples
  ///
  /// ```
  /// use hex::{Delta};
  /// assert_eq!(Delta{dx:0,dy:0}.length(), 0);
  /// assert_eq!(Delta{dx:1,dy:2}.length(), 3);
  /// ```
  pub fn length(&self) -> i32 { ((self.dx().abs() + self.dy().abs() + self.dz().abs()) / 2) as i32 }
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

/// A hexagonal area of cells of given radius centered on the origin.
///
/// A zero-radius area is a single hex.
///
/// # Examples
///
/// ```
/// use hex::hex_area;
/// assert_eq!(hex_area(0).count(), 1);
/// assert_eq!(hex_area(1).count(), 7);
/// ```
pub fn hex_area(radius: i32) -> Iter {
  Box::new(
    (-radius..radius+1).flat_map(move |q| {
      let r1 = cmp::max(-radius, -q - radius);
      let r2 = cmp::min(radius, -q + radius);
      (r1..r2+1).map(move |r| Hex{x:q, y:r})
    })
  )
}

static RING_SIDES: [(Direction, Direction); 6] =
  [(Direction::XY, Direction::YZ),
   (Direction::XZ, Direction::YX),
   (Direction::YZ, Direction::ZX),
   (Direction::YX, Direction::ZY),
   (Direction::ZX, Direction::XY),
   (Direction::ZY, Direction::XZ)];

/// A hexagonal ring of cells of given radius centered on the origin.
///
/// A zero-radius ring is a single hex.
///
/// # Examples
///
/// ```
/// use hex::hex_ring;
/// assert_eq!(hex_ring(0).count(), 1);
/// assert_eq!(hex_ring(1).count(), 6);
/// ```
pub fn hex_ring(radius: i32) -> Iter {
  if radius == 0 {
    return Box::new(Some(ORIGIN).into_iter());
  }
  Box::new(
    RING_SIDES.iter()
      .flat_map(move |&(start, dir)|
        (ORIGIN + start.delta()*radius)
          .axis(dir)
          .skip(1)
          .take(radius as usize))
  )
}

#[cfg(test)]
mod tests {

extern crate quickcheck;
extern crate rand;

use super::{Hex, Direction, hex_ring, ORIGIN};

use std::collections::HashSet;
use std::ops::Deref;

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

// The number of moves from a hex to its neighbors is 1.
#[test]
fn neighbor_moves() {
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
struct SmallPositiveInt(i32);

impl Deref for SmallPositiveInt {
  type Target = i32;
  fn deref<'a>(&'a self) -> &'a i32 {
    let SmallPositiveInt(ref val) = *self;
    val
  }
}

impl quickcheck::Arbitrary for SmallPositiveInt {
  fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
    SmallPositiveInt(g.gen_range(1, 1000))
  }
  fn shrink(&self) -> Box<Iterator<Item=SmallPositiveInt> + 'static> {
    match **self {
      1 => quickcheck::empty_shrinker(),
      n => quickcheck::single_shrinker(SmallPositiveInt(n/2))
    }
  }
}

// The difference between subsequent hexes in an axis is the directional delta.
#[test]
fn line_delta() {
  fn prop((h, d, i): (Hex, Direction, SmallPositiveInt)) -> bool {
    let mut prev = h;
    h.axis(d).skip(1).take(*i as usize).all(|pt| {
      let cmp = (pt - prev) == d.delta();
      prev = pt;
      cmp
    })
  }
  quickcheck(prop as fn((Hex, Direction, SmallPositiveInt)) -> bool);
}

#[derive(Clone, Debug)]
struct SmallNonNegativeInt(i32);

impl Deref for SmallNonNegativeInt {
  type Target = i32;
  fn deref<'a>(&'a self) -> &'a i32 {
    let SmallNonNegativeInt(ref val) = *self;
    val
  }
}

impl quickcheck::Arbitrary for SmallNonNegativeInt {
  fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
    SmallNonNegativeInt(g.gen_range(0, 1000))
  }
  fn shrink(&self) -> Box<Iterator<Item=SmallNonNegativeInt> + 'static> {
    match **self {
      0 => quickcheck::empty_shrinker(),
      1 => quickcheck::single_shrinker(SmallNonNegativeInt(0)),
      n => quickcheck::single_shrinker(SmallNonNegativeInt(n/2)),
    }
  }
}

// Number of hexes in a ring matches the expected function of radius.
#[test]
fn ring_len() {
  fn expected(r: i32) -> usize {
    match r {
      0 => 1,
      x => (x as usize)*6,
    }
  }
  fn prop(r: SmallNonNegativeInt) -> bool { hex_ring(*r).count() == expected(*r) }
  quickcheck(prop as fn(SmallNonNegativeInt) -> bool);
}

// The number of moves from hexes in a ring to the origin is the radius of the ring.
#[test]
fn ring_moves() {
  fn prop(r: SmallNonNegativeInt) -> bool {
    hex_ring(*r).all(|h| { ORIGIN.distance_to(h) == *r })
  }
  quickcheck(prop as fn(SmallNonNegativeInt) -> bool);
}

}  // mod tests
