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

impl Add<Hex> for Delta {
    type Output = Hex;

    fn add(self, Hex {x, y}: Hex) -> Hex {
        Hex {x: x+self.dx, y: y+self.dy}
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

impl Mul<Delta> for i32 {
    type Output = Delta;

    fn mul(self, Delta {dx, dy}: Delta) -> Delta {
        Delta {dx: self*dx, dy: self*dy}
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
    /// A straight line to the target hex.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::{Hex, ORIGIN};
    /// let h = Hex{x:1,y:2};
    /// assert_eq!(ORIGIN.line_to(h).last().unwrap(), h);
    /// ```
    pub fn line_to(&self, other: Hex) -> Iter {
        let copy = *self;
        let n = copy.distance_to(other);
        let step = 1.0 / cmp::max(n, 1) as f32;
        Box::new((0..n+1).map(move |i| hex_lerp(copy, other, step*(i as f32)).round()))
    }
    /// Rotate this hex clockwise or counter-clockwise around another center hex.
    pub fn rotate_around(&self, center: Hex, dir: Rotation) -> Hex {
        let x = self.x() - center.x();
        let y = self.y() - center.y();
        let z = self.z() - center.z();
        match dir {
            Rotation::CW    => Hex { x: center.x - y, y: center.y - z },
            Rotation::CCW   => Hex { x: center.x - z, y: center.y - x },
        }
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
    /// Rotate this delta.
    pub fn rotate(&self, dir: Rotation) -> Delta {
        match dir {
            Rotation::CW    => Delta { dx: -self.dy(), dy: -self.dz() },
            Rotation::CCW   => Delta { dx: -self.dz(), dy: -self.dx() },
        }
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

struct FHex { x: f32, y: f32, z: f32 }

impl FHex {
    fn round(&self) -> Hex {
        let mut x = self.x.round() as i32;
        let mut y = self.y.round() as i32;
        let z = self.z.round() as i32;
        let x_diff = (x as f32 - self.x).abs();
        let y_diff = (y as f32 - self.y).abs();
        let z_diff = (z as f32 - self.z).abs();
        if x_diff > y_diff && x_diff > z_diff {
            x = -y - z;
        } else if y_diff > z_diff {
            y = -x - z;
        } else {
            // z is unused for the result
            // z = -x - y;
        }
        Hex {x: x, y: y}
    }
}

fn hex_lerp(a: Hex, b: Hex, t: f32) -> FHex {
    FHex {
        x: (a.x() as f32) + ((b.x() - a.x()) as f32)*t,
        y: (a.y() as f32) + ((b.y() - a.y()) as f32)*t,
        z: (a.z() as f32) + ((b.z() - a.z()) as f32)*t,
    }
}

/// Clockwise or counter-clockwise rotation.
#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug)]
pub enum Rotation { CW, CCW }

#[cfg(test)]
mod tests {

    extern crate quickcheck;
    extern crate rand;

    use super::{Hex, Delta, Direction, Rotation, hex_ring, hex_area, ORIGIN};

    use std::collections::HashSet;
    use std::collections::HashMap;
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

    // Distance is not negative.
    #[test]
    fn non_negative_distance() {
        fn prop(h1: Hex, h2: Hex) -> bool { h1.distance_to(h2) >= 0 }
        quickcheck(prop as fn(Hex, Hex) -> bool);
    }

    // The distance from a hex to its neighbors is 1.
    #[test]
    fn neighbor_distance() {
        fn prop(h: Hex) -> bool { h.neighbors().all(|n| h.distance_to(n) == 1) }
        quickcheck(prop as fn(Hex) -> bool);
    }

    // Last hex in a line is the target hex.
    #[test]
    fn line_end() {
        fn prop(h1: Hex, h2: Hex) -> bool { h1.line_to(h2).last().unwrap() == h2 }
        quickcheck(prop as fn(Hex, Hex) -> bool);
    }

    // The distance between sequential hexes in a line is 1.
    #[test]
    fn line_dist() {
        fn prop(h1: Hex, h2: Hex) -> bool {
            let mut prev = h1;
            h1.line_to(h2).skip(1).all(|h| {
                let r = (h - prev).length() == 1;
                prev = h;
                r
            })
        }
        quickcheck(prop as fn(Hex, Hex) -> bool);
    }

    #[derive(PartialEq, Eq, Copy, Clone, Hash, Debug)]
    enum Axis { X, Y, Z }

    // At least one axis is consistently incremented/decremented on each line step.
    #[test]
    fn line_steps() {
        fn prop(h1: Hex, h2: Hex) -> bool {
            let mut updates = HashMap::new();
            {
                let mut update = |a: Axis, d: i32| {
                    if !updates.contains_key(&a) {
                        updates.insert(a, d);
                    } else if *updates.get(&a).unwrap() != d {
                        updates.remove(&a);
                    }
                };
                let mut prev = h1;
                for h in h1.line_to(h2).skip(1) {
                    let d = h - prev;
                    prev = h;
                    update(Axis::X, d.dx());
                    update(Axis::Y, d.dy());
                    update(Axis::Z, d.dz());
                }
            }
            !updates.is_empty()
        }
        quickcheck(prop as fn(Hex, Hex) -> bool);
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
        fn prop(h: Hex, d: Direction, i: SmallPositiveInt) -> bool {
            let mut prev = h;
            h.axis(d).skip(1).take(*i as usize).all(|pt| {
                let cmp = (pt - prev) == d.delta();
                prev = pt;
                cmp
            })
        }
        quickcheck(prop as fn(Hex, Direction, SmallPositiveInt) -> bool);
    }

    impl quickcheck::Arbitrary for Rotation {
        fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
            match g.gen_range(0, 2) {
                0 => Rotation::CW,
                1 => Rotation::CCW,
                _ => panic!("Invalid arbitrary rotation"),
            }
        }
    }

    // Rotating a hex six times yields the original hex.
    #[test]
    fn rotate_identity() {
        fn prop(h1: Hex, h2: Hex, r: Rotation) -> bool {
            let mut h = h1;
            for _ in (0..6) {
                h = h.rotate_around(h2, r);
            }
            h == h1
        }
        quickcheck(prop as fn(Hex, Hex, Rotation) -> bool);
    }

    impl quickcheck::Arbitrary for Delta {
        fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
            let Hex {x, y} = quickcheck::Arbitrary::arbitrary(g);
            Delta {dx: x, dy: y}
        }
        fn shrink(&self) -> Box<Iterator<Item=Delta> + 'static> {
            Box::new(Hex {x: self.dx, y: self.dy}.shrink().map(|Hex {x, y}| Delta {dx: x, dy: y}))
        }
    }

    // Rotating a delta six times yields the original delta.
    #[test]
    fn rotate_delta_identity() {
        fn prop(d0: Delta, r: Rotation) -> bool {
            let mut d = d0;
            for _ in (0..6) {
                d = d.rotate(r);
            }
            d == d0
        }
        quickcheck(prop as fn(Delta, Rotation) -> bool);
    }

    // Rotating a hex is the same as rotating a delta and adding to the center.
    #[test]
    fn rotate_by_delta() {
        fn prop(h1: Hex, h2: Hex, r: Rotation) -> Result<bool, String> {
            let r1 = h1.rotate_around(h2, r);
            let r2 = (h1 - h2).rotate(r) + h2;
            if r1 == r2 { Ok(true) } else { Err(format!("r1 = {:?}, r2 = {:?}", r1, r2)) }
        }
        quickcheck(prop as fn(Hex, Hex, Rotation) -> Result<bool, String>);
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

    // Number of hexes in a hex ring matches the expected function of radius.
    #[test]
    fn hex_ring_len() {
        fn expected(r: i32) -> usize {
            match r {
                0 => 1,
                x => (x as usize)*6,
            }
        }
        fn prop(r: SmallNonNegativeInt) -> bool { hex_ring(*r).count() == expected(*r) }
        quickcheck(prop as fn(SmallNonNegativeInt) -> bool);
    }

    // The distance from hexes in a hex ring to the origin is the radius of the ring.
    #[test]
    fn hex_ring_distance() {
        fn prop(r: SmallNonNegativeInt) -> bool {
            hex_ring(*r).all(|h| { ORIGIN.distance_to(h) == *r })
        }
        quickcheck(prop as fn(SmallNonNegativeInt) -> bool);
    }

    // Number of hexes in a hex area matches the expected function of radius.
    #[test]
    fn hex_area_len() {
        fn expected(r: i32) -> usize { (3*r.pow(2) + 3*r + 1) as usize }
        fn prop(r: SmallNonNegativeInt) -> bool { hex_area(*r).count() == expected(*r) }
        quickcheck(prop as fn(SmallNonNegativeInt) -> bool);
    }

    // The distance from hexes in a hex area to the origin is <= the radius of the area.
    #[test]
    fn hex_area_distance() {
        fn prop(r: SmallNonNegativeInt) -> bool { hex_area(*r).all(|h| ORIGIN.distance_to(h) <= *r) }
        quickcheck(prop as fn(SmallNonNegativeInt) -> bool);
    }

}  // mod tests
