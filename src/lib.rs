#[cfg(test)]
mod test_util;

pub mod gosper;

use std::cmp;
use std::ops::{Add,Sub,Mul};

/// A hex-grid coordinate, using cubic notation.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
pub struct Hex<T = i32> { pub x: T, pub y: T }

/// The difference between two `Hex` coordinates.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash)]
pub struct Delta<T = i32> { pub dx: T, pub dy: T }

pub static ORIGIN: Hex = Hex {x: 0, y: 0};

impl<D, H: Add<D>> Add<Delta<D>> for Hex<H> {
    type Output = Hex<<H as Add<D>>::Output>;

    fn add(self, Delta {dx, dy}: Delta<D>) -> Self::Output {
        Hex {x: self.x+dx, y: self.y+dy}
    }
}

impl<H, D: Add<H>> Add<Hex<H>> for Delta<D> {
    type Output = Hex<<D as Add<H>>::Output>;

    fn add(self, Hex {x, y}: Hex<H>) -> Self::Output {
        Hex {x: self.dx+x, y: self.dy+y}
    }
}

impl<R, L: Add<R>> Add<Delta<R>> for Delta<L> {
    type Output = Delta<<L as Add<R>>::Output>;

    fn add(self, Delta {dx, dy}: Delta<R>) -> Self::Output {
        Delta {dx: self.dx+dx, dy: self.dy+dy}
    }
}

impl<R, L: Sub<R>> Sub<Hex<R>> for Hex<L> {
    type Output = Delta<<L as Sub<R>>::Output>;

    fn sub(self, Hex {x, y}: Hex<R>) -> Self::Output {
        Delta {dx: self.x-x, dy: self.y-y}
    }
}

impl<S: Clone, D: Mul<S>> Mul<S> for Delta<D> {
    type Output = Delta<<D as Mul<S>>::Output>;

    fn mul(self, f: S) -> Self::Output {
        Delta {dx: self.dx*f.clone(), dy: self.dy*f}
    }
}

/* Conflicts with the other Mul because Delta<D> and S could overlap
impl<S: Clone, D: Mul<S>> Mul<Delta<D>> for S {
    type Output = Delta<<D as Mul<S>>::Output>;

    fn mul(self, Delta {dx, dy}: Delta<D>) -> Self::Output {
        Delta {dx: self.clone()*dx, dy: self*dy}
    }
}
*/

impl<T> Hex<T> {
    pub fn x(self) -> T { self.x }
    pub fn y(self) -> T { self.y }
    pub fn z<O>(self) -> <O as std::ops::Neg>::Output
        where T: Add<Output=O>,
              O: std::ops::Neg,
    { - (self.x + self.y) }
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
    pub fn distance_to<R>(self, other: Hex<R>) -> u32
        where Self: Sub<Hex<R>>,
    { (self - other).length() }
}

impl Hex {
    /// A sequence of hexes along the given direction, not including `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::{Hex, Direction, ORIGIN};
    /// assert_eq!(ORIGIN.ray(Direction::XY).nth(4).unwrap(), Hex {x:5,y:-5});
    /// ```
    pub fn ray(&self, dir: Direction) -> impl Iterator<Item=Hex> {
        let h = *self;
        (1..).map(move |d| h + dir.delta()*d)
    }
    /// The six neighbor coordinates.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::{Hex, ORIGIN};
    /// assert!(ORIGIN.neighbors().all(|h| ORIGIN.distance_to(h) == 1));
    /// ```
    pub fn neighbors(&self) -> impl ExactSizeIterator<Item=Hex> {
        let h = *self;
        Box::new(
            Direction::all().map(move |d| h + d.delta())
            )
    }
    /// A straight line to the target hex, not including `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::{Hex, ORIGIN};
    /// let h = Hex{x:1,y:2};
    /// assert_eq!(ORIGIN.line_to(h).last().unwrap(), h);
    /// ```
    pub fn line_to(&self, other: Hex) -> impl Iterator<Item=Hex> {
        let copy = *self;
        let n = copy.distance_to(other);
        let step = 1.0 / cmp::max(n, 1) as f32;
        (0..n+1).map(move |i| hex_lerp(copy, other, step*(i as f32)).round())
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
    /// Direction-aligned path from the origin to this hex, as (direction, number of steps).
    pub fn path(&self) -> Vec<(Direction, u32)> {
        let mut coords = [(Axis::X, self.x()), (Axis::Y, self.y()), (Axis::Z, self.z())];
        coords.sort_by(|&(_, a), &(_, b)| a.abs().cmp(&b.abs()));
        let (least, minor, major) = (coords[0], coords[1], coords[2]);
        let align_dir = if least.1 < 0 { Axis::direction(major.0, least.0) } else { Axis::direction(least.0, major.0) };
        let align_mag = least.1.abs() as u32;
        let axis_dir = if minor.1 < 0 { Axis::direction(major.0, minor.0) } else { Axis::direction(minor.0, major.0) };
        let axis_mag = minor.1.abs() as u32;
        vec![(axis_dir.unwrap(), axis_mag), (align_dir.unwrap(), align_mag)]
    }
    /// A hexagonal area of cells of given radius centered on this hex.
    ///
    /// A zero-radius area is a single hex.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::ORIGIN;
    /// assert_eq!(ORIGIN.area(0).count(), 1);
    /// assert_eq!(ORIGIN.area(1).count(), 7);
    /// ```
    pub fn area(&self, radius: u32) -> impl Iterator<Item=Hex> {
        let irad = radius as i32;
        let copy = *self;
        (-irad..irad+1).flat_map(move |q| {
            let r1 = cmp::max(-irad, -q - irad);
            let r2 = cmp::min(irad, -q + irad);
            (r1..r2+1).map(move |r| Hex{x:copy.x+q, y:copy.y+r})
        })
    }
    /// A hexagonal ring of cells of given radius centered on this hex.
    ///
    /// A zero-radius ring is a single hex.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::ORIGIN;
    /// assert_eq!(ORIGIN.ring(0).count(), 1);
    /// assert_eq!(ORIGIN.ring(1).count(), 6);
    /// ```
    pub fn ring(&self, radius: u32) -> Box<dyn Iterator<Item=Hex>> {
        let copy = *self;
        if radius == 0 {
            return Box::new(Some(copy).into_iter());
        }
        Box::new(RING_SIDES.iter()
            .flat_map(move |&(start, dir)| {
                (copy + start.delta()*(radius as i32))
                    .ray(dir)
                    .take(radius as usize)
            }))
    }
}

impl<T> Delta<T> {
    pub fn dx(self) -> T { self.dx }
    pub fn dy(self) -> T { self.dy }
    pub fn dz<O>(self) -> <O as std::ops::Neg>::Output
        where T: Add<Output=O>,
              O: std::ops::Neg,
    { - (self.dx + self.dy) }
    /// The length of this translation, i.e. the number of hexes a line of this length would have.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::{Delta};
    /// assert_eq!(Delta{dx:0,dy:0}.length(), 0);
    /// assert_eq!(Delta{dx:1,dy:2}.length(), 3);
    /// ```
    pub fn length(self) -> u32 { ((self.dx().abs() + self.dy().abs() + self.dz().abs()) / 2) as u32 }
}

impl Delta {
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

// DIRECTIONS and RING_SIDES are supporting datastructures for Hex::ring

static DIRECTIONS: [Direction; 6] = [Direction::XY, Direction::XZ, Direction::YZ, Direction::YX, Direction::ZX, Direction::ZY];

static RING_SIDES: [(Direction, Direction); 6] =
    [(Direction::XY, Direction::YZ),
     (Direction::XZ, Direction::YX),
     (Direction::YZ, Direction::ZX),
     (Direction::YX, Direction::ZY),
     (Direction::ZX, Direction::XY),
     (Direction::ZY, Direction::XZ)];

/// A parallelogram defined by two axes, starting at the origin.
pub fn parallelogram(a1: Axis, a2: Axis,
                     a1_size: u32, a2_size: u32) -> impl Iterator<Item=Hex> {
    assert!(a1 != a2);
    (0..a1_size as i32).flat_map(
        move |a1_val| (0..a2_size as i32).map(
            move |a2_val| {
                let x;
                let y;
                match (a1, a2) {
                    (Axis::X, Axis::Y) => { x = a1_val; y = a2_val; }
                    (Axis::X, Axis::Z) => { x = a1_val; y = -x - a2_val; }
                    (Axis::Y, Axis::X) => { y = a1_val; x = a2_val; }
                    (Axis::Y, Axis::Z) => { y = a1_val; x = -y - a2_val; }
                    (Axis::Z, Axis::X) => { x = a2_val; y = -x - a1_val; }
                    (Axis::Z, Axis::Y) => { y = a2_val; x = -y - a1_val; }
                    _ => panic!("Invalid axis combination")
                }
                Hex {x: x, y: y}
            }
        )
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

#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug)]
pub enum Axis { X, Y, Z }

impl Axis {
    pub fn direction(a: Axis, b: Axis) -> Option<Direction> {
        match (a, b) {
            (Axis::X, Axis::Y)  => Some(Direction::XY),
            (Axis::X, Axis::Z)  => Some(Direction::XZ),
            (Axis::Y, Axis::Z)  => Some(Direction::YZ),
            (Axis::Y, Axis::X)  => Some(Direction::YX),
            (Axis::Z, Axis::X)  => Some(Direction::ZX),
            (Axis::Z, Axis::Y)  => Some(Direction::ZY),
            _       => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Hex, Delta, Direction, Rotation, Axis, ORIGIN};
    use super::test_util::{SmallPositiveInt, SmallNonNegativeInt};

    use std::collections::HashSet;
    use std::collections::HashMap;

    use quickcheck::quickcheck;

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

    // The distance from the origin is the sum of the path step counts.
    #[test]
    fn line_path() {
        fn prop(h: Hex) -> Result<bool, String> {
            let dist = ORIGIN.distance_to(h);
            let path = h.path();
            let path_len = path.iter().fold(0, |n, &(_, i)| n+i);
            if dist == path_len { Ok(true) } else {
                Err(format!("dist = {:?} path_len = {:?} path = {:?}", dist, path_len, path))
            }
        }
        quickcheck(prop as fn(Hex) -> Result<bool, String>);
    }

    // The difference between subsequent hexes in a ray is the directional delta.
    #[test]
    fn ray_delta() {
        fn prop(h: Hex, d: Direction, i: SmallPositiveInt) -> bool {
            let mut prev = h;
            h.ray(d).take(i.0 as usize).all(|pt| {
                let cmp = (pt - prev) == d.delta();
                prev = pt;
                cmp
            })
        }
        quickcheck(prop as fn(Hex, Direction, SmallPositiveInt) -> bool);
    }

    // Rotating a hex six times yields the original hex.
    #[test]
    fn rotate_identity() {
        fn prop(h1: Hex, h2: Hex, r: Rotation) -> bool {
            let mut h = h1;
            for _ in 0..6 {
                h = h.rotate_around(h2, r);
            }
            h == h1
        }
        quickcheck(prop as fn(Hex, Hex, Rotation) -> bool);
    }

    // Rotating a delta six times yields the original delta.
    #[test]
    fn rotate_delta_identity() {
        fn prop(d0: Delta, r: Rotation) -> bool {
            let mut d = d0;
            for _ in 0..6 {
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

    // Number of hexes in a hex ring matches the expected function of radius.
    #[test]
    fn ring_len() {
        fn expected(r: u32) -> usize {
            match r {
                0 => 1,
                x => (x as usize)*6,
            }
        }
        fn prop(h: Hex, r: SmallNonNegativeInt) -> bool { h.ring(r.0).count() == expected(r.0) }
        quickcheck(prop as fn(Hex, SmallNonNegativeInt) -> bool);
    }

    // The distance from hexes in a hex ring to the origin is the radius of the ring.
    #[test]
    fn ring_distance() {
        fn prop(h: Hex, r: SmallNonNegativeInt) -> bool {
            h.ring(r.0).all(|h2| { h.distance_to(h2) == r.0 })
        }
        quickcheck(prop as fn(Hex, SmallNonNegativeInt) -> bool);
    }

    // Number of hexes in a hex area matches the expected function of radius.
    #[test]
    fn area_len() {
        fn expected(r: u32) -> usize { (3*r.pow(2) + 3*r + 1) as usize }
        fn prop(h: Hex, r: SmallNonNegativeInt) -> bool { h.area(r.0).count() == expected(r.0) }
        quickcheck(prop as fn(Hex, SmallNonNegativeInt) -> bool);
    }

    // The distance from hexes in a hex area to the origin is <= the radius of the area.
    #[test]
    fn area_distance() {
        fn prop(h: Hex, r: SmallNonNegativeInt) -> bool { h.area(r.0).all(|h2| h.distance_to(h2) <= r.0) }
        quickcheck(prop as fn(Hex, SmallNonNegativeInt) -> bool);
    }

}  // mod tests
