#[cfg(test)]
mod test_util;

pub mod gosper;

use std::{
    cmp,
    ops::{Add,Sub,Mul},
};
use num_iter;
use num_traits;
use serde::{Serialize,Deserialize};

/// A hex-grid coordinate, using cubic notation.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash, Serialize, Deserialize)]
pub struct Hex<T = i32> { pub x: T, pub y: T }

/// The difference between two `Hex` coordinates.
#[derive(PartialEq, Eq, Copy, Clone, Default, Debug, Hash, Serialize, Deserialize)]
pub struct Delta<T = i32> { pub dx: T, pub dy: T }

pub static ORIGIN: Hex = Hex {x: 0, y: 0};

// ToPrimitive is required for num_iter
pub trait HexCoord: Clone + Ord + num_traits::Num + num_traits::Signed + num_traits::ToPrimitive { }

impl<T> HexCoord for T where T: Clone + Ord + num_traits::Num + num_traits::Signed + num_traits::ToPrimitive { }

impl<C: HexCoord> Add<Delta<C>> for Hex<C> {
    type Output = Self;

    fn add(self, Delta {dx, dy}: Delta<C>) -> Self::Output {
        Hex {x: self.x+dx, y: self.y+dy}
    }
}

impl<C: HexCoord> Add<Hex<C>> for Delta<C> {
    type Output = Hex<C>;

    fn add(self, Hex {x, y}: Hex<C>) -> Self::Output {
        Hex {x: self.dx+x, y: self.dy+y}
    }
}

impl<C: HexCoord> Add<Delta<C>> for Delta<C> {
    type Output = Self;

    fn add(self, Delta {dx, dy}: Delta<C>) -> Self::Output {
        Delta {dx: self.dx+dx, dy: self.dy+dy}
    }
}

impl<C: HexCoord> Sub<Hex<C>> for Hex<C> {
    type Output = Delta<C>;

    fn sub(self, Hex {x, y}: Hex<C>) -> Self::Output {
        Delta {dx: self.x-x, dy: self.y-y}
    }
}

impl<C: HexCoord> Sub<Delta<C>> for Hex<C> {
    type Output = Hex<C>;

    fn sub(self, Delta {dx, dy}: Delta<C>) -> Self::Output {
        Hex {x: self.x-dx, y: self.y-dy}
    }
}

impl<C: HexCoord> Mul<C> for Delta<C> {
    type Output = Self;

    fn mul(self, f: C) -> Self::Output {
        Delta {dx: self.dx*f.clone(), dy: self.dy*f}
    }
}

/* Conflicts with the other Mul because Delta<D> and S could overlap
impl<C: HexCoord + Clone> Mul<Delta<C>> for C {
    type Output = Self;

    fn mul(self, Delta {dx, dy}: Delta<C>) -> Self::Output {
        Delta {dx: self.clone()*dx, dy: self*dy}
    }
}
*/

impl<C: HexCoord> Hex<C> {
    pub fn x(&self) -> C { self.x.clone() }
    pub fn y(&self) -> C { self.y.clone() }
    pub fn z(&self) -> C { - (self.x() + self.y()) }
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
    pub fn distance_to(&self, other: Hex<C>) -> C { (self.clone() - other).length() }
    /// A sequence of hexes along the given direction, including `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::{Hex, Direction, ORIGIN};
    /// assert_eq!(ORIGIN.ray(Direction::XY, 6).nth(5).unwrap(), Hex {x:5,y:-5});
    /// ```
    pub fn ray(&self, dir: Direction, size: C) -> impl Iterator<Item=Hex<C>>
    {
        let h = self.clone();
        num_iter::range(num_traits::zero(), size)
            .map(move |d| h.clone() + dir.delta()*d)
    }
    /// The six neighbor coordinates.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::{Hex, ORIGIN};
    /// assert!(ORIGIN.neighbors().all(|h| ORIGIN.distance_to(h) == 1));
    /// ```
    pub fn neighbors(&self) -> impl ExactSizeIterator<Item=Hex<C>> {
        let h = self.clone();
        Direction::all().map(move |d| h.clone() + d.delta())
    }
    /// Rotate this hex clockwise or counter-clockwise around another center hex.
    pub fn rotate_around(&self, center: Hex<C>, dir: Rotation) -> Hex<C> {
        let x = self.x() - center.x();
        let y = self.y() - center.y();
        let z = self.z() - center.z();
        match dir {
            Rotation::CW    => Hex { x: center.x - y, y: center.y - z },
            Rotation::CCW   => Hex { x: center.x - z, y: center.y - x },
        }
    }
    /// Direction-aligned path from the origin to this hex, as (direction, number of steps).
    pub fn path(&self) -> Vec<(Direction, C)> {
        let mut coords = [(Axis::X, self.x()), (Axis::Y, self.y()), (Axis::Z, self.z())];
        coords.sort_by(|&(_, ref a), &(_, ref b)| a.abs().cmp(&b.abs()));
        let (least, minor, major) = (coords[0].clone(), coords[1].clone(), coords[2].clone());
        let align_dir = if least.1 < num_traits::zero() { Axis::direction(major.0, least.0) } else { Axis::direction(least.0, major.0) };
        let align_mag = least.1.abs();
        let axis_dir = if minor.1 < num_traits::zero() { Axis::direction(major.0, minor.0) } else { Axis::direction(minor.0, major.0) };
        let axis_mag = minor.1.abs();
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
    pub fn area(&self, radius: C) -> impl Iterator<Item=Hex<C>>
    {
        let copy = self.clone();
        num_iter::range_inclusive(-radius.clone(), radius.clone()).flat_map(move |q| {
            let r1 = cmp::max(-radius.clone(), -q.clone() - radius.clone());
            let r2 = cmp::min(radius.clone(), -q.clone() + radius.clone());
            let copy = copy.clone();
            num_iter::range_inclusive(r1, r2).map(move |r| Hex{x:copy.clone().x+q.clone(), y:copy.clone().y+r})
        })
    }
    /// A hexagonal ring of cells of given radius centered on this hex.
    ///
    /// A zero-radius ring is invalid, and will panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::ORIGIN;
    /// assert_eq!(ORIGIN.ring(1).count(), 6);
    /// ```
    pub fn ring(&self, radius: C) -> impl Iterator<Item=Hex<C>>
    {
        let copy = self.clone();
        assert!(radius != num_traits::zero());
        RING_SIDES.iter()
            .flat_map(move |&(start, dir)| {
                (copy.clone() + start.delta()*radius.clone())
                    .ray(dir, radius.clone())
            })
    }
    /// A straight line to the target hex, including `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::{Hex, ORIGIN};
    /// let h = Hex{x:1,y:2};
    /// assert_eq!(ORIGIN.line_to(h).last().unwrap(), h);
    /// assert_eq!(ORIGIN.line_to(h).count(), 4);
    /// ```
    pub fn line_to(&self, other: Hex<C>) -> impl Iterator<Item=Hex<C>>
        where C: num_traits::FromPrimitive
    {
        self.line_to_impl(other, FHex { x: 1e-6, y: 2e-6, z: -3e-6 })
    }

    pub fn line_to_alt(&self, other: Hex<C>) -> impl Iterator<Item=Hex<C>>
        where C: num_traits::FromPrimitive
    {
        self.line_to_impl(other, FHex { x: -1e-6, y: -2e-6, z: 3e-6 })
    }

    fn line_to_impl(&self, other: Hex<C>, offset: FHex) -> impl Iterator<Item=Hex<C>>
        where C: num_traits::FromPrimitive
    {
        let n = self.distance_to(other.clone());
        let step = 1.0 / cmp::max(n.clone(), num_traits::one()).to_f32().unwrap();
        let mut start = FHex::new(self.clone());
        start.x += offset.x;
        start.y += offset.y;
        start.z += offset.z;
        let end = FHex::new(other);
        num_iter::range_inclusive(num_traits::zero(), n)
            .map(move |i| start.lerp(&end, step*(i.to_f32().unwrap())).round())
    }
}

impl<C: HexCoord> Delta<C> {
    pub fn dx(&self) -> C { self.dx.clone() }
    pub fn dy(&self) -> C { self.dy.clone() }
    pub fn dz(&self) -> C { - (self.dx() + self.dy()) }
    /// The length of this translation, i.e. the number of hexes a line of this length would have.
    ///
    /// # Examples
    ///
    /// ```
    /// use hex::{Delta};
    /// assert_eq!(Delta{dx:0,dy:0}.length(), 0);
    /// assert_eq!(Delta{dx:1,dy:2}.length(), 3);
    /// ```
    pub fn length(&self) -> C {
        let two = num_traits::one::<C>() + num_traits::one();
        (self.dx().abs() + self.dy().abs() + self.dz().abs()) / two
    }
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
#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug, Serialize, Deserialize)]
pub enum Direction { XY, XZ, YZ, YX, ZX, ZY }

impl Direction {
    // TODO: implement all() in terms of Range / Step?
    /// All `Direction`s, in convenient `Iterator` format.
    pub fn all() -> std::slice::Iter<'static, Direction> { DIRECTIONS.iter() }
    /// Returns the `Delta` corresponding to a single move in this `Direction`.
    pub fn delta<C: HexCoord>(self) -> Delta<C> {
        let neg_one = num_traits::zero::<C>() - num_traits::one();
        match self {
            Direction::XY => Delta {dx: num_traits::one(), dy: neg_one},
            Direction::XZ => Delta {dx: num_traits::one(), dy: num_traits::zero()},
            Direction::YZ => Delta {dx: num_traits::zero(), dy: num_traits::one()},
            Direction::YX => Delta {dx: neg_one, dy: num_traits::one()},
            Direction::ZX => Delta {dx: neg_one, dy: num_traits::zero()},
            Direction::ZY => Delta {dx: num_traits::zero(), dy: neg_one},
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
pub fn parallelogram<C: HexCoord>(a1: Axis, a2: Axis,
                     a1_size: C, a2_size: C) -> impl Iterator<Item=Hex<C>>
    {
    assert!(a1 != a2);
    num_iter::range(num_traits::zero(), a1_size).flat_map(
        move |a1_val| num_iter::range(num_traits::zero(), a2_size.clone()).map(
            move |a2_val| {
                let x;
                let y;
                let a1_val = a1_val.clone();
                match (a1, a2) {
                    (Axis::X, Axis::Y) => { x = a1_val; y = a2_val; }
                    (Axis::X, Axis::Z) => { x = a1_val; y = -x.clone() - a2_val; }
                    (Axis::Y, Axis::X) => { y = a1_val; x = a2_val; }
                    (Axis::Y, Axis::Z) => { y = a1_val; x = -y.clone() - a2_val; }
                    (Axis::Z, Axis::X) => { x = a2_val; y = -x.clone() - a1_val; }
                    (Axis::Z, Axis::Y) => { y = a2_val; x = -y.clone() - a1_val; }
                    _ => panic!("Invalid axis combination")
                }
                Hex {x: x, y: y}
            }
        )
    )
}

struct FHex { x: f32, y: f32, z: f32 }

impl FHex {
    fn new<C: HexCoord>(h: Hex<C>) -> FHex {
        FHex {
            x: (h.x().to_f32().unwrap()),
            y: (h.y().to_f32().unwrap()),
            z: (h.z().to_f32().unwrap()),
        }
    }
    fn lerp(&self, other: &FHex, t: f32) -> FHex {
        FHex {
            x: self.x + (other.x - self.x)*t,
            y: self.y + (other.y - self.y)*t,
            z: self.z + (other.z - self.z)*t,
        }
    }
    fn round<C: HexCoord + num_traits::FromPrimitive>(&self) -> Hex<C> {
        let round_x = self.x.round();
        let round_y = self.y.round();
        let round_z = self.z.round();
        let mut x: C = num_traits::FromPrimitive::from_f32(round_x).unwrap();
        let mut y: C = num_traits::FromPrimitive::from_f32(round_y).unwrap();
        let z: C = num_traits::FromPrimitive::from_f32(round_z).unwrap();
        let x_diff = (round_x - self.x).abs();
        let y_diff = (round_y - self.y).abs();
        let z_diff = (round_z - self.z).abs();
        if x_diff > y_diff && x_diff > z_diff {
            x = -y.clone() - z;
        } else if y_diff > z_diff {
            y = -x.clone() - z;
        } else {
            // z is unused for the result
            // z = -x - y;
        }
        Hex {x: x, y: y}
    }
}

/// Clockwise or counter-clockwise rotation.
#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug, Serialize, Deserialize)]
pub enum Rotation { CW, CCW }

#[derive(PartialEq, Eq, Copy, Clone, Hash, Debug, Serialize, Deserialize)]
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
    use std::convert::TryInto;

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
            if dist == path_len.try_into().unwrap() { Ok(true) } else {
                Err(format!("dist = {:?} path_len = {:?} path = {:?}", dist, path_len, path))
            }
        }
        quickcheck(prop as fn(Hex) -> Result<bool, String>);
    }

    // The difference between subsequent hexes in a ray is the directional delta.
    #[test]
    fn ray_delta() {
        fn prop(h: Hex, d: Direction, i: SmallPositiveInt) -> bool {
            let mut prev = h - d.delta();
            h.ray(d, i.0 as i32).all(|pt| {
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
        fn expected(r: u32) -> usize { (r as usize)*6 }
        fn prop(h: Hex, r: SmallPositiveInt) -> bool { h.ring(r.0 as i32).count() == expected(r.0) }
        quickcheck(prop as fn(Hex, SmallPositiveInt) -> bool);
    }

    // The distance from hexes in a hex ring to the origin is the radius of the ring.
    #[test]
    fn ring_distance() {
        fn prop(h: Hex, r: SmallPositiveInt) -> bool {
            h.ring(r.0 as i32).all(|h2| { h.distance_to(h2) == r.0.try_into().unwrap() })
        }
        quickcheck(prop as fn(Hex, SmallPositiveInt) -> bool);
    }

    // Number of hexes in a hex area matches the expected function of radius.
    #[test]
    fn area_len() {
        fn expected(r: u32) -> usize { (3*r.pow(2) + 3*r + 1) as usize }
        fn prop(h: Hex, r: SmallNonNegativeInt) -> bool { h.area(r.0 as i32).count() == expected(r.0) }
        quickcheck(prop as fn(Hex, SmallNonNegativeInt) -> bool);
    }

    // The distance from hexes in a hex area to the origin is <= the radius of the area.
    #[test]
    fn area_distance() {
        fn prop(h: Hex, r: SmallNonNegativeInt) -> bool { h.area(r.0 as i32).all(|h2| h.distance_to(h2) <= r.0.try_into().unwrap()) }
        quickcheck(prop as fn(Hex, SmallNonNegativeInt) -> bool);
    }

}  // mod tests
