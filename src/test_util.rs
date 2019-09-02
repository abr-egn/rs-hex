use super::{Hex, Delta, Direction, Rotation};

use std::cmp::PartialEq;
use std::fmt::Debug;
use rand::Rng;

impl quickcheck::Arbitrary for Hex {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
        let x = g.gen_range(-1000, 1000);
        let y = g.gen_range(-1000, 1000);
        Hex {x: x, y: y}
    }
    fn shrink(&self) -> Box<dyn Iterator<Item=Hex>> {
        let xy = (self.x, self.y).shrink();
        let out = xy.map(|(x, y)| Hex {x: x, y: y});
        Box::new(out)
    }
}

impl quickcheck::Arbitrary for Delta {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
        let Hex {x, y} = quickcheck::Arbitrary::arbitrary(g);
        Delta {dx: x, dy: y}
    }
    fn shrink(&self) -> Box<dyn Iterator<Item=Delta>> {
        Box::new(Hex {x: self.dx, y: self.dy}.shrink().map(|Hex {x, y}| Delta {dx: x, dy: y}))
    }
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

impl quickcheck::Arbitrary for Rotation {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
        match g.gen_range(0, 2) {
            0 => Rotation::CW,
            1 => Rotation::CCW,
            _ => panic!("Invalid arbitrary rotation"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct SmallPositiveInt(pub u32);

impl quickcheck::Arbitrary for SmallPositiveInt {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
        SmallPositiveInt(g.gen_range(1, 100))
    }
    fn shrink(&self) -> Box<dyn Iterator<Item=SmallPositiveInt>> {
        match self.0 {
            1 => quickcheck::empty_shrinker(),
            n => quickcheck::single_shrinker(SmallPositiveInt(n/2))
        }
    }
}

#[derive(Clone, Debug)]
pub struct SmallNonNegativeInt(pub u32);

impl quickcheck::Arbitrary for SmallNonNegativeInt {
    fn arbitrary<G: quickcheck::Gen>(g: &mut G) -> Self {
        SmallNonNegativeInt(g.gen_range(0, 100))
    }
    fn shrink(&self) -> Box<dyn Iterator<Item=SmallNonNegativeInt>> {
        match self.0 {
            0 => quickcheck::empty_shrinker(),
            1 => quickcheck::single_shrinker(SmallNonNegativeInt(0)),
            n => quickcheck::single_shrinker(SmallNonNegativeInt(n/2)),
        }
    }
}

pub fn check_eq<A, B>(left: A, right: B) -> Result<bool, String>
    where A: PartialEq<B>,
          A: Debug,
          B: Debug,
    {
    if left == right {
        Ok(true)
    } else {
        Err(format!("{:?} != {:?})", left, right))
    }
}