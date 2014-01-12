extern mod hex;

use std::rand::random;
use std::rand::distributions::range::Range;
use std::rand::distributions::range::SampleRange;
use std::hashmap::HashSet;

use hex::Hex;
use hex::Direction;

trait Arbitrary : ToStr + Clone {
  fn get() -> Self;
  fn narrow(self) -> Option<Self> { None }
}

impl Arbitrary for int {
  fn get() -> int { random() }
  fn narrow(self) -> Option<int> {
    match self {
      0 => None,
      1 | -1 => Some(0),
      v => Some(v/2)
    }
  }
}

fn bounded<T: SampleRange + Ord>(min: T, max: T) -> T {
  let r = Range::new(min, max);
  SampleRange::sample_range(&r, &mut std::rand::task_rng())
}

impl Arbitrary for Hex {
  fn get() -> Hex {
    let x = bounded(-1000, 1000);
    let y = bounded(-1000, 1000);
    Hex {x: x, y: y, z: 0 - (x+y)}
  }
  fn narrow(self) -> Option<Hex> {
    let Hex {x, y, ..} = self;
    match (x.narrow(), y.narrow()) {
      (Some(x2), Some(y2)) => Some(Hex {x: x2, y: y2, z: 0 - (x2+y2)}),
      _ => None
    }
  }
}

impl<A: Arbitrary, B: Arbitrary> Arbitrary for (A, B) {
  fn get() -> (A, B) { (Arbitrary::get(), Arbitrary::get()) }
  fn narrow(self) -> Option<(A, B)> {
    let (a, b) = self;
    match (a.clone().narrow(), b.clone().narrow()) {
      (Some(a2), Some(b2)) => Some((a2, b2)),
      (Some(a2), None) => Some((a2, b)),
      (None, Some(b2)) => Some((a, b2)),
      _ => None
    }
  }
}

impl<A: Arbitrary, B: Arbitrary, C: Arbitrary> Arbitrary for (A, B, C) {
  fn get() -> (A, B, C) { (Arbitrary::get(), Arbitrary::get(), Arbitrary::get()) }
  fn narrow(self) -> Option<(A, B, C)> {
    let (a, b, c) = self;
    let mut some = false;
    let a2 = match a.clone().narrow() {
      Some(v) => { some = true; v }
      None => a
    };
    let b2 = match b.clone().narrow() {
      Some(v) => { some = true; v }
      None => b
    };
    let c2 = match c.clone().narrow() {
      Some(v) => { some = true; v }
      None => c
    };
    if some { Some((a2, b2, c2)) } else { None }
  }
}

fn run_test<T: Arbitrary>(f: |T| -> bool) {
  for _ in std::iter::range(0, 100) {
    let val: T = Arbitrary::get();
    if !f(val.clone()) {
      let mut failing = val;
      loop {
        match failing.clone().narrow() {
          None => break,
          Some(v) => {
            if f(v.clone()) { break }
            else { failing = v }
          }
        }
      }
      fail!(failing.to_str())
    }
  }
}

#[test]
fn six_neighbors() {
  run_test::<Hex>(|hex| { hex.neighbors().len() == 6 });
}

fn test_neighbors(f: |Hex, Hex, &[Hex]| -> bool) {
  run_test::<Hex>(|hex| {
    let ns = hex.neighbors();
    ns.iter().all(|n| {
      f(hex, *n, ns)
    })
  });
}

#[test]
fn transitive_neighbors() {
  test_neighbors(|hex, n, _| {
    let nns = n.neighbors();
    nns.iter().any(|nn| *nn == hex)
  });
}

#[test]
fn overlap_neighbors() {
  test_neighbors(|_, n, ns| {
    let nns = n.neighbors();
    let ns_set: HashSet<&Hex> = ns.iter().collect();
    let nns_set: HashSet<&Hex> = nns.iter().collect();
    ns_set.intersection(&nns_set).len() == 2
  });
}

#[test]
fn neighbor_distance() {
  test_neighbors(|p, n, _| {
    hex::distance(p, n) == 1
  });
}

#[test]
fn neighbor_direction() {
  run_test::<Hex>(|p| {
    let mut ds: ~[Hex] = Direction::all().map(|d| p + d.delta()).collect();
    ds.sort();
    let mut ns = p.neighbors();
    ns.sort();
    ds == ns
  });
}

impl Arbitrary for Direction {
  fn get() -> Direction { random() }
}

#[deriving(Clone, ToStr)]
struct SmallPositiveInt(uint);

impl Arbitrary for SmallPositiveInt {
  fn get() -> SmallPositiveInt { SmallPositiveInt(bounded(1u, 1000u)) }
  fn narrow(self) -> Option<SmallPositiveInt> {
    match self {
      SmallPositiveInt(1) => None,
      SmallPositiveInt(v) => Some(SmallPositiveInt(v/2))
    }
  }
}

#[test]
fn line_length() {
  run_test::<(Hex, Direction, SmallPositiveInt)>(|(h, d, SmallPositiveInt(i))|
    hex::line(h, d, i).len() == i
  );
}
