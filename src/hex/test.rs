extern mod hex;

use std::rand::random;
use std::hashmap::HashSet;

use hex::Hex;

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

impl Arbitrary for Hex {
  fn get() -> Hex {
    let x = Arbitrary::get();
    let y: int = Arbitrary::get();
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
