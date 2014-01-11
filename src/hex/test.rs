extern mod hex;

use std::rand::random;

use hex::Hex;

trait Arbitrary : ToStr {
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
    let x: int = Arbitrary::get();
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

fn run_test<T: Arbitrary + Clone>(f: |T| -> bool) {
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
  run_test::<Hex>(|hex| { hex.neighbors().len() == 5 });
  // Q: why does the "do" syntactic sugar require a fn that takes a proc?
  /*
  run_test::<Hex>(|hex| {
    assert_eq!(6, hex.neighbors().len());
  });
  */
}

#[test]
fn transitive_neighbors() {
}
