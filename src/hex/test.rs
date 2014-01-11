extern mod hex;

use std::rand::random;

use hex::Hex;

trait Arbitrary {
  fn get() -> Self;
}

impl Arbitrary for int {
  fn get() -> int { random() }
}

impl Arbitrary for Hex {
  fn get() -> Hex { Hex {x: Arbitrary::get(), y: Arbitrary::get(), z: Arbitrary::get()} }
}

struct OnFail { msg: ~str }

impl Drop for OnFail {
  fn drop(&mut self) {
    println(self.msg);
  }
}

#[test]
fn passes() { }

#[test]
fn six_neighbors() {
  for _ in std::iter::range(0, 100) {
    let hex: Hex = Arbitrary::get();
    let fail = OnFail { msg: hex.to_str() };
    assert_eq!(6, hex.neighbors().len());
  }
}
