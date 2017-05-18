#![cfg(feature = "serde")]

#[macro_use]
extern crate ordermap;
extern crate serde_test;

use serde_test::{Token, assert_tokens};

#[test]
fn test_serde() {
    let map = ordermap! { 1 => 2, 3 => 4 };
    assert_tokens(&map,
                  &[Token::Map { len: Some(2) },
                    Token::I32(1),
                    Token::I32(2),
                    Token::I32(3),
                    Token::I32(4),
                    Token::MapEnd]);
}
