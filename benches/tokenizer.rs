#![feature(test)]

extern crate test;

use strizer::{StringTokenizer, Token};
use test::Bencher;

#[bench]
fn bench_tokenize_words(b: &mut Bencher) {
  let tokenizer = StringTokenizer::new("hello world");
  b.iter(|| tokenizer.clone().collect::<Vec<Token>>());
}

#[bench]
fn bench_tokenize_ordinary_chars(b: &mut Bencher) {
  let mut tokenizer = StringTokenizer::new("hello world");
  tokenizer.ordinary_char('o');
  b.iter(|| tokenizer.clone().collect::<Vec<Token>>());
}
