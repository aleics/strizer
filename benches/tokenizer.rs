#![feature(test)]

extern crate test;

use test::Bencher;

use std::io::Cursor;
use strizer::{StreamTokenizer, StringTokenizer, Token};

#[bench]
fn bench_string_tokenize_words(b: &mut Bencher) {
  b.iter(|| StringTokenizer::new("hello world", &[]).collect::<Vec<Token>>());
}

#[bench]
fn bench_string_tokenize_ordinary_chars(b: &mut Bencher) {
  let tokenizer = StringTokenizer::new("hello world", &['o']);
  b.iter(|| tokenizer.clone().collect::<Vec<Token>>());
}

#[bench]
fn bench_stream_tokenize_words(b: &mut Bencher) {
  let cursor = &mut Cursor::new("hello\nworld!\n");
  b.iter(|| StreamTokenizer::new(cursor, &[]).collect::<Vec<Token>>());
}

#[bench]
fn bench_stream_tokenize_ordinary_chars(b: &mut Bencher) {
  let cursor = &mut Cursor::new("hello\nworld!\n");
  b.iter(|| {
    let tokenizer = StreamTokenizer::new(cursor, &['o']);
    tokenizer.collect::<Vec<Token>>()
  });
}
