#![feature(test)]

extern crate test;

use test::Bencher;

use std::io::Cursor;
use strizer::{Span, StreamTokenizer, StringTokenizer, Token};

#[bench]
fn bench_string_tokenize_words(b: &mut Bencher) {
  let tokenizer = StringTokenizer::new("hello world", &[]);
  b.iter(|| tokenizer.collect::<Vec<(Token, Span, &str)>>());
}

#[bench]
fn bench_string_tokenize_identifiers(b: &mut Bencher) {
  let tokenizer = StringTokenizer::new("hello world", &['o']);
  b.iter(|| tokenizer.collect::<Vec<(Token, Span, &str)>>());
}

#[bench]
fn bench_stream_tokenize_words(b: &mut Bencher) {
  let cursor = &mut Cursor::new("hello\nworld!\n");
  b.iter(|| StreamTokenizer::new(cursor, &[]).collect::<Vec<(Token, Span, String)>>());
}

#[bench]
fn bench_stream_tokenize_identifiers(b: &mut Bencher) {
  let cursor = &mut Cursor::new("hello\nworld!\n");
  b.iter(|| {
    let tokenizer = StreamTokenizer::new(cursor, &['o']);
    tokenizer.collect::<Vec<(Token, Span, String)>>()
  });
}
