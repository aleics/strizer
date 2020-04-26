use std::fs::File;
use std::io;
use strizer::{StreamTokenizer, TokenKind};

fn main() -> io::Result<()> {
  let f = File::open("examples/file/data.txt")?;
  let f = &mut io::BufReader::new(f);

  let tokenizer = StreamTokenizer::new(f, &['a']);

  let mut a_count = 0;
  let mut sit_count = 0;

  tokenizer.for_each(|(token, _, slice)| match token.kind() {
    TokenKind::Character => {
      if slice == "a" {
        a_count += 1;
      }
    }
    TokenKind::Word => {
      if slice == "sit" {
        sit_count += 1;
      }
    }
  });

  println!("Number of 'a': {}", a_count);
  println!("Number of \"sit\": {}", sit_count);

  Ok(())
}
