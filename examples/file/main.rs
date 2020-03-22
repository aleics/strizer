use std::fs::File;
use std::io;
use strizer::StreamTokenizer;

fn main() -> io::Result<()> {
  let f = File::open("examples/file/data.txt")?;
  let f = &mut io::BufReader::new(f);

  let mut tokenizer = StreamTokenizer::new(f);
  tokenizer.ordinary_char('a');

  let mut a_count = 0;
  let mut sit_count = 0;

  tokenizer.for_each(|token| {
    if token.is_character_equal('a') {
      a_count += 1;
    } else if token.is_word_equal("sit") {
      sit_count += 1;
    }
  });

  println!("Number of 'a': {}", a_count);
  println!("Number of \"sit\": {}", sit_count);

  Ok(())
}
