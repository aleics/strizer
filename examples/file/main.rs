use std::fs::File;
use std::io;
use strizer::StreamTokenizer;

fn main() -> io::Result<()> {
  let f = File::open("examples/file/data.txt")?;
  let f = &mut io::BufReader::new(f);

  let mut tokenizer = StreamTokenizer::new(f);
  tokenizer.ordinary_char('a');

  let a_count = tokenizer.filter(|token| token.is_character()).count();

  println!("Number of a: {}", a_count);

  Ok(())
}
