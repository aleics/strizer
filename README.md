# strizer

[![CI](https://github.com/aleics/strizer/workflows/CI/badge.svg?event=push)](https://github.com/aleics/strizer/actions/workflows/ci.yml)
[![Crate](https://img.shields.io/crates/v/strizer.svg)](https://crates.io/crates/strizer)
[![Docs](https://docs.rs/strizer/badge.svg)](https://docs.rs/strizer)

__strizer__ is a minimal and fast library for text tokenization.

## Usage
### Install
Add this to your `Cargo.toml`:

```toml
[dependencies]
strizer = "0.1.0"
```

### StreamTokenizer
```rust
use std::fs::File;
use std::io::BufReader;
use strizer::{StreamTokenizer, Token, TokenKind};

fn main() -> std::io::Result<()> {
  // read contest to a reader buffer
  let file = File::open("log.txt")?;
  let mut reader = BufReader::new(file);

  // tokenize BufRead, and count number of "ERROR" words
  let error_count = StreamTokenizer::new(&mut reader, &[])
    .filter(|(_, _, slice)| slice == "ERROR")
    .count();

  println!("number of error logs: {}", error_count);
  Ok(())
}
```

### StringTokenizer
```rust
use strizer::StringTokenizer;

fn main() {
  // tokenize input string and count the amount of words
  let token_count = StringTokenizer::new("hello world", &[]).count();

  println!("number of words: {}", token_count);
}
```

## License
[MIT](https://choosealicense.com/licenses/mit/)
