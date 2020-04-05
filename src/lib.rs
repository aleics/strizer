use std::io::BufRead;

/// `TokenKind` defines the different types of [`Token`] available.
///
/// [`Token`]: struct.Token.html
#[derive(PartialEq, Debug)]
pub enum TokenKind {
  Character(char),
  Number(f32),
  Word(String),
}

/// `Token` describes the primitive that is returned while iterating through a Tokenizer.
/// Tokens can be of different type or kind: [`TokenKind::Character`] or [`TokenKind::Word`].
/// The associated data is stored in the Token, along with its start position (in bytes),
/// and its index.
///
/// [`TokenKind::Character`]: enum.TokenKind.html#variant.Character
/// [`TokenKind::Word`]: enum.TokenKind.html#variant.Word
#[derive(PartialEq, Debug)]
pub struct Token {
  pub kind: TokenKind,
  start: usize,
}

impl Token {
  /// Creates a character token with a given start position (in bytes).
  pub fn character(character: char, start: usize) -> Token {
    Token {
      kind: TokenKind::Character(character),
      start,
    }
  }

  /// Returns `true` if the `Token` is [`TokenKind::Character`]
  ///
  /// [`TokenKind::Character`]: enum.TokenKind.html#variant.Character
  pub fn is_character(&self) -> bool {
    match self.kind {
      TokenKind::Character(_) => true,
      _ => false,
    }
  }

  /// Returns `true` if the `Token` is [`TokenKind::Character`] and equal to the `input` character.
  ///
  /// [`TokenKind::Character`]: enum.TokenKind.html#variant.Character
  pub fn is_character_equal(&self, input: char) -> bool {
    match self.kind {
      TokenKind::Character(character) => character == input,
      _ => false,
    }
  }

  /// Creates a word token with a given start position (in bytes).
  pub fn word(term: &str, start: usize) -> Token {
    Token {
      kind: TokenKind::Word(term.to_owned()),
      start,
    }
  }

  /// Returns `true` if the `Token` is [`TokenKind::Word`]
  ///
  /// [`TokenKind::Word`]: enum.TokenKind.html#variant.Word
  pub fn is_word(&self) -> bool {
    match self.kind {
      TokenKind::Word(_) => true,
      _ => false,
    }
  }

  /// Returns `true` if the `Token` is [`TokenKind::Word`] and equal to the `input` string
  /// reference.
  ///
  /// [`TokenKind::Word`]: enum.TokenKind.html#variant.Word
  pub fn is_word_equal(&self, input: &str) -> bool {
    match self.kind {
      TokenKind::Word(ref word) => word == input,
      _ => false,
    }
  }

  /// Creates a number token with a given start position (in bytes).
  pub fn number(number: f32, start: usize) -> Token {
    Token {
      kind: TokenKind::Number(number),
      start,
    }
  }

  /// Returns `true` if the `Token` is [`TokenKind::Number`]
  ///
  /// [`TokenKind::Number`]: enum.TokenKind.html#variant.Number
  pub fn is_number(&self) -> bool {
    match self.kind {
      TokenKind::Number(_) => true,
      _ => false,
    }
  }

  /// Returns `true` if the `Token` is [`TokenKind::Number`] and equal to the `input` string
  /// reference.
  ///
  /// [`TokenKind::Number`]: enum.TokenKind.html#variant.Number
  pub fn is_number_equal(&self, input: f32) -> bool {
    match self.kind {
      TokenKind::Number(number) => (number - input).abs() < std::f32::EPSILON,
      _ => false,
    }
  }
}

/// `StreamTokenizer<R>` defines the structure for the tokenization of a given input that implements
/// the [`BufRead`] trait. By using [`BufRead`], the content of the text data is efficiently
/// tokenized by reading it line-by-line.
///
/// # Examples
///
/// ```no_run
/// use std::fs::File;
/// use std::io::BufReader;
/// use strizer::{StreamTokenizer, Token, TokenKind};
///
/// fn main() -> std::io::Result<()> {
///   let file = File::open("log.txt")?;
///   let mut reader = BufReader::new(file);
///
///   let error_count = StreamTokenizer::new(&mut reader)
///     .filter(|token| token.is_word_equal("ERROR"))
///     .count();
///   println!("number of error logs: {}", error_count);
///   Ok(())
/// }
/// ```
///
/// [`BufRead`]: https://doc.rust-lang.org/std/io/trait.BufRead.html
pub struct StreamTokenizer<'a, R> {
  input: &'a mut R,
  current_line: Option<String>,
  line_offset: usize,
  offset: usize,
  ordinary_chars: Vec<char>,
}

impl<'a, R: BufRead> StreamTokenizer<'a, R> {
  /// Creates a new `StreamTokenizer<R>` with a given [`BufRead`] input. The different offsets
  /// and data used while iterating is also initialized.
  ///
  /// [`BufRead`]: https://doc.rust-lang.org/std/io/trait.BufRead.html
  pub fn new(input: &'a mut R) -> Self {
    StreamTokenizer {
      input,
      current_line: None,
      line_offset: 0,
      offset: 0,
      ordinary_chars: Vec::new(),
    }
  }

  /// Includes a new ordinary character that is identified during iteration as character [`Token`].
  ///
  /// # Examples
  ///
  /// ```
  /// use std::io::Cursor;
  /// use strizer::{StreamTokenizer, Token, TokenKind};
  ///
  /// let cursor = &mut Cursor::new("abracadabra");
  /// let mut tokenizer = StreamTokenizer::new(cursor);
  /// tokenizer.ordinary_char('a');
  ///
  /// let a_count = tokenizer
  ///   .filter(|token| token.is_character_equal('a'))
  ///   .count();
  ///
  /// assert_eq!(a_count, 5);
  /// ```
  ///
  /// [`Token`]: struct.Token.html
  pub fn ordinary_char(&mut self, c: char) {
    self.ordinary_chars.push(c);
  }

  /// Reads the next line from the inner [`BufRead`]. Returns `None` if the line couldn't be read
  /// or the buffer has reached end of file.
  ///
  /// [`BufRead`]: https://doc.rust-lang.org/std/io/trait.BufRead.html
  fn read_next_line(&mut self) -> Option<String> {
    let mut buf = String::new();
    let eof = self.input.read_line(&mut buf).ok().map(|bytes| bytes > 0)?;
    if eof {
      Some(buf)
    } else {
      None
    }
  }
}

/// [`StreamTokenizer<R>`] implementation for [`Iterator`].
impl<'a, R: BufRead> Iterator for StreamTokenizer<'a, R> {
  type Item = Token;

  fn next(&mut self) -> Option<Self::Item> {
    if self.current_line.is_none() {
      self.current_line = self.read_next_line();
    }

    while let Some(line) = &self.current_line {
      for character in line[self.line_offset..].chars() {
        let (token, length) = extract_token(
          &line[self.line_offset..],
          character,
          &self.ordinary_chars,
          self.offset,
        );

        self.offset += length;
        self.line_offset += length;

        if token.is_some() {
          return token;
        }
      }

      self.current_line = self.read_next_line();
      self.line_offset = 0;
    }

    None
  }
}

/// `StringTokenizer` defines the structure for the tokenization of strings.
///
/// # Examples
///
/// ```
/// use strizer::StringTokenizer;
///
/// let word_count = StringTokenizer::new("hello world").count();
/// assert_eq!(word_count, 2);
/// ```
#[derive(Clone)]
pub struct StringTokenizer<'a> {
  input: &'a str,
  offset: usize,
  ordinary_chars: Vec<char>,
}

impl<'a> StringTokenizer<'a> {
  /// Creates a new `StringTokenizer` with a given string input. The different offsets
  /// and data used while iterating is also initialized.
  pub fn new(input: &'a str) -> Self {
    StringTokenizer {
      input,
      offset: 0,
      ordinary_chars: Vec::new(),
    }
  }

  /// Includes a new ordinary character that is identified during iteration as character [`Token`].
  ///
  /// # Examples
  ///
  /// ```
  /// use std::io::Cursor;
  /// use strizer::{StringTokenizer, Token, TokenKind};
  ///
  /// let mut tokenizer = StringTokenizer::new("abracadabra");
  /// tokenizer.ordinary_char('a');
  ///
  /// let a_count = tokenizer
  ///   .filter(|token| token.is_character_equal('a'))
  ///   .count();
  ///
  /// assert_eq!(a_count, 5);
  /// ```
  ///
  /// [`Token`]: struct.Token.html
  pub fn ordinary_char(&mut self, c: char) {
    self.ordinary_chars.push(c);
  }
}

/// [`StringTokenizer`] implementation for [`Iterator`].
impl<'a> Iterator for StringTokenizer<'a> {
  type Item = Token;

  fn next(&mut self) -> Option<Self::Item> {
    for character in self.input[self.offset..].chars() {
      let (token, length) = extract_token(
        &self.input[self.offset..],
        character,
        &self.ordinary_chars,
        self.offset,
      );

      self.offset += length;

      if token.is_some() {
        return token;
      }
    }
    None
  }
}

fn extract_token(
  input: &str,
  character: char,
  delimiters: &[char],
  offset: usize,
) -> (Option<Token>, usize) {
  if delimiters.contains(&character) {
    let (token, length) = extract_character_token(character, offset);
    (Some(token), length)
  } else if character.is_whitespace() {
    (None, character.len_utf8())
  } else {
    let (token, length) = extract_token_chunk(&input, &delimiters, offset);
    (Some(token), length)
  }
}

fn extract_character_token(character: char, offset: usize) -> (Token, usize) {
  let token = Token::character(character, offset);
  (token, character.len_utf8())
}

fn extract_token_chunk<'a>(
  input: &'a str,
  delimiters: &'a [char],
  offset: usize,
) -> (Token, usize) {
  let chunk = extract_chunk(input, delimiters);

  let token = if let Ok(number) = chunk.parse() {
    Token::number(number, offset)
  } else {
    Token::word(chunk, offset)
  };
  (token, chunk.len())
}

fn extract_chunk<'a>(input: &'a str, delimiters: &'a [char]) -> &'a str {
  input
    .char_indices()
    .find(|(_, c)| c.is_whitespace() || delimiters.contains(c))
    .map(|(index, _)| &input[..index])
    .unwrap_or(&input)
}

#[cfg(test)]
mod token_tests {
  use crate::{Token, TokenKind};

  #[test]
  fn is_character() {
    let char_token = Token {
      kind: TokenKind::Character('a'),
      start: 0,
    };
    assert_eq!(char_token.is_character(), true);

    let word_token = Token {
      kind: TokenKind::Word(String::from("a")),
      start: 0,
    };
    assert_eq!(word_token.is_character(), false);
  }

  #[test]
  fn is_character_equal() {
    let char_token = Token {
      kind: TokenKind::Character('a'),
      start: 0,
    };
    assert_eq!(char_token.is_character_equal('a'), true);
    assert_eq!(char_token.is_character_equal('b'), false);
  }

  #[test]
  fn is_word() {
    let word_token = Token {
      kind: TokenKind::Word(String::from("a")),
      start: 0,
    };
    assert_eq!(word_token.is_word(), true);

    let char_token = Token {
      kind: TokenKind::Character('a'),
      start: 0,
    };
    assert_eq!(char_token.is_word(), false);
  }

  #[test]
  fn is_word_equal() {
    let word_token = Token {
      kind: TokenKind::Word(String::from("a")),
      start: 0,
    };
    assert_eq!(word_token.is_word_equal("a"), true);
    assert_eq!(word_token.is_word_equal("b"), false);
  }

  #[test]
  fn is_number() {
    let number_token = Token {
      kind: TokenKind::Number(1.0),
      start: 0,
    };
    assert_eq!(number_token.is_number(), true);

    let char_token = Token {
      kind: TokenKind::Character('a'),
      start: 0,
    };
    assert_eq!(char_token.is_number(), false);
  }

  #[test]
  fn is_number_equal() {
    let number_token = Token {
      kind: TokenKind::Number(1.0),
      start: 0,
    };
    assert_eq!(number_token.is_number_equal(1.0), true);
    assert_eq!(number_token.is_number_equal(-1.0), false);
  }
}

#[cfg(test)]
mod string_tokenizer_tests {
  use crate::{StringTokenizer, Token};

  #[test]
  fn handles_whitespace() {
    let result = StringTokenizer::new(" ").collect::<Vec<Token>>();
    assert_eq!(result.len(), 0);
  }

  #[test]
  fn handle_custom_whitespace() {
    let result = StringTokenizer::new("\u{2000}").collect::<Vec<Token>>();
    assert_eq!(result.len(), 0);
  }

  #[test]
  fn handles_multiple_whitespace() {
    let result = StringTokenizer::new("  ").collect::<Vec<Token>>();
    assert_eq!(result.len(), 0);
  }

  #[test]
  fn handles_whitespace_as_char() {
    let mut tokenizer = StringTokenizer::new(" ");
    tokenizer.ordinary_char(' ');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 1);
    assert_eq!(result.get(0), Some(&Token::character(' ', 0)));
  }

  #[test]
  fn handles_multiple_whitespace_with_chars() {
    let mut tokenizer = StringTokenizer::new(" a ");
    tokenizer.ordinary_char('a');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 1);
    assert_eq!(result.get(0), Some(&Token::character('a', 1)));
  }

  #[test]
  fn handles_multiple_whitespace_with_word() {
    let tokenizer = StringTokenizer::new(" hello world ");

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 1)));
    assert_eq!(result.get(1), Some(&Token::word("world", 7)));
  }

  #[test]
  fn handles_whitespace_with_word() {
    let tokenizer = StringTokenizer::new("hello world");

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 0)));
    assert_eq!(result.get(1), Some(&Token::word("world", 6)));
  }

  #[test]
  fn handles_new_line() {
    let tokenizer = StringTokenizer::new("hello \n world");

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 0)));
    assert_eq!(result.get(1), Some(&Token::word("world", 8)));
  }

  #[test]
  fn handle_flags_chars_word() {
    let tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8}\u{1F1EE}\u{1F1F4}");

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 1);
    assert_eq!(
      result.get(0),
      Some(&Token::word("\u{1F1F7}\u{1F1F8}\u{1F1EE}\u{1F1F4}", 0))
    );
  }

  #[test]
  fn handle_flags_with_ordinary_flag() {
    let mut tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8}\u{1F1EE}\u{1F1F4}");
    tokenizer.ordinary_char('\u{1F1F8}');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get(0), Some(&Token::word("\u{1F1F7}", 0)));
    assert_eq!(result.get(1), Some(&Token::character('\u{1F1F8}', 4)));
    assert_eq!(result.get(2), Some(&Token::word("\u{1F1EE}\u{1F1F4}", 8)));
  }

  #[test]
  fn handle_flags_with_multiple_ordinary_char() {
    let mut tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8}a\u{1F1EE}b\u{1F1F4}");
    tokenizer.ordinary_char('a');
    tokenizer.ordinary_char('b');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 5);
    assert_eq!(result.get(0), Some(&Token::word("\u{1F1F7}\u{1F1F8}", 0)));
    assert_eq!(result.get(1), Some(&Token::character('a', 8)));
    assert_eq!(result.get(2), Some(&Token::word("\u{1F1EE}", 9)));
    assert_eq!(result.get(3), Some(&Token::character('b', 13)));
    assert_eq!(result.get(4), Some(&Token::word("\u{1F1F4}", 14)));
  }

  #[test]
  fn handle_flags_with_multiple_whitespaces() {
    let tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8} \u{1F1EE}\n\u{1F1F4}");

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get(0), Some(&Token::word("\u{1F1F7}\u{1F1F8}", 0)));
    assert_eq!(result.get(1), Some(&Token::word("\u{1F1EE}", 9)));
    assert_eq!(result.get(2), Some(&Token::word("\u{1F1F4}", 14)));
  }

  #[test]
  fn handle_chinese_char() {
    let tokenizer = StringTokenizer::new("hello ⼦");

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 0)));
    assert_eq!(result.get(1), Some(&Token::word("⼦", 6)));
  }

  #[test]
  fn handle_chinese_ordinary_char() {
    let mut tokenizer = StringTokenizer::new("hello ⼦");
    tokenizer.ordinary_char('⼦');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 0)));
    assert_eq!(result.get(1), Some(&Token::character('⼦', 6)));
  }

  #[test]
  fn handle_natural_numbers() {
    let tokenizer = StringTokenizer::new("1 2 3");

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get(0), Some(&Token::number(1f32, 0)));
    assert_eq!(result.get(1), Some(&Token::number(2f32, 2)));
    assert_eq!(result.get(2), Some(&Token::number(3f32, 4)));
  }

  #[test]
  fn handle_decimal_numbers() {
    let tokenizer = StringTokenizer::new("1.1 2.2 3.3");

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get(0), Some(&Token::number(1.1f32, 0)));
    assert_eq!(result.get(1), Some(&Token::number(2.2f32, 4)));
    assert_eq!(result.get(2), Some(&Token::number(3.3f32, 8)));
  }

  #[test]
  fn handle_negative_integer_numbers() {
    let tokenizer = StringTokenizer::new("-1 -2 -3");

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get(0), Some(&Token::number(-1f32, 0)));
    assert_eq!(result.get(1), Some(&Token::number(-2f32, 3)));
    assert_eq!(result.get(2), Some(&Token::number(-3f32, 6)));
  }

  #[test]
  fn handle_negative_decimal_numbers() {
    let tokenizer = StringTokenizer::new("-1.1 -2.2 -3.3");

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get(0), Some(&Token::number(-1.1f32, 0)));
    assert_eq!(result.get(1), Some(&Token::number(-2.2f32, 5)));
    assert_eq!(result.get(2), Some(&Token::number(-3.3f32, 10)));
  }

  #[test]
  fn handle_numbers_with_ordinary_chars() {
    let mut tokenizer = StringTokenizer::new("-1 -2 -3");
    tokenizer.ordinary_char('-');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 6);
    assert_eq!(result.get(0), Some(&Token::character('-', 0)));
    assert_eq!(result.get(1), Some(&Token::number(1f32, 1)));
    assert_eq!(result.get(2), Some(&Token::character('-', 3)));
    assert_eq!(result.get(3), Some(&Token::number(2f32, 4)));
    assert_eq!(result.get(4), Some(&Token::character('-', 6)));
    assert_eq!(result.get(5), Some(&Token::number(3f32, 7)));
  }
}

#[cfg(test)]
mod stream_tokenizer_tests {
  use std::io::Cursor;

  use crate::{StreamTokenizer, Token};

  #[test]
  fn handles_multiple_lines_with_whitespace() {
    let result =
      StreamTokenizer::new(&mut Cursor::new(" \n\u{2000}\n \n ")).collect::<Vec<Token>>();
    assert_eq!(result.len(), 0);
  }

  #[test]
  fn handles_multiple_whitespace_with_chars() {
    let cursor = &mut Cursor::new(" a ");

    let mut tokenizer = StreamTokenizer::new(cursor);
    tokenizer.ordinary_char('a');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 1);
    assert_eq!(result.get(0), Some(&Token::character('a', 1)));
  }

  #[test]
  fn handles_multiple_whitespace_with_word() {
    let result = StreamTokenizer::new(&mut Cursor::new(" hello world ")).collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 1)));
    assert_eq!(result.get(1), Some(&Token::word("world", 7)));
  }

  #[test]
  fn handles_multiple_lines_with_words() {
    let result = StreamTokenizer::new(&mut Cursor::new(" hello \n world ")).collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 1)));
    assert_eq!(result.get(1), Some(&Token::word("world", 9)));
  }

  #[test]
  fn handles_multiple_lines_with_words_and_ordinary_chars() {
    let cursor = &mut Cursor::new(" hello \n world \n\n!");

    let mut tokenizer = StreamTokenizer::new(cursor);
    tokenizer.ordinary_char('!');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get(0), Some(&Token::word("hello", 1)));
    assert_eq!(result.get(1), Some(&Token::word("world", 9)));
    assert_eq!(result.get(2), Some(&Token::character('!', 17)));
  }

  #[test]
  fn handles_multiple_lines_with_flag_chars() {
    let cursor = &mut Cursor::new("\u{1F1EE}\n\n\u{1F1EE}\u{1F1F8}\n\u{1F1F7}\u{1F1F8}");

    let mut tokenizer = StreamTokenizer::new(cursor);
    tokenizer.ordinary_char('\u{1F1EE}');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 4);
    assert_eq!(result.get(0), Some(&Token::character('\u{1F1EE}', 0)));
    assert_eq!(result.get(1), Some(&Token::character('\u{1F1EE}', 6)));
    assert_eq!(result.get(2), Some(&Token::word("\u{1F1F8}", 10)));
    assert_eq!(result.get(3), Some(&Token::word("\u{1F1F7}\u{1F1F8}", 15)));
  }

  #[test]
  fn handle_multiple_lines_numbers() {
    let cursor = &mut Cursor::new("1.1\n2\n\n-3\n-4.4");
    let tokenizer = StreamTokenizer::new(cursor);

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 4);
    assert_eq!(result.get(0), Some(&Token::number(1.1f32, 0)));
    assert_eq!(result.get(1), Some(&Token::number(2f32, 4)));
    assert_eq!(result.get(2), Some(&Token::number(-3f32, 7)));
    assert_eq!(result.get(3), Some(&Token::number(-4.4f32, 10)));
  }

  #[test]
  fn handle_multiple_lines_numbers_with_ordinary_chars() {
    let cursor = &mut Cursor::new("1.1\n2\n\n-3\n-4.4");
    let mut tokenizer = StreamTokenizer::new(cursor);
    tokenizer.ordinary_char('-');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 6);
    assert_eq!(result.get(0), Some(&Token::number(1.1f32, 0)));
    assert_eq!(result.get(1), Some(&Token::number(2f32, 4)));
    assert_eq!(result.get(2), Some(&Token::character('-', 7)));
    assert_eq!(result.get(3), Some(&Token::number(3f32, 8)));
    assert_eq!(result.get(4), Some(&Token::character('-', 10)));
    assert_eq!(result.get(5), Some(&Token::number(4.4f32, 11)));
  }
}
