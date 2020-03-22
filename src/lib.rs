use std::io::BufRead;

/// `TokenKind` defines the different types of [`Token`] available.
///
/// [`Token`]: struct.Token.html
#[derive(PartialEq, Debug)]
pub enum TokenKind {
  Character(char),
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
  index: usize,
}

impl Token {
  /// Creates a character token with a given start position (in bytes) and an index.
  pub fn character(character: char, start: usize, index: usize) -> Token {
    Token {
      kind: TokenKind::Character(character),
      start,
      index,
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

  /// Creates a word token with a given start position (in bytes) and an index.
  pub fn word(term: &str, start: usize, index: usize) -> Token {
    Token {
      kind: TokenKind::Word(term.to_owned()),
      start,
      index,
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
///     .filter(|token| match &token.kind {
///       TokenKind::Word(word) => word == "ERROR",
///       TokenKind::Character(_) => false
///     })
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
  index: usize,
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
      index: 0,
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
  ///   .filter(|token| token.is_character())
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
          self.index,
        );

        self.offset += length;
        self.line_offset += length;

        if token.is_some() {
          self.index += 1;
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
  index: usize,
  ordinary_chars: Vec<char>,
}

impl<'a> StringTokenizer<'a> {
  /// Creates a new `StringTokenizer` with a given string input. The different offsets
  /// and data used while iterating is also initialized.
  pub fn new(input: &'a str) -> Self {
    StringTokenizer {
      input,
      offset: 0,
      index: 0,
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
  ///   .filter(|token| token.is_character())
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
        self.index,
      );

      self.offset += length;

      if token.is_some() {
        self.index += 1;
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
  index: usize,
) -> (Option<Token>, usize) {
  if character.is_whitespace() {
    return (None, character.len_utf8());
  }

  let (token, length) = if delimiters.contains(&character) {
    extract_character_token(character, offset, index)
  } else {
    extract_word_token(&input, &delimiters, offset, index)
  };

  (Some(token), length)
}

fn extract_character_token(character: char, offset: usize, index: usize) -> (Token, usize) {
  let token = Token::character(character, offset, index);
  (token, character.len_utf8())
}

fn extract_word_token<'a>(
  input: &'a str,
  delimiters: &'a [char],
  offset: usize,
  index: usize,
) -> (Token, usize) {
  let word = extract_word(input, delimiters);
  let token = Token::word(word, offset, index);

  (token, word.len())
}

fn extract_word<'a>(input: &'a str, delimiters: &'a [char]) -> &'a str {
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
      index: 0,
    };
    assert_eq!(char_token.is_character(), true);

    let word_token = Token {
      kind: TokenKind::Word("a".to_string()),
      start: 0,
      index: 0,
    };
    assert_eq!(word_token.is_character(), false);
  }

  #[test]
  fn is_word() {
    let word_token = Token {
      kind: TokenKind::Word("a".to_string()),
      start: 0,
      index: 0,
    };
    assert_eq!(word_token.is_word(), true);

    let char_token = Token {
      kind: TokenKind::Character('a'),
      start: 0,
      index: 0,
    };
    assert_eq!(char_token.is_word(), false);
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
  fn handles_multiple_whitespace_with_chars() {
    let mut string_tokenizer = StringTokenizer::new(" a ");
    string_tokenizer.ordinary_char('a');

    let result = string_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 1);
    assert_eq!(result.get(0), Some(&Token::character('a', 1, 0)));
  }

  #[test]
  fn handles_multiple_whitespace_with_word() {
    let string_tokenizer = StringTokenizer::new(" hello world ");

    let result = string_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 1, 0)));
    assert_eq!(result.get(1), Some(&Token::word("world", 7, 1)));
  }

  #[test]
  fn handles_whitespace_with_word() {
    let string_tokenizer = StringTokenizer::new("hello world");

    let result = string_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 0, 0)));
    assert_eq!(result.get(1), Some(&Token::word("world", 6, 1)));
  }

  #[test]
  fn handles_new_line() {
    let string_tokenizer = StringTokenizer::new("hello \n world");

    let result = string_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 0, 0)));
    assert_eq!(result.get(1), Some(&Token::word("world", 8, 1)));
  }

  #[test]
  fn handle_flags_chars_word() {
    let string_tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8}\u{1F1EE}\u{1F1F4}");

    let result = string_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 1);
    assert_eq!(
      result.get(0),
      Some(&Token::word("\u{1F1F7}\u{1F1F8}\u{1F1EE}\u{1F1F4}", 0, 0))
    );
  }

  #[test]
  fn handle_flags_with_ordinary_flag() {
    let mut string_tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8}\u{1F1EE}\u{1F1F4}");
    string_tokenizer.ordinary_char('\u{1F1F8}');

    let result = string_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get(0), Some(&Token::word("\u{1F1F7}", 0, 0)));
    assert_eq!(result.get(1), Some(&Token::character('\u{1F1F8}', 4, 1)));
    assert_eq!(
      result.get(2),
      Some(&Token::word("\u{1F1EE}\u{1F1F4}", 8, 2))
    );
  }

  #[test]
  fn handle_flags_with_multiple_ordinary_char() {
    let mut string_tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8}a\u{1F1EE}b\u{1F1F4}");
    string_tokenizer.ordinary_char('a');
    string_tokenizer.ordinary_char('b');

    let result = string_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 5);
    assert_eq!(
      result.get(0),
      Some(&Token::word("\u{1F1F7}\u{1F1F8}", 0, 0))
    );
    assert_eq!(result.get(1), Some(&Token::character('a', 8, 1)));
    assert_eq!(result.get(2), Some(&Token::word("\u{1F1EE}", 9, 2)));
    assert_eq!(result.get(3), Some(&Token::character('b', 13, 3)));
    assert_eq!(result.get(4), Some(&Token::word("\u{1F1F4}", 14, 4)));
  }

  #[test]
  fn handle_flags_with_multiple_whitespaces() {
    let string_tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8} \u{1F1EE}\n\u{1F1F4}");

    let result = string_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 3);
    assert_eq!(
      result.get(0),
      Some(&Token::word("\u{1F1F7}\u{1F1F8}", 0, 0))
    );
    assert_eq!(result.get(1), Some(&Token::word("\u{1F1EE}", 9, 1)));
    assert_eq!(result.get(2), Some(&Token::word("\u{1F1F4}", 14, 2)));
  }

  #[test]
  fn handle_chinese_char() {
    let string_tokenizer = StringTokenizer::new("hello ⼦");

    let result = string_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 0, 0)));
    assert_eq!(result.get(1), Some(&Token::word("⼦", 6, 1)));
  }

  #[test]
  fn handle_chinese_ordinary_char() {
    let mut string_tokenizer = StringTokenizer::new("hello ⼦");
    string_tokenizer.ordinary_char('⼦');

    let result = string_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 0, 0)));
    assert_eq!(result.get(1), Some(&Token::character('⼦', 6, 1)));
  }
}

#[cfg(test)]
mod stream_tokenizer_tests {
  use crate::{StreamTokenizer, Token};
  use std::io::Cursor;

  #[test]
  fn handles_multiple_lines_with_whitespace() {
    let result =
      StreamTokenizer::new(&mut Cursor::new(" \n\u{2000}\n \n ")).collect::<Vec<Token>>();
    assert_eq!(result.len(), 0);
  }

  #[test]
  fn handles_multiple_whitespace_with_chars() {
    let cursor = &mut Cursor::new(" a ");

    let mut stream_tokenizer = StreamTokenizer::new(cursor);
    stream_tokenizer.ordinary_char('a');

    let result = stream_tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 1);
    assert_eq!(result.get(0), Some(&Token::character('a', 1, 0)));
  }

  #[test]
  fn handles_multiple_whitespace_with_word() {
    let result = StreamTokenizer::new(&mut Cursor::new(" hello world ")).collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 1, 0)));
    assert_eq!(result.get(1), Some(&Token::word("world", 7, 1)));
  }

  #[test]
  fn handles_multiple_lines_with_words() {
    let result = StreamTokenizer::new(&mut Cursor::new(" hello \n world ")).collect::<Vec<Token>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&Token::word("hello", 1, 0)));
    assert_eq!(result.get(1), Some(&Token::word("world", 9, 1)));
  }

  #[test]
  fn handles_multiple_lines_with_words_and_ordinary_chars() {
    let cursor = &mut Cursor::new(" hello \n world \n\n!");

    let mut tokenizer = StreamTokenizer::new(cursor);
    tokenizer.ordinary_char('!');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get(0), Some(&Token::word("hello", 1, 0)));
    assert_eq!(result.get(1), Some(&Token::word("world", 9, 1)));
    assert_eq!(result.get(2), Some(&Token::character('!', 17, 2)));
  }

  #[test]
  fn handles_multiple_lines_with_flag_chars() {
    let cursor = &mut Cursor::new("\u{1F1EE}\n\n\u{1F1EE}\u{1F1F8}\n\u{1F1F7}\u{1F1F8}");

    let mut tokenizer = StreamTokenizer::new(cursor);
    tokenizer.ordinary_char('\u{1F1EE}');

    let result = tokenizer.collect::<Vec<Token>>();
    assert_eq!(result.len(), 4);
    assert_eq!(result.get(0), Some(&Token::character('\u{1F1EE}', 0, 0)));
    assert_eq!(result.get(1), Some(&Token::character('\u{1F1EE}', 6, 1)));
    assert_eq!(result.get(2), Some(&Token::word("\u{1F1F8}", 10, 2)));
    assert_eq!(
      result.get(3),
      Some(&Token::word("\u{1F1F7}\u{1F1F8}", 15, 3))
    );
  }
}
