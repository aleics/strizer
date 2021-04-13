use std::fmt;
use std::io::BufRead;
use std::ops::Range;

/// `Span` defines the absolute range of a [`Token`] inside the input data.
///
/// [`Token`]: struct.Token.html
pub type Span = Range<usize>;

/// `TokenKind` defines the different types of [`Token`] available.
///
/// [`Token`]: struct.Token.html
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TokenKind {
  Character(char),
  Word,
}

impl From<char> for TokenKind {
  fn from(character: char) -> Self {
    TokenKind::Character(character)
  }
}

impl fmt::Display for TokenKind {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      TokenKind::Character(char) => write!(f, "Character({})", char),
      TokenKind::Word => write!(f, "Word"),
    }
  }
}

/// `Token` describes the primitive that is returned while iterating through a Tokenizer.
/// Tokens can be of different type or kind:
///
///  * [`TokenKind::Character`]
///  * [`TokenKind::Word`].
///
/// The associated data is stored in the Token, along with its start position (in bytes).
///
/// [`TokenKind::Character`]: enum.TokenKind.html#variant.Character
/// [`TokenKind::Word`]: enum.TokenKind.html#variant.Word
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Token {
  kind: TokenKind,
}

impl Token {
  /// Returns token's kind
  pub fn kind(&self) -> &TokenKind {
    &self.kind
  }

  /// Creates a character token with a given start position (in bytes).
  pub fn character(character: char) -> Token {
    Token {
      kind: TokenKind::from(character),
    }
  }

  /// Returns `true` if the `Token` is [`TokenKind::Character`]
  ///
  /// [`TokenKind::Character`]: enum.TokenKind.html#variant.Character
  pub fn is_character(&self) -> bool {
    matches!(self.kind, TokenKind::Character(_))
  }

  /// Returns `true` if the `Token` is [`TokenKind::Character`] and equal to the `input` character.
  ///
  /// [`TokenKind::Character`]: enum.TokenKind.html#variant.Character
  pub fn is_character_equal(&self, input: char) -> bool {
    if let TokenKind::Character(character) = self.kind {
      character == input
    } else {
      false
    }
  }

  /// Creates a word token
  pub fn word() -> Token {
    Token {
      kind: TokenKind::Word,
    }
  }

  /// Returns `true` if the `Token` is [`TokenKind::Word`]
  ///
  /// [`TokenKind::Word`]: enum.TokenKind.html#variant.Word
  pub fn is_word(&self) -> bool {
    matches!(self.kind, TokenKind::Word)
  }
}

impl fmt::Display for Token {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "kind: {}", self.kind)
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
///   let error_count = StreamTokenizer::new(&mut reader, &[])
///     .filter(|(_, _, slice)| slice == "ERROR")
///     .count();
///
///   println!("number of error logs: {}", error_count);
///   Ok(())
/// }
/// ```
///
/// [`BufRead`]: https://doc.rust-lang.org/std/io/trait.BufRead.html
#[derive(Debug)]
pub struct StreamTokenizer<'a, R> {
  input: &'a mut R,
  current_line: Option<String>,
  line_offset: usize,
  offset: usize,
  identifiers: &'a [char],
}

impl<'a, R: BufRead> StreamTokenizer<'a, R> {
  /// Creates a new `StreamTokenizer<R>` with a given [`BufRead`] input. The different offsets
  /// and data used while iterating are initialized. An array of `identifiers` is passed by, and
  /// the associated characters will be identified as `Character` [`Token`] during the tokenization.
  ///
  ///
  /// # Examples
  ///
  /// ```
  /// use std::io::Cursor;
  /// use strizer::{StreamTokenizer, Token, TokenKind};
  ///
  /// let cursor = &mut Cursor::new("abracadabra");
  /// let tokenizer = StreamTokenizer::new(cursor, &['a']);
  ///
  /// let a_count = tokenizer
  ///   .filter(|(token, _, slice)| token.is_character() && slice == "a")
  ///   .count();
  ///
  /// assert_eq!(a_count, 5);
  /// ```
  ///
  /// [`BufRead`]: https://doc.rust-lang.org/std/io/trait.BufRead.html
  /// [`Token`]: struct.Token.html
  pub fn new(input: &'a mut R, identifiers: &'a [char]) -> Self {
    StreamTokenizer {
      input,
      current_line: None,
      line_offset: 0,
      offset: 0,
      identifiers,
    }
  }

  /// Create a slice of the input by a defined length
  fn slice(&self, line: &str, length: usize) -> String {
    let start = self.line_offset;
    let end = self.line_offset + length;

    line[start..end].to_owned()
  }

  // Create a span range of the current position and a token length
  fn span(&self, length: usize) -> Span {
    let start = self.offset;
    let end = self.offset + length;

    start..end
  }

  /// Reads the next line from the inner [`BufRead`]. Returns `None` if the line couldn't be read
  /// or the buffer has reached end of file.
  ///
  /// [`BufRead`]: https://doc.rust-lang.org/std/io/trait.BufRead.html
  fn read_line(&mut self) -> Option<String> {
    let mut buf = String::new();
    let bytes = self.input.read_line(&mut buf).ok()?;

    (bytes > 0).then(|| buf)
  }
}

/// [`StreamTokenizer<R>`] implementation for [`Iterator`].
impl<'a, R: BufRead> Iterator for StreamTokenizer<'a, R> {
  type Item = (Token, Span, String);

  fn next(&mut self) -> Option<Self::Item> {
    if self.current_line.is_none() {
      self.current_line = self.read_line();
    }

    while let Some(line) = &self.current_line {
      for character in line[self.line_offset..].chars() {
        let (extraction, length) =
          extract_token(&line[self.line_offset..], character, &self.identifiers);

        let range = self.span(length);
        let slice = self.slice(line, length);

        self.offset += length;
        self.line_offset += length;

        if let Some(token) = extraction {
          return Some((token, range, slice));
        }
      }

      self.current_line = self.read_line();
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
/// let token_count = StringTokenizer::new("hello world", &[]).count();
/// assert_eq!(token_count, 2);
/// ```
#[derive(Copy, Clone, Debug)]
pub struct StringTokenizer<'a> {
  input: &'a str,
  offset: usize,
  identifiers: &'a [char],
}

impl<'a> StringTokenizer<'a> {
  /// Creates a new `StringTokenizer` with a given string input. The different offsets
  /// and data used while iterating is also initialized.
  /// # Examples
  ///
  /// ```
  /// use std::io::Cursor;
  /// use strizer::{StringTokenizer, Token, TokenKind};
  ///
  /// let tokenizer = StringTokenizer::new("abracadabra", &['a']);
  ///
  /// let a_count = tokenizer
  ///   .filter(|(token, _, slice)| token.is_character() && slice == &"a")
  ///   .count();
  ///
  /// assert_eq!(a_count, 5);
  /// ```
  pub fn new(input: &'a str, identifiers: &'a [char]) -> Self {
    StringTokenizer {
      input,
      offset: 0,
      identifiers,
    }
  }

  /// Create a slice of the input by a defined length
  fn slice(&self, length: usize) -> &'a str {
    let start = self.offset;
    let end = self.offset + length;

    &self.input[start..end]
  }

  // Create a span range of the current position and a token length
  fn span(&self, length: usize) -> Span {
    let start = self.offset;
    let end = self.offset + length;

    start..end
  }
}

/// [`StringTokenizer`] implementation for [`Iterator`].
impl<'a> Iterator for StringTokenizer<'a> {
  type Item = (Token, Span, &'a str);

  fn next(&mut self) -> Option<Self::Item> {
    for character in self.input[self.offset..].chars() {
      let (extraction, length) =
        extract_token(&self.input[self.offset..], character, &self.identifiers);

      let range = self.span(length);
      let slice = self.slice(length);

      self.offset += length;

      if let Some(token) = extraction {
        return Some((token, range, slice));
      }
    }
    None
  }
}

fn extract_token(input: &str, character: char, identifiers: &[char]) -> (Option<Token>, usize) {
  if identifiers.contains(&character) {
    (Some(Token::character(character)), character.len_utf8())
  } else if character.is_whitespace() {
    (None, character.len_utf8())
  } else {
    let chunk = extract_chunk(input, identifiers);
    (Some(Token::word()), chunk.len())
  }
}

fn extract_chunk<'a>(input: &'a str, identifiers: &'a [char]) -> &'a str {
  input
    .char_indices()
    .find(|(_, c)| c.is_whitespace() || identifiers.contains(c))
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
    };
    assert_eq!(char_token.is_character(), true);

    let word_token = Token {
      kind: TokenKind::Word,
    };
    assert_eq!(word_token.is_character(), false);
  }

  #[test]
  fn is_character_equal() {
    let char_token = Token {
      kind: TokenKind::Character('a'),
    };
    assert_eq!(char_token.is_character_equal('a'), true);
    assert_eq!(char_token.is_character_equal('b'), false);
  }

  #[test]
  fn is_word() {
    let word_token = Token {
      kind: TokenKind::Word,
    };
    assert_eq!(word_token.is_word(), true);

    let char_token = Token {
      kind: TokenKind::Character('a'),
    };
    assert_eq!(char_token.is_word(), false);
  }
}

#[cfg(test)]
mod string_tokenizer_tests {
  use crate::{Span, StringTokenizer, Token};

  #[test]
  fn handles_whitespace() {
    let result = StringTokenizer::new(" ", &[]).collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 0);
  }

  #[test]
  fn handle_custom_whitespace() {
    let result = StringTokenizer::new("\u{2000}", &[]).collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 0);
  }

  #[test]
  fn handles_multiple_whitespace() {
    let result = StringTokenizer::new("  ", &[]).collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 0);
  }

  #[test]
  fn handles_whitespace_as_char() {
    let tokenizer = StringTokenizer::new(" ", &[' ']);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 1);
    assert_eq!(result.get(0), Some(&(Token::character(' '), 0..1, " ")));
  }

  #[test]
  fn handles_multiple_whitespace_with_chars() {
    let tokenizer = StringTokenizer::new(" a ", &['a']);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 1);
    assert_eq!(result.get(0), Some(&(Token::character('a'), 1..2, "a")));
  }

  #[test]
  fn handles_multiple_whitespace_with_word() {
    let tokenizer = StringTokenizer::new(" hello world ", &[]);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&(Token::word(), 1..6, "hello")));
    assert_eq!(result.get(1), Some(&(Token::word(), 7..12, "world")));
  }

  #[test]
  fn handles_whitespace_with_word() {
    let tokenizer = StringTokenizer::new("hello world", &[]);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&(Token::word(), 0..5, "hello")));
    assert_eq!(result.get(1), Some(&(Token::word(), 6..11, "world")));
  }

  #[test]
  fn handles_new_line() {
    let tokenizer = StringTokenizer::new("hello \n world", &[]);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&(Token::word(), 0..5, "hello")));
    assert_eq!(result.get(1), Some(&(Token::word(), 8..13, "world")));
  }

  #[test]
  fn handle_flags_chars_word() {
    let tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8}\u{1F1EE}\u{1F1F4}", &[]);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 1);
    assert_eq!(
      result.get(0),
      Some(&(Token::word(), 0..16, "\u{1F1F7}\u{1F1F8}\u{1F1EE}\u{1F1F4}"))
    );
  }

  #[test]
  fn handle_flags_with_flag_identifier() {
    let tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8}\u{1F1EE}\u{1F1F4}", &['\u{1F1F8}']);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 3);
    assert_eq!(result.get(0), Some(&(Token::word(), 0..4, "\u{1F1F7}")));
    assert_eq!(
      result.get(1),
      Some(&(Token::character('\u{1F1F8}'), 4..8, "\u{1F1F8}"))
    );
    assert_eq!(
      result.get(2),
      Some(&(Token::word(), 8..16, "\u{1F1EE}\u{1F1F4}"))
    );
  }

  #[test]
  fn handle_flags_with_multiple_identifiers() {
    let tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8}a\u{1F1EE}b\u{1F1F4}", &['a', 'b']);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 5);
    assert_eq!(
      result.get(0),
      Some(&(Token::word(), 0..8, "\u{1F1F7}\u{1F1F8}"))
    );
    assert_eq!(result.get(1), Some(&(Token::character('a'), 8..9, "a")));
    assert_eq!(result.get(2), Some(&(Token::word(), 9..13, "\u{1F1EE}")));
    assert_eq!(result.get(3), Some(&(Token::character('b'), 13..14, "b")));
    assert_eq!(result.get(4), Some(&(Token::word(), 14..18, "\u{1F1F4}")));
  }

  #[test]
  fn handle_flags_with_multiple_whitespaces() {
    let tokenizer = StringTokenizer::new("\u{1F1F7}\u{1F1F8} \u{1F1EE}\n\u{1F1F4}", &[]);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 3);
    assert_eq!(
      result.get(0),
      Some(&(Token::word(), 0..8, "\u{1F1F7}\u{1F1F8}"))
    );
    assert_eq!(result.get(1), Some(&(Token::word(), 9..13, "\u{1F1EE}")));
    assert_eq!(result.get(2), Some(&(Token::word(), 14..18, "\u{1F1F4}")));
  }

  #[test]
  fn handle_chinese_char() {
    let tokenizer = StringTokenizer::new("hello ⼦", &[]);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&(Token::word(), 0..5, "hello")));
    assert_eq!(result.get(1), Some(&(Token::word(), 6..9, "⼦")));
  }

  #[test]
  fn handle_chinese_identifier() {
    let tokenizer = StringTokenizer::new("hello ⼦", &['⼦']);

    let result = tokenizer.collect::<Vec<(Token, Span, &str)>>();
    assert_eq!(result.len(), 2);
    assert_eq!(result.get(0), Some(&(Token::word(), 0..5, "hello")));
    assert_eq!(result.get(1), Some(&(Token::character('⼦'), 6..9, "⼦")));
  }
}

#[cfg(test)]
mod tests {
  use std::io::Cursor;

  use crate::{Span, StreamTokenizer, Token};

  #[test]
  fn handles_multiple_lines_with_whitespace() {
    let result =
      StreamTokenizer::new(&mut Cursor::new(" \n\u{2000}\n \n "), &[])
        .collect::<Vec<(Token, Span, String)>>();
    assert_eq!(result.len(), 0);
  }

  #[test]
  fn handles_multiple_whitespace_with_chars() {
    let result =
      StreamTokenizer::new(&mut Cursor::new(" a "), &['a']).collect::<Vec<(Token, Span, String)>>();
    assert_eq!(result.len(), 1);
    assert_eq!(
      result.get(0),
      Some(&(Token::character('a'), 1..2, "a".to_string()))
    );
  }

  #[test]
  fn handles_multiple_whitespace_with_word() {
    let result =
      StreamTokenizer::new(&mut Cursor::new(" hello world "), &[])
        .collect::<Vec<(Token, Span, String)>>();
    assert_eq!(result.len(), 2);
    assert_eq!(
      result.get(0),
      Some(&(Token::word(), 1..6, "hello".to_string()))
    );
    assert_eq!(
      result.get(1),
      Some(&(Token::word(), 7..12, "world".to_string()))
    );
  }

  #[test]
  fn handles_multiple_lines_with_words() {
    let result =
      StreamTokenizer::new(&mut Cursor::new(" hello \n world "), &[])
        .collect::<Vec<(Token, Span, String)>>();
    assert_eq!(result.len(), 2);
    assert_eq!(
      result.get(0),
      Some(&(Token::word(), 1..6, "hello".to_string()))
    );
    assert_eq!(
      result.get(1),
      Some(&(Token::word(), 9..14, "world".to_string()))
    );
  }

  #[test]
  fn handles_multiple_lines_with_words_and_identifiers() {
    let result = StreamTokenizer::new(&mut Cursor::new(" hello \n world \n\n!"), &['!'])
      .collect::<Vec<(Token, Span, String)>>();
    assert_eq!(result.len(), 3);
    assert_eq!(
      result.get(0),
      Some(&(Token::word(), 1..6, "hello".to_string()))
    );
    assert_eq!(
      result.get(1),
      Some(&(Token::word(), 9..14, "world".to_string()))
    );
    assert_eq!(
      result.get(2),
      Some(&(Token::character('!'), 17..18, "!".to_string()))
    );
  }

  #[test]
  fn handles_multiple_lines_with_flag_chars() {
    let result = StreamTokenizer::new(
      &mut Cursor::new("\u{1F1EE}\n\n\u{1F1EE}\u{1F1F8}\n\u{1F1F7}\u{1F1F8}"),
      &['\u{1F1EE}'],
    )
    .collect::<Vec<(Token, Span, String)>>();
    assert_eq!(result.len(), 4);
    assert_eq!(
      result.get(0),
      Some(&(Token::character('\u{1F1EE}'), 0..4, "\u{1F1EE}".to_string()))
    );
    assert_eq!(
      result.get(1),
      Some(&(
        Token::character('\u{1F1EE}'),
        6..10,
        "\u{1F1EE}".to_string()
      ))
    );
    assert_eq!(
      result.get(2),
      Some(&(Token::word(), 10..14, "\u{1F1F8}".to_string()))
    );
    assert_eq!(
      result.get(3),
      Some(&(Token::word(), 15..23, "\u{1F1F7}\u{1F1F8}".to_string()))
    );
  }

  #[test]
  fn handle_multiple_lines_numbers_with_identifiers() {
    let cursor = &mut Cursor::new("1.1\n2\n\n-3\n-4.4");
    let tokenizer = StreamTokenizer::new(cursor, &['-']);

    let result = tokenizer.collect::<Vec<(Token, Span, String)>>();
    assert_eq!(result.len(), 6);
    assert_eq!(
      result.get(0),
      Some(&(Token::word(), 0..3, "1.1".to_string()))
    );
    assert_eq!(result.get(1), Some(&(Token::word(), 4..5, "2".to_string())));
    assert_eq!(
      result.get(2),
      Some(&(Token::character('-'), 7..8, "-".to_string()))
    );
    assert_eq!(result.get(3), Some(&(Token::word(), 8..9, "3".to_string())));
    assert_eq!(
      result.get(4),
      Some(&(Token::character('-'), 10..11, "-".to_string()))
    );
    assert_eq!(
      result.get(5),
      Some(&(Token::word(), 11..14, "4.4".to_string()))
    );
  }
}
