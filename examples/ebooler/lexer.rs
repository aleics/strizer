use strizer::{StringTokenizer, TokenKind};

#[derive(Debug, PartialEq)]
pub enum Symbol {
  Or,
  And,
  Not,
  Left,
  Right,
  True,
  False,
}

fn get_character_symbol(character: char) -> Option<Symbol> {
  match character {
    '|' => Some(Symbol::Or),
    '&' => Some(Symbol::And),
    '!' => Some(Symbol::Not),
    '(' => Some(Symbol::Left),
    ')' => Some(Symbol::Right),
    _ => None,
  }
}

fn get_word_symbol(word: &String) -> Option<Symbol> {
  match word.to_uppercase().as_str() {
    "TRUE" => Some(Symbol::True),
    "FALSE" => Some(Symbol::False),
    _ => None,
  }
}

pub(crate) struct Lexer<'a> {
  tokenizer: StringTokenizer<'a>,
}

impl<'a> Lexer<'a> {
  pub(crate) fn new(text: &'a str) -> Lexer<'a> {
    let mut tokenizer = StringTokenizer::new(text);
    tokenizer.ordinary_char('(');
    tokenizer.ordinary_char(')');
    tokenizer.ordinary_char('&');
    tokenizer.ordinary_char('|');
    tokenizer.ordinary_char('!');

    Lexer { tokenizer }
  }
}

impl<'a> Iterator for Lexer<'a> {
  type Item = Symbol;

  fn next(&mut self) -> Option<Self::Item> {
    let token = self.tokenizer.next()?;

    match token.kind {
      TokenKind::Character(character) => get_character_symbol(character),
      TokenKind::Word(word) => get_word_symbol(&word),
    }
  }
}
