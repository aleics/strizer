use crate::lexer::{Lexer, Symbol};

pub(crate) trait Expression {
  fn interpret(&self) -> bool;
}

struct TrueExpression;

impl Expression for TrueExpression {
  fn interpret(&self) -> bool {
    true
  }
}

struct FalseExpression;

impl Expression for FalseExpression {
  fn interpret(&self) -> bool {
    false
  }
}

struct NotExpression {
  child: Box<dyn Expression>,
}

impl Expression for NotExpression {
  fn interpret(&self) -> bool {
    !self.child.interpret()
  }
}

struct OrExpression {
  left: Box<dyn Expression>,
  right: Box<dyn Expression>,
}

impl Expression for OrExpression {
  fn interpret(&self) -> bool {
    self.left.interpret() || self.right.interpret()
  }
}

struct AndExpression {
  left: Box<dyn Expression>,
  right: Box<dyn Expression>,
}

impl Expression for AndExpression {
  fn interpret(&self) -> bool {
    self.left.interpret() && self.right.interpret()
  }
}

pub(crate) struct Parser<'a> {
  lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
  pub(crate) fn new(text: &'a str) -> Parser<'a> {
    Parser {
      lexer: Lexer::new(text),
    }
  }

  pub(crate) fn build(&mut self) -> Option<Box<dyn Expression>> {
    self.expression()
  }

  fn expression(&mut self) -> Option<Box<dyn Expression>> {
    let left = self.term()?;
    let op = self
      .lexer
      .next()
      .filter(|op_symbol| op_symbol == &Symbol::And || op_symbol == &Symbol::Or);

    if let Some(op_symbol) = op {
      let right = self.term()?;

      match op_symbol {
        Symbol::Or => Some(Box::new(OrExpression { left, right })),
        Symbol::And => Some(Box::new(AndExpression { left, right })),
        _ => None,
      }
    } else {
      Some(left)
    }
  }

  fn term(&mut self) -> Option<Box<dyn Expression>> {
    match self.lexer.next()? {
      Symbol::True => Some(Box::new(TrueExpression)),
      Symbol::False => Some(Box::new(FalseExpression)),
      Symbol::Not => Some(Box::new(NotExpression {
        child: self.term()?,
      })),
      Symbol::Left => {
        let expression = self.expression();
        self.lexer.next(); // ignore right bracket
        return expression;
      }
      _ => None,
    }
  }
}

#[cfg(test)]
mod tests {
  use crate::parser::Parser;

  #[test]
  fn single_and_expression() {
    let result = Parser::new("false & false").build().unwrap();
    assert_eq!(result.interpret(), false);

    let result = Parser::new("true & false").build().unwrap();
    assert_eq!(result.interpret(), false);

    let result = Parser::new("false & true").build().unwrap();
    assert_eq!(result.interpret(), false);

    let result = Parser::new("true & true").build().unwrap();
    assert_eq!(result.interpret(), true);
  }

  #[test]
  fn combined_and_expression() {
    let result = Parser::new("(true & true) & false").build().unwrap();
    assert_eq!(result.interpret(), false);

    let result = Parser::new("(false & false) & true").build().unwrap();
    assert_eq!(result.interpret(), false);
  }

  #[test]
  fn multiple_combined_and_expressions() {
    let result = Parser::new("(false & false) & (true & true)")
      .build()
      .unwrap();
    assert_eq!(result.interpret(), false);

    let result = Parser::new("(false & false) & (false & false)")
      .build()
      .unwrap();
    assert_eq!(result.interpret(), false);
  }

  #[test]
  fn single_or_expression() {
    let result = Parser::new("false | false").build().unwrap();
    assert_eq!(result.interpret(), false);

    let result = Parser::new("true | false").build().unwrap();
    assert_eq!(result.interpret(), true);

    let result = Parser::new("false | true").build().unwrap();
    assert_eq!(result.interpret(), true);

    let result = Parser::new("true | true").build().unwrap();
    assert_eq!(result.interpret(), true);
  }

  #[test]
  fn combined_or_expression() {
    let result = Parser::new("(false | false) | true").build().unwrap();
    assert_eq!(result.interpret(), true);

    let result = Parser::new("(false | false) | false").build().unwrap();
    assert_eq!(result.interpret(), false);
  }

  #[test]
  fn multiple_combined_or_expressions() {
    let result = Parser::new("(false | false) | (true | true)")
      .build()
      .unwrap();
    assert_eq!(result.interpret(), true);

    let result = Parser::new("(false | false) | (false | false)")
      .build()
      .unwrap();
    assert_eq!(result.interpret(), false);
  }

  #[test]
  fn single_expression_with_brackets() {
    let result = Parser::new("(true & true)").build().unwrap();
    assert_eq!(result.interpret(), true);
  }

  #[test]
  fn single_not_expression() {
    let result = Parser::new("!false").build().unwrap();
    assert_eq!(result.interpret(), true);

    let result = Parser::new("!true").build().unwrap();
    assert_eq!(result.interpret(), false);
  }

  #[test]
  fn single_not_with_expression() {
    let result = Parser::new("!(false | false)").build().unwrap();
    assert_eq!(result.interpret(), true);

    let result = Parser::new("!(true & false)").build().unwrap();
    assert_eq!(result.interpret(), true);
  }

  #[test]
  fn combined_not_and_expression() {
    let result = Parser::new("!false & false").build().unwrap();
    assert_eq!(result.interpret(), false);

    let result = Parser::new("!true & true").build().unwrap();
    assert_eq!(result.interpret(), false);
  }

  #[test]
  fn combined_not_or_expression() {
    let result = Parser::new("!false | false").build().unwrap();
    assert_eq!(result.interpret(), true);

    let result = Parser::new("!true | true").build().unwrap();
    assert_eq!(result.interpret(), true);
  }
}
