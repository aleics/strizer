mod lexer;
mod parser;

use parser::Parser;
use std::io::stdin;

fn main() {
  println!("Welcome to ebooler! A boolean expression parser.");

  loop {
    println!("input: ");
    let mut input = String::new();

    stdin()
      .read_line(&mut input)
      .expect("error: couldn't read user input");

    if let Some(result) = Parser::new(&input).build() {
      println!("\nresult: {}", result.interpret());
    } else {
      println!("\nerror: invalid expression");
    }
  }
}
