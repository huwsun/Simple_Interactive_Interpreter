//extern crate regex;

//use regex::Regex;
#![allow(unused_assignments)]
mod interpreter;
use interpreter::{Interpreter,Lexer};

fn main() {


    //let s="[x] x+2*5";
    let mut c = Interpreter::new();


    //let tokens = c.tokenize("");

      match c.input("fn echo _x => _x ") {
          Ok(v) => { println!("successful value:{:?}", v) }
          Err(e) => println!("error:{}", e)
      };

      println!("vars:{:?}", c.variables);
      println!("functions:{:?}", c.functions);

    let l=Lexer::new("fn add _x1 y2 => (x + y)/2").peekable();
    println!("lexer:{:?}",l);

    for c in l {
        println!("{:?}",c);
    }

    /*
          match c.input("y_2 = 6") {
              Ok(v) => { println!("successful value:{:?}", v) }
              Err(e) => println!("error:{}", e)
          };

          println!("vars:{:?}", c.vars);
          println!("functions:{:?}", c.funs);

          match c.input("fn echo x => x") {
              Ok(v) => { println!("successful value:{:?}", v) }
              Err(e) => println!("error:{}", e)
          };

          println!("vars:{:?}", c.vars);
          println!("functions:{:?}", c.funs);

          match c.input("echo y") {
              Ok(v) => { println!("successful value:{:?}", v) }
              Err(e) => println!("error:{}", e)
          };

          println!("vars:{:?}", c.vars);
          println!("functions:{:?}", c.funs);

          match c.input("fn add x y => x+y") {
              Ok(v) => { println!("successful value:{:?}", v) }
              Err(e) => println!("error:{}", e)
          };

          println!("vars:{:?}", c.vars);
          println!("functions:{:?}", c.funs);

          match c.input("add (echo 4) (echo 3)") {
              Ok(v) => { println!("successful value:{:?}", v) }
              Err(e) => println!("error:{}", e)
          };

          println!("vars:{:?}", c.vars);
          println!("functions:{:?}", c.funs);*/
}

