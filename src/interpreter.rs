use std::collections::{HashMap, HashSet};
use std::iter::{Peekable, repeat};
use std::mem::swap;
use std::str::Chars;

pub struct Interpreter {
    pub variables: HashMap<String, f32>,
    pub functions: HashMap<String, (Vec<String>, Ast)>,
}

impl Interpreter {
    pub fn new() -> Interpreter {
        Interpreter { variables: HashMap::new(), functions: HashMap::new() }
    }

    pub fn input(&mut self, input: &str) -> Result<Option<f32>, String> {
        let funcs = self.functions.iter().map(|(k, v)| (k.clone(), v.0.len())).collect();
        let mut parser = Parser::new(Lexer::new(input), funcs);

        if parser.lexer.peek().is_none() {
            return Ok(None);
        }

        let func = parser.lexer.peek() == Some(&Fn);

        let ast = if func {
            parser.parse_func()?
        } else {
            parser.parse_expr()?
        };

        if parser.lexer.peek().is_some() {
            return Err(format!("expected Eof, got `{:?}`", parser.lexer.collect::<Vec<_>>()));
        }

        let ret = self.eval(ast);

        if func {
            ret.map(|_| None)
        } else {
            ret.map(|x| Some(x))
        }
    }

    pub fn eval(&mut self, expr: Ast) -> Result<f32, String> {
        match expr {
            Const(num) => Ok(num),
            Var(name) => self.variables.get(&name)
                .cloned().ok_or(format!("unknown variable `{}`", name)),
            Bin(lhs, op, rhs) => Ok(match op {
                '+' => self.eval(*lhs)? + self.eval(*rhs)?,
                '-' => self.eval(*lhs)? - self.eval(*rhs)?,
                '*' => self.eval(*lhs)? * self.eval(*rhs)?,
                '/' => self.eval(*lhs)? / self.eval(*rhs)?,
                '%' => self.eval(*lhs)? % self.eval(*rhs)?,
                _ => unreachable!(),
            }),
            Assign(name, expr) => {
                if self.functions.contains_key(&name) {
                    return Err(format!("existing function with name `{}`", name));
                }
                let value = self.eval(*expr)?;
                self.variables.insert(name, value);
                Ok(value)
            }
            Call(name, args) => {
                let (argn, body) = self.functions.get(&name)
                    .cloned().ok_or(format!("unknown function `{}`", name))?;
                let mut vars = HashMap::new();
                for (arg, expr) in argn.iter().cloned().zip(args) {
                    vars.insert(arg, self.eval(expr)?);
                }
                swap(&mut self.variables, &mut vars);
                let ret = self.eval(body);
                self.variables = vars;
                ret
            }
            Func(name, args, expr) => {
                if self.variables.contains_key(&name) {
                    return Err(format!("existing variable with name `{}`", name));
                }
                let len = args.len();
                if len > args.iter().collect::<HashSet<_>>().len() {
                    return Err(format!("duplicate arguments"));
                }
                self.functions.insert(name.clone(), (args, *expr));
                let ret = self.eval(Call(name.clone(), repeat(Const(0.0)).take(len).collect()));
                if ret.is_err() {
                    self.functions.remove(&name);
                }
                ret
            }
        }
    }
}

use self::Token::*;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Token {
    Ident(String),
    Num(String),
    InValid(String),
    BinOp(char),
    OpenParen,
    CloseParen,
    FatArrow,
    Eq,
    Fn,
}

#[derive(Debug)]
pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Lexer<'a> {
        Lexer { input: input.chars().peekable() }
    }

    pub fn take_while<P: FnMut(&char) -> bool>(&mut self, mut predicate: P) -> String {
        let mut ret = String::new();
        while let Some(c) = self.input.peek().cloned() {
            if !predicate(&c) {
                break;
            }
            self.input.next();
            ret.push(c);
        }
        ret
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        self.take_while(|c| c.is_whitespace());
        let mut ret = None;
        if let Some(c) = self.input.peek().cloned() {
            match c {
                c if c.is_alphabetic() => {
                    let ident = self.take_while(|c| c.is_alphanumeric() || c == &'_');
                    if ident == "fn" {
                        ret = Some(Fn);
                    } else {
                        ret = Some(Ident(ident));
                    }
                }
                c if c.is_digit(10) => ret = Some(Num(self.take_while(|c| c.is_digit(10) || c == &'.'))),
                '+' | '-' | '*' | '/' | '%' => {
                    self.input.next();
                    ret = Some(BinOp(c));
                }
                '(' => {
                    self.input.next();
                    ret = Some(OpenParen);
                }
                ')' => {
                    self.input.next();
                    ret = Some(CloseParen);
                }
                '=' => {
                    self.input.next();
                    if let Some(&'>') = self.input.peek() {
                        self.input.next();
                        ret = Some(FatArrow);
                    } else {
                        ret = Some(Eq);
                    }
                }
                _ => ret = Some(InValid(format!("invalid token {}",
                                                self.take_while(|c| c.is_alphanumeric() || c == &'_')))),
            }
        }
        ret
    }
}

use self::Ast::*;

#[derive(Clone, Debug)]
pub enum Ast {
    Const(f32),
    Var(String),
    Bin(Box<Ast>, char, Box<Ast>),
    Assign(String, Box<Ast>),
    Call(String, Vec<Ast>),
    Func(String, Vec<String>, Box<Ast>),
}

struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
    funcs: HashMap<String, usize>,
}

impl<'a> Parser<'a> {
    fn new(lexer: Lexer<'a>, funcs: HashMap<String, usize>) -> Parser<'a> {
        Parser { lexer: lexer.peekable(), funcs: funcs }
    }

    fn prec(&mut self) -> i32 {
        match self.lexer.peek() {
            Some(&BinOp(ref op)) => {
                match op.clone() {
                    '*' | '/' | '%' => 3,
                    '+' | '-' => 2,
                    _ => 1,
                }
            }
            _ => 0,
        }
    }

    fn parse_expr(&mut self) -> Result<Ast, String> {
        let lhs = self.parse_factor()?;
        self.parse_expr_rhs(lhs, 0)
    }

    fn parse_expr_rhs(&mut self, lhs: Ast, lhs_prec: i32) -> Result<Ast, String> {
        let prec = self.prec();
        if prec <= lhs_prec {
            return Ok(lhs);
        }
        let op = match self.lexer.next() {
            Some(BinOp(op)) => op,
            e => return Err(format!("expected BinOp, got `{:?}`", e)),
        };
        let rhs = self.parse_factor()?;
        let next_prec = self.prec();
        if prec < next_prec {
            return Ok(Bin(Box::new(lhs), op, Box::new(self.parse_expr_rhs(rhs, prec)?)));
        }
        self.parse_expr_rhs(Bin(Box::new(lhs), op, Box::new(rhs)), 0)
    }

    fn parse_factor(&mut self) -> Result<Ast, String> {
        match self.lexer.next() {
            Some(Num(num)) => Ok(Const(num.parse().unwrap())),
            Some(OpenParen) => {
                let expr = self.parse_expr()?;
                match self.lexer.next() {
                    Some(CloseParen) => (),
                    e => return Err(format!("expected CloseParen, got `{:?}`", e)),
                }
                Ok(expr)
            }
            Some(Ident(ident)) => {
                if let Some(&Eq) = self.lexer.peek() {
                    self.lexer.next();
                    let expr = self.parse_expr()?;
                    return Ok(Assign(ident, Box::new(expr)));
                }
                if let Some(argc) = self.funcs.get(&ident).cloned() {
                    let mut args = Vec::new();
                    for _ in 0..argc {
                        args.push(self.parse_expr()?)
                    }
                    return Ok(Call(ident, args));
                }
                Ok(Var(ident))
            }
            Some(InValid(m)) => Err(m),
            e => Err(format!("expected Factor, got `{:?}`", e)),
        }
    }

    fn parse_func(&mut self) -> Result<Ast, String> {
        match self.lexer.next() {
            Some(Fn) => (),
            e => return Err(format!("expected Fn, got `{:?}`", e)),
        }
        let name = match self.lexer.next() {
            Some(Ident(name)) => name,
            e => return Err(format!("expected Ident, got `{:?}`", e)),
        };
        let mut args = Vec::new();
        while let Some(Ident(arg)) = self.lexer.peek().cloned() {
            self.lexer.next();
            args.push(arg);
        }
        match self.lexer.next() {
            Some(FatArrow) => (),
            e => return Err(format!("expected FatArrow, got `{:?}`", e)),
        }
        Ok(Func(name, args, Box::new(self.parse_expr()?)))
    }
}

#[test]
fn basic_arithmetic() {
    let mut i = Interpreter::new();
    assert_eq!(i.input("1 + 1"), Ok(Some(2.0)));
    assert_eq!(i.input("2 - 1"), Ok(Some(1.0)));
    assert_eq!(i.input("2 * 3"), Ok(Some(6.0)));
    assert_eq!(i.input("8 / 4"), Ok(Some(2.0)));
    assert_eq!(i.input("7 % 4"), Ok(Some(3.0)));
}

#[test]
fn variables() {
    let mut i = Interpreter::new();
    assert_eq!(i.input("x = 1"), Ok(Some(1.0)));
    assert_eq!(i.input("x"), Ok(Some(1.0)));
    assert_eq!(i.input("x + 3"), Ok(Some(4.0)));
    assert!(i.input("y").is_err());
}

#[test]
fn functions() {
    let mut i = Interpreter::new();
    assert_eq!(i.input("fn avg x y => (x + y) / 2"), Ok(None));
    assert_eq!(i.input("avg 4 2"), Ok(Some(3.0)));
    assert!(i.input("avg 7").is_err());
    assert!(i.input("avg 7 2 4").is_err());
}

#[test]
fn conflicts() {
    let mut i = Interpreter::new();
    assert_eq!(i.input("x = 1"), Ok(Some(1.0)));
    assert_eq!(i.input("fn avg x y => (x + y) / 2"), Ok(None));
    assert!(i.input("fn x => 0").is_err());
    assert!(i.input("avg = 5").is_err());
}