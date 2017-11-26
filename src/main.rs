//extern crate regex;

//use regex::Regex;
#![allow(unused_assignments)]
use Ast::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
enum Ast {
    Op(String, Box<Ast>, Box<Ast>),
    Fu(String, HashMap<String, Box<Ast>>),
    Pa(String),
    Im(f32)
}

#[derive(Debug)]
struct Interpreter {
    op: HashMap<String, u8>,
    vars: HashMap<String, f32>,
    funs: HashMap<String, Functions>
}

#[derive(Debug)]
struct Functions {
    params: Vec<String>,
    ast: Ast
}

impl Interpreter {
    fn new() -> Interpreter {
        let mut op = HashMap::new();
        op.insert("=".to_string(), 4);
        op.insert("+".to_string(), 3);
        op.insert("-".to_string(), 3);
        op.insert("*".to_string(), 2);
        op.insert("/".to_string(), 2);
        op.insert("%".to_string(), 2);

        Interpreter { op: op, vars: HashMap::new(), funs: HashMap::new() }
    }

    fn tokenize(&self, s: &str) -> Vec<String> {
        //let re = Regex::new(r"\s*(=>|[\-\+\*/%=\(\)]|[A-Za-z_][A-Za-z0-9_]*|[0-9]*\.?[0-9]+)\s*").unwrap();
        //let tokens_re: Vec<&str> = re.find_iter(s).map(|s| s.as_str().trim()).collect();

        let tokens: Vec<String> = s.replace("(", " ( ")
            .replace(")", " ) ")
            .replace("+"," + ")
            .replace("-"," - ")
            .replace("*"," * ")
            .replace("/"," / ")
            .replace("%"," % ")
            .split_whitespace().map(|s| s.to_string()).collect();


        tokens
    }

    fn input(&mut self, str: &str) -> Result<Option<f32>, String> {
        let tokens = self.tokenize(str);
        let tokens:Vec<&str>=tokens.iter().map(|s|s.as_str()).collect();
        let mut ret: Option<f32> = None;
        if tokens.len() == 0 {
            return Ok(ret);
        }

        if tokens[0] == "fn" {
            self.func_parser(tokens)?;
        } else {
            let (ast, _) = self.exp_parser(tokens)?;
            let scope = HashMap::new();
            ret = Some(self.exec(&ast, &scope)?);
        }

        Ok(ret)
    }

    fn func_parser(&mut self, tokens: Vec<&str>) -> Result<(), String> {
        println!("function tokens:{:?}", tokens);
        let fun_name = tokens[1];
        let mut params: Vec<String> = Vec::new();
        let mut idx = 2;

        if self.vars.contains_key(fun_name) {
            return Err(format!("functio({}): conflicting to global var", fun_name));
        }

        if !tokens.contains(&"=>") {
            return Err(format!("function({}): invalid syntax", fun_name));
        }

        for (i, c) in tokens[idx..].iter().enumerate() {
            match *c {
                s if s == "=>" => {
                    idx = idx + i;
                    break;
                }
                s => {
                    if params.contains(&s.to_string()) {
                        return Err(format!("parameter({}): duplicate", s));
                    } else { params.push(s.to_string()); }
                }
            }
        }
        let (ast, args) = self.exp_parser(tokens[(idx + 1)..].to_vec())?;

        for arg in args {
            if !params.contains(&arg) {
                return Err(format!("arg({}): not a valid parameter", arg));
            }
        }

        self.funs.insert(fun_name.to_string(), Functions { params: params, ast: ast });

        Ok(())
    }

    fn exp_parser(&mut self, tokens: Vec<&str>) -> Result<(Ast, Vec<String>), String> {
        println!("expression token:{:?}", tokens);
        let mut tokens = tokens;
        //let mut exp_flag=true;

        tokens.insert(0, "(");
        tokens.push(")");

        let mut ops = Vec::new();
        let mut ds = Vec::new();

        let mut args: Vec<String> = Vec::new();

        let mut iter = tokens.iter().rev();
        //println!("iter:{:?}", iter);
        while let Some(&s) = iter.next() {
            //println!("token:{}",s);
            match s {
                c if self.op.contains_key(&c.to_string()) => {
                    //println!("op=0>:{}", c);
                    //println!("op=0>ops:{:?}", ops);
                    //println!("op=0>ds:{:?}", ds);
                    loop {
                        if ops.is_empty() || ops.last().unwrap() == ")"
                            || (self.op.get(&c.to_string()) == self.op.get(ops.last().unwrap()) && c != "=")
                            || self.op.get(&c.to_string()) < self.op.get(ops.last().unwrap()) {
                            ops.push(c.to_string());
                            break;
                        } else {
                            let a = ds.pop().unwrap();
                            let b = ds.pop().unwrap();
                            ds.push(Op(ops.pop().unwrap(), Box::new(a), Box::new(b)));
                        }
                    }
                    // exp_flag=true;
                    //println!("op=1>ops:{:?}", ops);
                    //println!("op=1>ds:{:?}", ds);
                }
                "(" => {
                    //println!("(=0>: oprator=>{:?}", ops);

                    //println!("(=0>ds:{:?}", ds);
                    while let Some(p) = ops.pop() {
                        if p == ")".to_string() {
                            break;
                        } else {
                            let a = ds.pop().unwrap();
                            let b = ds.pop().unwrap();
                            ds.push(Op(p, Box::new(a), Box::new(b)));
                        }
                    }

                    //println!("(=1>ds:{:?}", ds);
                }
                c if c == ")" => {
                    ops.push(c.to_string());

                    //println!("(=>: operator=>{:?}", ops);
                }
                c if self.funs.contains_key(c) => {
                    let mut params = HashMap::new();
                    for param in self.funs.get(c).unwrap().params.clone() {
                        match ds.pop() {
                            Some(ast) => {
                                params.insert(param, Box::new(ast));
                            }
                            None => {
                                return Err(format!("call function ({}) not enough parameters", c));
                            }
                        }
                    }
                    ds.push(Fu(c.to_string(), params));
                }
                c if c.parse::<f32>().is_ok() => {
                    ds.push(Im(c.parse::<f32>().unwrap()));
                }
                c => {
                    if !args.contains(&c.to_string()) { args.push(c.to_string()); }
                    ds.push(Pa(c.to_string()));

                    //println!("exp arg:{}", c);
                }
            }

            // println!("datastack=>{:?}", ds);
        }
        println!("args:{:?}", args);
        println!("datastack=>{:?}", ds);
        if ds.len() > 1 || ds.len() == 0 {
            return Err("expression invalid".to_string());
        }

        Ok((ds[0].clone(), args))
    }

    fn exec(&mut self, ast: &Ast, scope: &HashMap<String, f32>) -> Result<f32, String> {
        let mut res = 0.0;
        match ast {
            &Im(n) => {
                res = n;
            }
            &Pa(ref param) => {
                res = self.eval(param, scope)?;
            }
            &Op(ref op, ref lv, ref rv) => {
                let r = self.exec(&rv.clone(), scope)?;
                if op == "=" {
                    match lv.as_ref() {
                        &Pa(ref var) => {
                            self.vars.insert(var.to_string(), r);
                            res = r;
                        }
                        _ => { return Err(format!("can not assign to {:?}", lv)); }
                    }
                } else {
                    let l = self.exec(&lv.clone(), scope)?;

                    match op.as_str() {
                        "+" => res = l + r,
                        "-" => res = l - r,
                        "*" => res = l * r,
                        "/" => res = l / r,
                        "%" => res = l % r,
                        _ => {}
                    }
                }
            }
            &Fu(ref fun_name, ref params) => {
                let mut pms = HashMap::new();
                for (param, ast) in params {
                    pms.insert(param.to_string(), self.exec(&ast, scope)?);
                }
                let ast = self.funs.get(fun_name).unwrap().ast.clone();
                res = self.exec(&ast, &pms)?;
            }
        }
        Ok(res)
    }

    fn eval(&mut self, var: &str, scope: &HashMap<String, f32>) -> Result<f32, String> {
        let mut res = 0.0;
        if scope.contains_key(var) {
            res = *scope.get(var).unwrap();
        } else if self.vars.contains_key(var) {
            res = *self.vars.get(var).unwrap();
        } else {
            return Err(format!("var({}) not exists!", var));
        }

        Ok(res)
    }
}


fn main() {
    //let s="[x] x+2*5";
    let c = Interpreter::new();
    let f = ".23".parse::<f32>();
    match f {
        Ok(n) => println!("{}", n),
        Err(ref e) => println!("error msg:{}", e)
    }

    println!("{:?}", f);
    let tokens = c.tokenize("fn add x y => (x + y) / 2");


    println!("tokens:{:?}", tokens);
    /*  match c.input("x_2 = 4") {
          Ok(v) => { println!("successful value:{:?}", v) }
          Err(e) => println!("error:{}", e)
      };

      println!("vars:{:?}", c.vars);
      println!("functions:{:?}", c.funs);


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
