use rustyline::error::ReadlineError;
use rustyline::Editor;

use anyhow::{Context, Result};

use lazy_static::lazy_static;

use regex::Regex;

/*
enum Token {
    Spec1(char), // []{}()'`~^@
    Spec2,       // ~@
}
*/

fn main() -> Result<()> {
    let mut ed = Editor::<()>::new()?;

    loop {
        let l = match ed.readline("user> ") {
            Ok(l) => l,
            Err(ReadlineError::Interrupted) => continue,
            Err(ReadlineError::Eof) => break,
            Err(err) => {
                eprintln!("{:?}", err);
                break;
            }
        };

        if l.is_empty() {
            continue;
        }

        let data = match read_str(&l) {
            Ok(data) => data,
            Err(err) => {
                eprintln!("{}", err);
                continue;
            }
        };

        println_data(&data);
    }

    Ok(())
}

fn println_data(data: &Data) {
    print_data(&data);
    println!();
}

fn print_data(data: &Data) {
    use Data::*;

    match &data {
        Nil => print!("nil"),
        Bool(b) => print!("{}", b),
        List(l) => {
            print!("(");

            let mut first = true;
            for each in l {
                if first {
                    first = false;
                } else {
                    print!(" ");
                }

                print_data(&each);
            }

            print!(")");
        }
        Str(s) => {
            print!("\"{}\"", s);
        }
        I64(n) => {
            print!("{}", n);
        }
        Sym(s) => {
            print!("{}", s);
        }
    }
}

fn read_str(text: &str) -> Result<Data> {
    let tokens = tokenize(text);

    let (_, data) = read_form(tokens.iter().peekable())?;

    Ok(data)
}

fn tokenize(text: &str) -> Vec<String> {
    lazy_static! {
        static ref RE: Regex = Regex::new(
            r##"[\s,]*(~@|[\[\]{}()'`~^@]|"(?:\\.|[^\\"])*"?|;.*|[^\s\[\]{}('"`,;)]*)"##
        )
        .unwrap();
    }

    RE.captures_iter(text).map(|x| x[1].to_string()).collect()
}

#[derive(Debug, PartialEq, Eq)]
enum Data {
    Nil,
    Bool(bool),
    List(Vec<Data>),
    Str(String),
    I64(i64),
    Sym(String),
}

#[test]
fn test_read_form() {
    use Data::*;

    assert_eq!(
        read_str(r#"(define a (false nil "ok" false))"#).unwrap(),
        List(vec![
            Sym("define".to_string()),
            Sym("a".to_string()),
            List(vec![Bool(false), Nil, Str("ok".to_string()), Bool(false)]),
        ])
    );
}

fn read_list<'s, I>(mut tokens: std::iter::Peekable<I>) -> Result<(std::iter::Peekable<I>, Data)>
where
    I: std::iter::Iterator<Item = &'s String>,
{
    let close = match tokens.next().map(String::as_str) {
        Some("(") => ")",
        Some("[") => "]",
        Some("{") => "}",
        token => panic!("invalid token: {:?}", token),
    };

    let mut list = vec![];

    while let Some(token) = tokens.peek() {
        if *token == close {
            let _ = tokens.next();
            return Ok((tokens, Data::List(list)));
        }

        let (rest_token, data) = read_form(tokens)?;

        list.push(data);

        tokens = rest_token;
    }

    anyhow::bail!("reach EOF before close list")
}

fn read_atom<'s, I>(mut tokens: std::iter::Peekable<I>) -> Result<(std::iter::Peekable<I>, Data)>
where
    I: std::iter::Iterator<Item = &'s String>,
{
    let data = match tokens.next().unwrap().as_str() {
        "true" => Data::Bool(true),
        "false" => Data::Bool(false),
        "nil" => Data::Nil,
        token if token.starts_with('"') => Data::Str(
            token
                .strip_prefix('"')
                .unwrap()
                .strip_suffix('"')
                .context("unbalanced string: reach token end before close")?
                .to_string(),
        ),
        token => {
            if let Ok(n) = token.parse::<i64>() {
                Data::I64(n)
            } else {
                Data::Sym(token.to_string())
            }
        }
    };

    Ok((tokens, data))
}

fn read_form<'s, I>(mut tokens: std::iter::Peekable<I>) -> Result<(std::iter::Peekable<I>, Data)>
where
    I: std::iter::Iterator<Item = &'s String>,
{
    let token = tokens.peek().unwrap();

    match token.chars().next().unwrap() {
        '(' | '[' | '{' => read_list(tokens),
        _ => read_atom(tokens),
    }
}
