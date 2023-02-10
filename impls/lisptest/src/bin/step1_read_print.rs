use rustyline::error::ReadlineError;
use rustyline::Editor;

use anyhow::Result;

use lazy_static::lazy_static;

use regex::Regex;

#[macro_use]
extern crate log;

/*
enum Token {
    Spec1(char), // []{}()'`~^@
    Spec2,       // ~@
}
*/

fn main() -> Result<()> {
    env_logger::init();

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

        println!("{}", data);
    }

    Ok(())
}

fn read_str(text: &str) -> Result<Data> {
    let tokens = tokenize(text);

    debug!("tokens: {:?}", tokens);

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

#[derive(PartialEq, Eq)]
enum Data {
    Nil,
    Bool(bool),
    List {
        pair: (char, char),
        elements: Vec<Data>,
    },
    Str(String),
    I64(i64),
    Sym(String),
    Quote(Box<Data>),
    QuasiQuote(Box<Data>),
    Unquote(Box<Data>),
    SpliceUnqute(Box<Data>),
}

impl std::fmt::Display for Data {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        use Data::*;

        match &self {
            Nil => write!(f, "nil")?,
            Bool(b) => write!(f, "{}", b)?,

            List {
                pair: (open, close),
                elements: l,
            } => {
                write!(f, "{}", open)?;

                let mut first = true;
                for each in l {
                    if first {
                        first = false;
                    } else {
                        write!(f, " ")?;
                    }

                    write!(f, "{}", each)?;
                }

                write!(f, "{}", close)?;
            }

            Str(s) => write!(f, "{:?}", s)?,
            I64(n) => write!(f, "{}", n)?,
            Sym(s) => write!(f, "{}", s)?,

            Quote(x) => write!(f, "(quote {})", x)?,
            QuasiQuote(x) => write!(f, "(quasiquote {})", x)?,
            Unquote(x) => write!(f, "(unquote {})", x)?,
            SpliceUnqute(x) => write!(f, "(splice-unqute {})", x)?,
        }

        Ok(())
    }
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
    let open = tokens.next().unwrap().chars().next().unwrap();

    let close = match open {
        '(' => ')',
        '[' => ']',
        '{' => '}',
        token => panic!("invalid token: {:?}", token),
    };

    let mut list = vec![];

    while let Some(token) = tokens.peek() {
        if token.starts_with(close) {
            let _ = tokens.next();
            return Ok((
                tokens,
                Data::List {
                    pair: (open, close),
                    elements: list,
                },
            ));
        }

        let (rest_token, data) = read_form(tokens)?;

        list.push(data);

        tokens = rest_token;
    }

    anyhow::bail!("reach EOF before close list")
}

/// 将输入的字符串字面值转换成转义后的字符串。
fn escape_str(text: &str) -> Result<String> {
    let mut s = vec![];

    let mut escape = false;
    let mut end = false;

    for c in text.chars().skip(1) {
        if escape {
            s.push(escape_char(c));
            escape = false;
            continue;
        }

        match c {
            '"' => end = true,
            '\\' => escape = true,
            _ => s.push(c),
        }
    }

    if !end {
        anyhow::bail!("unbalanced string: reach token end before close");
    }

    Ok(s.into_iter().collect())
}

fn escape_char(c: char) -> char {
    match c {
        'n' => '\n',
        't' => '\t',
        'r' => '\r',
        _ => c,
    }
}

fn read_atom<'s, I>(mut tokens: std::iter::Peekable<I>) -> Result<(std::iter::Peekable<I>, Data)>
where
    I: std::iter::Iterator<Item = &'s String>,
{
    let data = match tokens.next().unwrap().as_str() {
        "true" => Data::Bool(true),
        "false" => Data::Bool(false),
        "nil" => Data::Nil,

        token if token.starts_with('"') => Data::Str(escape_str(token)?),
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

type ParseOk<I> = (std::iter::Peekable<I>, Data);

type ParseResult<I> = Result<ParseOk<I>>;

fn read_form<'s, I>(mut tokens: std::iter::Peekable<I>) -> ParseResult<I>
where
    I: std::iter::Iterator<Item = &'s String>,
{
    let token = tokens.peek().unwrap();

    match token.as_str() {
        "(" | "[" | "{" => read_list(tokens),

        "'" => {
            let _ = tokens.next();
            let (tokens, data) = read_form(tokens)?;
            Ok((tokens, Data::Quote(Box::new(data))))
        }

        "`" => {
            let _ = tokens.next();
            let (tokens, data) = read_form(tokens)?;
            Ok((tokens, Data::QuasiQuote(Box::new(data))))
        }

        "~" => {
            let _ = tokens.next();
            let (tokens, data) = read_form(tokens)?;
            Ok((tokens, Data::Unquote(Box::new(data))))
        }

        "~@" => {
            let _ = tokens.next();
            let (tokens, data) = read_form(tokens)?;
            Ok((tokens, Data::SpliceUnqute(Box::new(data))))
        }
        _ => read_atom(tokens),
    }
}
