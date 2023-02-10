use rustyline::error::ReadlineError;
use rustyline::Editor;

use anyhow::{Context, Result};

use lazy_static::lazy_static;

use regex::Regex;

use std::collections::HashMap;
use std::rc::Rc;

#[macro_use]
extern crate log;

/*
enum Token {
    Spec1(char), // []{}()'`~^@
    Spec2,       // ~@
}
*/

trait LispFn {
    fn apply(&self, args: &[Data]) -> Result<Data>;
}

struct LispAdd;

impl LispFn for LispAdd {
    fn apply(&self, args: &[Data]) -> Result<Data> {
        let mut n = 0;
        for each in args {
            let x = match each {
                Data::I64(n) => n,
                _ => anyhow::bail!("can not call '+' on: {each}"),
            };
            n += x;
        }

        Ok(Data::I64(n))
    }
}

struct LispMul;

impl LispFn for LispMul {
    fn apply(&self, args: &[Data]) -> Result<Data> {
        let mut n = 1;

        for each in args {
            let x = match each {
                Data::I64(n) => n,
                _ => anyhow::bail!("can not call '*' on: {each}"),
            };
            n *= x;
        }

        Ok(Data::I64(n))
    }
}

struct LispSub;

impl LispFn for LispSub {
    fn apply(&self, args: &[Data]) -> Result<Data> {
        let n = match args {
            [Data::I64(n)] => -n,
            [Data::I64(lhs), Data::I64(rhs)] => lhs - rhs,
            _ => anyhow::bail!("can not call '-' on arguments: {args:?}"),
        };

        Ok(Data::I64(n))
    }
}

struct LispDiv;

impl LispFn for LispDiv {
    fn apply(&self, args: &[Data]) -> Result<Data> {
        let n = match args {
            [Data::I64(lhs), Data::I64(rhs)] => lhs / rhs,
            _ => anyhow::bail!("can not call '/' on arguments: {args:?}"),
        };

        Ok(Data::I64(n))
    }
}

struct Env {
    envmap: HashMap<String, Data>,
}

impl Env {
    fn new() -> Self {
        let mut envmap: HashMap<String, _> = HashMap::new();

        envmap.insert("+".to_string(), Data::Fn(Rc::new(LispAdd)));
        envmap.insert("*".to_string(), Data::Fn(Rc::new(LispMul)));
        envmap.insert("-".to_string(), Data::Fn(Rc::new(LispSub)));
        envmap.insert("/".to_string(), Data::Fn(Rc::new(LispDiv)));

        Self { envmap }
    }

    fn lookup(&self, name: &str) -> Result<&Data> {
        self.envmap
            .get(name)
            .ok_or_else(|| anyhow::format_err!("failed to lookup: {}", name))
    }
}

fn eval<'env>(form: &'env Data, env: &'env Env) -> Result<Data> {
    use Data::*;

    Ok(match form {
        Var(s) => env.lookup(s)?.clone(),
        List(elements) => {
            // A empty list.
            if elements.is_empty() {
                return Ok(form.clone());
            }

            let func = eval(&elements[0], env)?;
            let args: Vec<_> = elements
                .iter()
                .skip(1)
                .map(|x| eval(x, env))
                .collect::<Result<Vec<_>>>()?;

            match func {
                Fn(func) => func.apply(&args)?,
                _ => anyhow::bail!("first argument of function call is not function: {}", func),
            }
        }
        Ary(elements) => Data::Ary(
            elements
                .iter()
                .map(|x| eval(x, env))
                .collect::<Result<Vec<_>>>()?,
        ),
        Map(elements) => Data::Map(
            elements
                .iter()
                .map(|x| eval(x, env))
                .collect::<Result<Vec<_>>>()?,
        ),
        _ => form.clone(),
    })
}

fn main() -> Result<()> {
    env_logger::init();

    let mut ed = Editor::<()>::new()?;

    let env = Env::new();

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

        let data = match read_str(&l).and_then(|form| eval(&form, &env)) {
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

#[derive(Clone)]
enum Data {
    Nil,
    Bool(bool),
    Str(String),
    I64(i64),
    Var(String),
    Sym(String),

    // (a b c)
    List(Vec<Data>),

    // [1 2 3]
    Ary(Vec<Data>),

    // {:one 1 :two 2}
    Map(Vec<Data>),

    Quote(Box<Data>),
    QuasiQuote(Box<Data>),
    Unquote(Box<Data>),
    SpliceUnqute(Box<Data>),

    Fn(Rc<dyn LispFn>),
}

impl Eq for Data {}

impl PartialEq for Data {
    fn eq(&self, rhs: &Data) -> bool {
        use Data::*;

        match (&self, rhs) {
            (Nil, Nil) => true,
            (Bool(lhs), Bool(rhs)) => lhs == rhs,
            (Str(lhs), Str(rhs)) => lhs == rhs,
            (I64(lhs), I64(rhs)) => lhs == rhs,

            (Sym(lhs), Sym(rhs)) => lhs == rhs,
            (Var(lhs), Var(rhs)) => lhs == rhs,

            (List(lhs), List(rhs)) => lhs == rhs,
            (Ary(lhs), Ary(rhs)) => lhs == rhs,
            (Map(lhs), Map(rhs)) => lhs == rhs,

            (Quote(lhs), Quote(rhs)) => lhs == rhs,
            (QuasiQuote(lhs), QuasiQuote(rhs)) => lhs == rhs,
            (SpliceUnqute(lhs), SpliceUnqute(rhs)) => lhs == rhs,

            (Fn(_), Fn(_)) => false,

            _ => false,
        }
    }
}

impl std::fmt::Debug for Data {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        <Data as std::fmt::Display>::fmt(self, f)
    }
}

fn fmt_list<T>(
    (open, close): (char, char),
    l: &[T],
    f: &mut std::fmt::Formatter<'_>,
) -> Result<(), std::fmt::Error>
where
    T: std::fmt::Display,
{
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
    Ok(())
}

impl std::fmt::Display for Data {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        use Data::*;

        match &self {
            Nil => write!(f, "nil")?,
            Bool(b) => write!(f, "{}", b)?,

            List(elements) => fmt_list(('(', ')'), elements, f)?,
            Ary(elements) => fmt_list(('[', ']'), elements, f)?,
            Map(elements) => fmt_list(('{', '}'), elements, f)?,

            Str(s) => write!(f, "{:?}", s)?,
            I64(n) => write!(f, "{}", n)?,
            Sym(s) => write!(f, "{}", s)?,
            Var(s) => write!(f, "{}", s)?,

            Quote(x) => write!(f, "(quote {})", x)?,
            QuasiQuote(x) => write!(f, "(quasiquote {})", x)?,
            Unquote(x) => write!(f, "(unquote {})", x)?,
            SpliceUnqute(x) => write!(f, "(splice-unqute {})", x)?,

            Fn(_) => write!(f, "<function>")?,
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
            Var("define".to_string()),
            Var("a".to_string()),
            List(vec![Bool(false), Nil, Str("ok".to_string()), Bool(false)]),
        ])
    );
}

fn read_list<'s, I>(tokens: std::iter::Peekable<I>) -> Result<(std::iter::Peekable<I>, Data)>
where
    I: std::iter::Iterator<Item = &'s String>,
{
    read_sequence(('(', ')'), tokens, Data::List)
}

fn read_ary<'s, I>(tokens: std::iter::Peekable<I>) -> Result<(std::iter::Peekable<I>, Data)>
where
    I: std::iter::Iterator<Item = &'s String>,
{
    read_sequence(('[', ']'), tokens, Data::Ary)
}

fn read_map<'s, I>(tokens: std::iter::Peekable<I>) -> Result<(std::iter::Peekable<I>, Data)>
where
    I: std::iter::Iterator<Item = &'s String>,
{
    read_sequence(('{', '}'), tokens, Data::Map)
}

fn read_sequence<'s, I, MakeSeq>(
    (open, close): (char, char),
    mut tokens: std::iter::Peekable<I>,
    make_seq: MakeSeq,
) -> Result<(std::iter::Peekable<I>, Data)>
where
    I: std::iter::Iterator<Item = &'s String>,
    MakeSeq: Fn(Vec<Data>) -> Data,
{
    let _ = tokens.next(); // 跳过 open

    let mut list = vec![];

    while let Some(token) = tokens.peek() {
        if token.starts_with(close) {
            let _ = tokens.next();
            return Ok((tokens, make_seq(list)));
        }

        // 从当前剩余的 tokens 读取一个 form，作为 list 的一项。
        let (rest_token, data) = read_form(tokens)?;

        // 读取到的项目添加到容器里。
        list.push(data);

        // 下一个循环解析剩下的 tokens。
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

        token if token.starts_with(':') => Data::Sym(token.to_string()),

        token => {
            if let Ok(n) = token.parse::<i64>() {
                Data::I64(n)
            } else {
                Data::Var(token.to_string())
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

    debug!("read form: {:?}", token);

    match token.as_str() {
        "(" => read_list(tokens),
        "[" => read_ary(tokens),
        "{" => read_map(tokens),

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
