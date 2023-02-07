use rustyline::error::ReadlineError;
use rustyline::Editor;

use anyhow::Result;

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

        if !l.is_empty() {
            println!("{}", l);
        }
    }

    Ok(())
}
