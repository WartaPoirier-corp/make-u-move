mod lexer;
mod parser;

struct Makefile<'a> {
    rules: Vec<Rule<'a>>,
}

struct Rule<'a> {
    name: &'a str,
    deps: Vec<&'a Rule<'a>>,
    commands: Vec<String>,
}

#[derive(Debug)]
enum Error {
    UnexpectedCharacter,
    UnexpectedEof,
}

impl<'a> Makefile<'a> {
    fn try_parse(src: &'a str) -> Result<Makefile<'a>, Error> {
        let tokens = lexer::try_lex(src)?;
        parser::try_parse(tokens)
    }
}
