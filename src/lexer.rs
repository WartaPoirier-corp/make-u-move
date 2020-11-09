use super::Error;

#[derive(PartialEq, Eq, Debug)]
pub(crate) enum Lexeme<'a> {
    Word(&'a str),
    Colon,
    Tab,
}

use Lexeme::*;

#[derive(PartialEq)]
enum Grammar {
    Normal,
}

struct Tokenizer<'a> {
    tokens: Vec<Lexeme<'a>>,
    grammar: Grammar,
    chars: Vec<char>,
}

impl<'a> Tokenizer<'a> {
    fn new(buf_size: usize) -> Tokenizer<'a> {
        Tokenizer {
            tokens: Vec::with_capacity(buf_size / 3),
            grammar: Grammar::Normal,
            chars: Vec::with_capacity(buf_size / 10),
        }
    }
}

pub(crate) fn try_lex<'a>(src: &'a str) -> Result<Vec<Lexeme>, Error> {
    let res = src.chars().fold(Tokenizer::new(src.len()), |mut t, c| {
        match t.grammar {
            Grammar::Normal => match c {
                ' ' | '\t' | ':' => {
                    t.chars.push(c);
                    let chars: String = t.chars.iter().collect();
                    if let Some(tok) = str_to_tok(&chars) {
                        t.tokens.push(tok);
                        t.chars.clear();
                    }

                    t
                }
                _ => {
                    t.chars.push(c);
                    t
                }
            }
        }
    });

    if res.grammar == Grammar::Normal && res.chars.is_empty() {
        Ok(res.tokens)
    } else {
        Err(Error::UnexpectedEof)
    }
}

fn str_to_tok<'a>(s: &'a str) -> Option<Lexeme<'a>> {
    match s {
        ":" => Some(Colon),
        "\t" => Some(Tab),
        " " => None,
        _ => Some(Word(s)),
    }
}

#[cfg(test)]
mod tests {
    macro_rules! assert_lex {
        ($src:expr, [ $( $lexeme:ident ),* ]) => {
            assert_eq!(super::try_lex($src).unwrap(), vec![ $( super::Lexeme::$lexeme ),* ])
        };
        ($src:expr, fail) => {
            assert!(super::try_lex($src).is_err());
        }
    }

    #[test]
    fn one_base_token() {
        assert_lex!(":", [ Colon ]);
        assert_lex!("\t", [ Tab ]);
    }

    #[test]
    fn words() {
        
    }
}
