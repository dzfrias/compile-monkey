use crate::frontend::token::Token;
use std::iter::Peekable;
use std::str::Chars;

/// A lexer that can an input string and turn it into a stream of Monkey
/// [tokens](crate::token::Token).
///
/// # Examples
/// ```
/// use monkey_rs::lexer::Lexer;
/// use monkey_rs::token::Token;
///
/// let input = "let hello_world = 30;";
/// let mut lexer = Lexer::new(input);
///
/// assert_eq!(Token::Let, lexer.next_token());
/// assert_eq!(Token::Ident("hello_world".to_owned()), lexer.next_token());
/// assert_eq!(Token::Assign, lexer.next_token());
/// assert_eq!(Token::Int("30".to_owned()), lexer.next_token());
/// assert_eq!(Token::Semicolon, lexer.next_token());
/// assert_eq!(Token::EOF, lexer.next_token());
/// ```
#[derive(Debug)]
pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    ch: char,
}

impl<'a> Lexer<'a> {
    /// Creates a new `Lexer` with an input and reads the first character.
    /// # Examples
    /// ```
    /// use monkey_rs::lexer::Lexer;
    /// let mut lexer = Lexer::new("1234");
    /// ```
    pub fn new(input: &'a str) -> Self {
        let chars = input.chars().peekable();
        let mut lex = Self {
            input: chars,
            ch: '\0',
        };
        lex.read_char();
        lex
    }

    /// Return the next token found in the lexer's input. It returns
    /// [Token::EOF](crate::token::Token::EOF) when the end of the input is exceeded or reached.
    ///
    /// # Examples
    /// ```
    /// use monkey_rs::lexer::Lexer;
    /// use monkey_rs::token::Token;
    ///
    /// let mut lexer = Lexer::new("let x = 42;");
    /// assert_eq!(lexer.next_token(), Token::Let);
    /// assert_eq!(lexer.next_token(), Token::Ident("x".to_owned()));
    /// assert_eq!(lexer.next_token(), Token::Assign);
    /// assert_eq!(lexer.next_token(), Token::Int("42".to_owned()));
    /// assert_eq!(lexer.next_token(), Token::Semicolon);
    /// assert_eq!(lexer.next_token(), Token::EOF);
    /// ```
    pub fn next_token(&mut self) -> Token {
        macro_rules! peek_eq {
            ($tok:ident, $else_tok:ident) => {
                if self.peek_char() == '=' {
                    self.read_char();
                    Token::$tok
                } else {
                    Token::$else_tok
                }
            };
        }

        self.skip_whitespace();

        let token = match self.ch {
            // Return Token::Assign if a '=' char is found in peek
            '=' => peek_eq!(Eq, Assign),
            ';' => Token::Semicolon,
            '(' => Token::Lparen,
            ')' => Token::Rparen,
            ',' => Token::Comma,
            ':' => Token::Colon,
            '+' => Token::Plus,
            '-' => Token::Minus,
            '!' => peek_eq!(NotEq, Bang),
            '/' => Token::Slash,
            '*' => Token::Asterisk,
            '%' => Token::Percent,
            '<' => peek_eq!(Le, Lt),
            '>' => peek_eq!(Ge, Gt),
            '{' => Token::Lbrace,
            '}' => Token::Rbrace,
            '[' => Token::Lbracket,
            ']' => Token::Rbracket,
            '\0' => Token::EOF,

            // Return early to not call read_char another time
            '0'..='9' => return Token::Int(self.read_number()),

            '"' => Token::String(self.read_string()),

            _ if self.ch.is_alphabetic() || self.ch == '_' => {
                let literal = self.read_identifier();
                return match literal.as_str() {
                    "fn" => Token::Function,
                    "let" => Token::Let,
                    "true" => Token::True,
                    "false" => Token::False,
                    "if" => Token::If,
                    "else" => Token::Else,
                    "return" => Token::Return,
                    _ => Token::Ident(literal.to_owned()),
                };
            }

            _ => Token::Illegal,
        };
        self.read_char();
        token
    }

    fn read_char(&mut self) {
        self.ch = self.input.next().unwrap_or('\0');
    }

    fn peek_char(&mut self) -> char {
        *self.input.peek().unwrap_or(&'\0')
    }

    fn skip_whitespace(&mut self) {
        while self.ch.is_ascii_whitespace() {
            self.read_char();
        }
    }

    fn read_number(&mut self) -> String {
        let mut number = String::new();
        while self.ch.is_ascii_digit() {
            number.push(self.ch);
            self.read_char();
        }
        number
    }

    fn read_identifier(&mut self) -> String {
        let mut ident = String::new();
        // Check if ascii digit so idents like "x1" can be tokenized properly
        while self.ch.is_alphabetic() || self.ch == '_' || self.ch.is_ascii_digit() {
            ident.push(self.ch);
            self.read_char();
        }
        ident
    }

    fn read_string(&mut self) -> String {
        let mut string = String::new();
        self.read_char();
        while self.ch != '"' && self.ch != '\0' {
            string.push(self.ch);
            self.read_char();
        }
        string
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    #[test]
    fn test_next_token() {
        let input = "let five = 5;
        let ten = 10;

        let add = fn(x, y) {
            x + y;
        };

        let result = add(five, ten);
        !-/*5;
        5 < 10 > 5;

        if (5 < 10) {
            return true;
        } else {
            return false;
        }

        10 == 10;
        10 != 9;

        \"foobar\"
        \"foo bar\"

        [1, 2];
        {\"foo\": \"bar\"}
        ";
        let mut lex = Lexer::new(input);

        let expected_tokens = [
            Token::Let,
            Token::Ident("five".to_owned()),
            Token::Assign,
            Token::Int("5".to_owned()),
            Token::Semicolon,
            Token::Let,
            Token::Ident("ten".to_owned()),
            Token::Assign,
            Token::Int("10".to_owned()),
            Token::Semicolon,
            Token::Let,
            Token::Ident("add".to_owned()),
            Token::Assign,
            Token::Function,
            Token::Lparen,
            Token::Ident("x".to_owned()),
            Token::Comma,
            Token::Ident("y".to_owned()),
            Token::Rparen,
            Token::Lbrace,
            Token::Ident("x".to_owned()),
            Token::Plus,
            Token::Ident("y".to_owned()),
            Token::Semicolon,
            Token::Rbrace,
            Token::Semicolon,
            Token::Let,
            Token::Ident("result".to_owned()),
            Token::Assign,
            Token::Ident("add".to_owned()),
            Token::Lparen,
            Token::Ident("five".to_owned()),
            Token::Comma,
            Token::Ident("ten".to_owned()),
            Token::Rparen,
            Token::Semicolon,
            Token::Bang,
            Token::Minus,
            Token::Slash,
            Token::Asterisk,
            Token::Int("5".to_owned()),
            Token::Semicolon,
            Token::Int("5".to_owned()),
            Token::Lt,
            Token::Int("10".to_owned()),
            Token::Gt,
            Token::Int("5".to_owned()),
            Token::Semicolon,
            Token::If,
            Token::Lparen,
            Token::Int("5".to_owned()),
            Token::Lt,
            Token::Int("10".to_owned()),
            Token::Rparen,
            Token::Lbrace,
            Token::Return,
            Token::True,
            Token::Semicolon,
            Token::Rbrace,
            Token::Else,
            Token::Lbrace,
            Token::Return,
            Token::False,
            Token::Semicolon,
            Token::Rbrace,
            Token::Int("10".to_owned()),
            Token::Eq,
            Token::Int("10".to_owned()),
            Token::Semicolon,
            Token::Int("10".to_owned()),
            Token::NotEq,
            Token::Int("9".to_owned()),
            Token::Semicolon,
            Token::String("foobar".to_owned()),
            Token::String("foo bar".to_owned()),
            Token::Lbracket,
            Token::Int("1".to_owned()),
            Token::Comma,
            Token::Int("2".to_owned()),
            Token::Rbracket,
            Token::Semicolon,
            Token::Lbrace,
            Token::String("foo".to_owned()),
            Token::Colon,
            Token::String("bar".to_owned()),
            Token::Rbrace,
            Token::EOF,
        ];

        for expected in expected_tokens {
            let tok = lex.next_token();
            assert_eq!(expected, tok);
        }
    }

    #[test]
    fn next_token_tokenizes_underscore_ident() {
        let input = "hello_world";
        let mut lex = Lexer::new(input);
        assert_eq!(Token::Ident("hello_world".to_owned()), lex.next_token())
    }

    #[test]
    fn next_token_tokenizes_non_ascii_character() {
        let input = "你好";
        let mut lex = Lexer::new(input);
        assert_eq!(Token::Ident("你好".to_owned()), lex.next_token())
    }

    #[test]
    fn next_token_gives_illegal_with_non_alphabetic_character() {
        let input = "👍";
        let mut lex = Lexer::new(input);
        assert_eq!(Token::Illegal, lex.next_token())
    }

    #[test]
    fn next_token_gives_eof() {
        let input = "";
        let mut lex = Lexer::new(input);
        assert_eq!(Token::EOF, lex.next_token());
    }

    #[test]
    fn next_token_recognizes_keywords() {
        let keywords = HashMap::from([
            ("let", Token::Let),
            ("fn", Token::Function),
            ("return", Token::Return),
            ("else", Token::Else),
            ("if", Token::If),
            ("true", Token::True),
            ("false", Token::False),
        ]);
        for (keyword, token) in keywords.iter() {
            let mut lex = Lexer::new(keyword);
            assert_eq!(*token, lex.next_token());
        }
    }

    #[test]
    fn next_token_tokenizes_2_length_binary_ops() {
        let ops = HashMap::from([
            ("==", Token::Eq),
            ("!=", Token::NotEq),
            (">=", Token::Ge),
            ("<=", Token::Le),
        ]);
        for (keyword, token) in ops.iter() {
            let mut lex = Lexer::new(keyword);
            assert_eq!(*token, lex.next_token());
        }
    }

    #[test]
    fn next_token_ignores_whitespace() {
        let input = "	  
        
            word";
        let mut lex = Lexer::new(input);
        assert_eq!(Token::Ident("word".to_owned()), lex.next_token());
    }

    #[test]
    fn next_token_tokenizes_ints() {
        let input = "123";
        let mut lex = Lexer::new(input);
        assert_eq!(Token::Int("123".to_owned()), lex.next_token());
    }

    #[test]
    fn next_token_tokenizes_idents_with_num() {
        let input = "x1";
        let mut lexer = Lexer::new(input);
        assert_eq!(Token::Ident("x1".to_owned()), lexer.next_token());
    }

    #[test]
    fn next_token_gives_int_with_num_before_ident() {
        let input = "1x";
        let mut lexer = Lexer::new(input);
        assert_eq!(Token::Int("1".to_owned()), lexer.next_token());
        assert_eq!(Token::Ident("x".to_owned()), lexer.next_token());
    }

    #[test]
    fn next_token_tokenizes_strings() {
        let input = "\"Hello world\"";
        let mut lexer = Lexer::new(input);
        assert_eq!(Token::String("Hello world".to_owned()), lexer.next_token());
    }
}
