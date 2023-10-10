use crate::frontend::ast::{self, Expr, Stmt};
use crate::frontend::lexer::Lexer;
use crate::frontend::token::Token;
use std::convert::TryFrom;
use std::fmt;

#[derive(Debug, PartialEq, PartialOrd)]
enum Precedence {
    Lowest,
    Equals,
    LessGreater,
    Sum,
    Product,
    Prefix,
    Call,
    Index,
}

impl From<&Token> for Precedence {
    fn from(token: &Token) -> Self {
        match token {
            Token::Eq | Token::NotEq => Precedence::Equals,
            Token::Lt | Token::Gt | Token::Le | Token::Ge => Precedence::LessGreater,
            Token::Plus | Token::Minus => Precedence::Sum,
            Token::Slash | Token::Asterisk | Token::Percent => Precedence::Product,
            Token::Lparen => Precedence::Call,
            Token::Lbracket => Precedence::Index,
            _ => Precedence::Lowest,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct ParserError(String);

impl fmt::Display for ParserError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "parser error: {}", self.0)
    }
}

#[derive(Debug)]
pub struct Parser<'a> {
    lexer: Lexer<'a>,
    errors: Vec<ParserError>,

    current_tok: Token,
    peek_tok: Token,

    in_func: bool,
}

impl<'a> Parser<'a> {
    /// Creates a new `Parser` with the first tokens read in.
    /// # Examples
    /// ```
    /// use monkey_rs::parser::Parser;
    /// use monkey_rs::lexer::Lexer;
    ///
    /// let input = "let x = 4;";
    /// let lexer = Lexer::new(input);
    /// let parser = Parser::new(lexer);
    /// ```
    pub fn new(lexer: Lexer<'a>) -> Self {
        let mut parser = Self {
            lexer,
            errors: Vec::new(),
            current_tok: Token::EOF,
            peek_tok: Token::EOF,
            in_func: false,
        };

        parser.next_token();
        parser.next_token();

        parser
    }

    /// Parses the targeted program and into an [ast::Program](crate::ast::Program). This  will be
    /// a vector of [statements](crate::ast::Stmt).
    ///
    /// # Examples
    /// ```
    /// use monkey_rs::parser::Parser;
    /// use monkey_rs::lexer::Lexer;
    /// use monkey_rs::ast;
    ///
    /// let input = "2 + 3";
    /// let lexer = Lexer::new(input);
    /// let parser = Parser::new(lexer);
    /// let program = parser.parse_program().expect("Should have no parser errors");
    /// assert_eq!(1, program.0.len());
    /// assert_eq!(
    ///     ast::Stmt::Expr(ast::Expr::Infix {
    ///         left: Box::new(ast::Expr::IntegerLiteral(2)),
    ///         op: ast::InfixOp::Plus,
    ///         right: Box::new(ast::Expr::IntegerLiteral(3)),
    ///     }),
    ///     program.0[0]
    /// );
    ///
    /// ```
    pub fn parse_program(mut self) -> Result<ast::Program, Vec<ParserError>> {
        let mut program: ast::Program = ast::Block(Vec::new());

        while self.current_tok != Token::EOF {
            if let Some(stmt) = self.parse_statement() {
                if matches!(stmt, Stmt::Return { .. }) {
                    self.push_error("Cannot return outside of a function context");
                    break;
                }
                program.0.push(stmt);
            }
            self.next_token();
        }

        if self.errors.is_empty() {
            Ok(program)
        } else {
            Err(self.errors)
        }
    }

    fn next_token(&mut self) -> &mut Self {
        self.current_tok = self.peek_tok.clone();
        self.peek_tok = self.lexer.next_token();
        self
    }

    fn expect_peek(&mut self, token: Token) -> Option<&mut Self> {
        if self.peek_tok != token {
            self.push_error(format!("Expected {:?}", token).as_str());
            None
        } else {
            self.next_token();
            Some(self)
        }
    }

    fn push_error(&mut self, reason: &str) {
        self.errors.push(ParserError(reason.to_owned()));
    }

    fn peek_prec(&self) -> Precedence {
        Precedence::from(&self.peek_tok)
    }

    fn current_prec(&self) -> Precedence {
        Precedence::from(&self.current_tok)
    }

    fn parse_statement(&mut self) -> Option<Stmt> {
        match self.current_tok {
            Token::Let => self.parse_let_statement(),
            Token::Return => self.parse_return_statement(),
            _ => self.parse_expr_stmt(),
        }
    }

    fn parse_let_statement(&mut self) -> Option<Stmt> {
        let ident = if let Token::Ident(ident) = &self.peek_tok {
            ast::Identifier(ident.to_owned())
        } else {
            self.push_error("Expected identifier");
            return None;
        };

        self.next_token().expect_peek(Token::Assign)?.next_token();

        let mut value = self.parse_expr(Precedence::Lowest)?;

        if let Expr::Function { name, .. } = &mut value {
            *name = Some(ident.clone().0);
        }
        if self.peek_tok == Token::Semicolon {
            self.next_token();
        }
        Some(Stmt::Let { ident, expr: value })
    }

    fn parse_return_statement(&mut self) -> Option<Stmt> {
        // To expression token(s)
        let return_val = self.next_token().parse_expr(Precedence::Lowest)?;
        if self.peek_tok == Token::Semicolon {
            self.next_token();
        }
        Some(Stmt::Return { expr: return_val })
    }

    fn parse_expr_stmt(&mut self) -> Option<Stmt> {
        let expr = self.parse_expr(Precedence::Lowest)?;
        // Optional semicolon
        if self.peek_tok == Token::Semicolon {
            self.next_token();
        }
        Some(Stmt::Expr(expr))
    }

    fn parse_expr(&mut self, precedence: Precedence) -> Option<Expr> {
        let mut left_exp = match self.current_tok {
            Token::Ident(_) => self
                .parse_ident_expr()
                .expect("Should not happen if current token is Ident"),
            Token::Int(_) => self.parse_integer()?,
            Token::True | Token::False => self
                .parse_bool()
                .expect("Should not happen if current token is True or False"),
            Token::String(_) => self
                .parse_string()
                .expect("Should not happen if current token is a String"),
            Token::Lbracket => self.parse_array_literal()?,
            Token::Bang | Token::Minus | Token::Plus => self.parse_prefix_expr()?,
            Token::Lparen => self.parse_grouped_expr()?,
            Token::If => self.parse_if_expr()?,
            Token::Function => self.parse_function_expr()?,
            Token::Lbrace => self.parse_hash_literal()?,
            _ => {
                self.push_error(
                    format!("No prefix operator {:?} found", self.current_tok).as_ref(),
                );
                return None;
            }
        };

        while self.peek_tok != Token::Semicolon && precedence < self.peek_prec() {
            left_exp = match self.peek_tok {
                Token::Plus
                | Token::Minus
                | Token::Slash
                | Token::Asterisk
                | Token::Eq
                | Token::NotEq
                | Token::Lt
                | Token::Gt
                | Token::Ge
                | Token::Le
                | Token::Percent => self.next_token().parse_infix_expr(left_exp)?,
                Token::Lbracket => self.next_token().parse_index_expr(left_exp)?,
                Token::Lparen => self.next_token().parse_call_expr(left_exp)?,
                _ => return Some(left_exp),
            };
        }
        Some(left_exp)
    }

    fn parse_ident(&mut self) -> Option<ast::Identifier> {
        if let Token::Ident(name) = &self.current_tok {
            Some(ast::Identifier(name.to_owned()))
        } else {
            None
        }
    }

    fn parse_ident_expr(&mut self) -> Option<Expr> {
        Some(Expr::Identifier(self.parse_ident()?))
    }

    fn parse_integer(&mut self) -> Option<Expr> {
        if let Token::Int(int) = &self.current_tok {
            let result = match int.parse() {
                Ok(int) => int,
                Err(_) => {
                    self.push_error("Integer parsing failed");
                    return None;
                }
            };
            Some(Expr::IntegerLiteral(result))
        } else {
            None
        }
    }

    fn parse_bool(&mut self) -> Option<Expr> {
        match self.current_tok {
            Token::True | Token::False => {
                Some(Expr::BooleanLiteral(self.current_tok == Token::True))
            }
            _ => None,
        }
    }

    fn parse_grouped_expr(&mut self) -> Option<Expr> {
        if self.current_tok != Token::Lparen {
            return None;
        }
        let expr = self.next_token().parse_expr(Precedence::Lowest)?;
        self.expect_peek(Token::Rparen)?;
        Some(expr)
    }

    fn parse_prefix_expr(&mut self) -> Option<Expr> {
        let prefix_op = ast::PrefixOp::try_from(&self.current_tok).ok()?;
        let expr = self.next_token().parse_expr(Precedence::Prefix)?;
        Some(Expr::Prefix {
            op: prefix_op,
            expr: Box::new(expr),
        })
    }

    fn parse_infix_expr(&mut self, left: Expr) -> Option<Expr> {
        let infix_op = ast::InfixOp::try_from(&self.current_tok).ok()?;
        let precendence = self.current_prec();
        let right = self.next_token().parse_expr(precendence)?;
        Some(Expr::Infix {
            left: Box::new(left),
            op: infix_op,
            right: Box::new(right),
        })
    }

    fn parse_if_expr(&mut self) -> Option<Expr> {
        let condition = self
            .expect_peek(Token::Lparen)?
            .next_token() // To expresion
            .parse_expr(Precedence::Lowest)?;
        let consequence = self
            .expect_peek(Token::Rparen)?
            .expect_peek(Token::Lbrace)?
            .parse_block_stmt()?;
        let mut alternative = None;
        if self.peek_tok == Token::Else {
            self.next_token().expect_peek(Token::Lbrace)?;
            alternative = Some(self.parse_block_stmt()?);
        }

        Some(Expr::If {
            condition: Box::new(condition),
            consequence,
            alternative,
        })
    }

    fn parse_block_stmt(&mut self) -> Option<ast::Block> {
        let mut statements = ast::Block(Vec::new());
        self.next_token();
        while self.current_tok != Token::Rbrace && self.current_tok != Token::EOF {
            let stmt = self.parse_statement();
            if let Some(stmt) = stmt {
                if matches!(stmt, Stmt::Return { .. }) && !self.in_func {
                    self.push_error("Cannot return outside of a function context");
                    return None;
                }
                statements.0.push(stmt);
            }
            self.next_token();
        }
        Some(statements)
    }

    fn parse_function_expr(&mut self) -> Option<Expr> {
        let params = self.expect_peek(Token::Lparen)?.parse_function_params()?;
        self.in_func = true;
        let body = self.expect_peek(Token::Lbrace)?.parse_block_stmt()?;
        self.in_func = false;
        Some(Expr::Function {
            params,
            body,
            name: None,
        })
    }

    fn parse_function_params(&mut self) -> Option<Vec<ast::Identifier>> {
        let mut idents = Vec::new();
        if self.peek_tok == Token::Rparen {
            self.next_token();
            return Some(idents);
        }
        let ident = match self.next_token().parse_ident() {
            Some(id) => id,
            None => {
                self.push_error("Expected Ident in function params");
                return None;
            }
        };
        idents.push(ident);

        while self.peek_tok == Token::Comma {
            let ident = match self.next_token().next_token().parse_ident() {
                Some(id) => id,
                None => {
                    self.push_error("Expected Ident in function params");
                    return None;
                }
            };
            idents.push(ident);
        }

        self.expect_peek(Token::Rparen);

        Some(idents)
    }

    fn parse_call_expr(&mut self, function: Expr) -> Option<Expr> {
        let args: Vec<Expr> = self.parse_expr_list(Token::Rparen)?;
        Some(Expr::Call {
            func: Box::new(function),
            args,
        })
    }

    fn parse_string(&mut self) -> Option<Expr> {
        match &self.current_tok {
            Token::String(s) => Some(Expr::StringLiteral(s.to_owned())),
            _ => None,
        }
    }

    fn parse_array_literal(&mut self) -> Option<Expr> {
        Some(Expr::ArrayLiteral(self.parse_expr_list(Token::Rbracket)?))
    }

    fn parse_expr_list(&mut self, end: Token) -> Option<Vec<Expr>> {
        let mut exprs = Vec::new();
        if self.peek_tok == end {
            self.next_token();
            return Some(exprs);
        }

        exprs.push(self.next_token().parse_expr(Precedence::Lowest)?);

        while self.peek_tok == Token::Comma {
            self.next_token().next_token();
            exprs.push(self.parse_expr(Precedence::Lowest)?);
        }
        self.expect_peek(end)?;

        Some(exprs)
    }

    fn parse_index_expr(&mut self, left: Expr) -> Option<Expr> {
        let index = self.next_token().parse_expr(Precedence::Lowest)?;
        self.expect_peek(Token::Rbracket)?;
        Some(Expr::Index {
            expr: Box::new(left),
            index: Box::new(index),
        })
    }

    fn parse_hash_literal(&mut self) -> Option<Expr> {
        let mut pairs = Vec::new();
        while self.peek_tok != Token::Rbrace {
            self.next_token();
            let key = self.parse_expr(Precedence::Lowest)?;
            let value = self
                .expect_peek(Token::Colon)?
                .next_token()
                .parse_expr(Precedence::Lowest)?;
            pairs.push((key, value));
            if self.peek_tok != Token::Rbrace && self.expect_peek(Token::Comma).is_none() {
                return None;
            }
        }
        self.expect_peek(Token::Rbrace)?;

        Some(Expr::HashLiteral(pairs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn errs_contain(errs: Vec<ParserError>, err_msg: &str) {
        assert!(errs.contains(&ParserError(err_msg.to_owned())));
    }

    #[test]
    fn parser_parses_let_stmt() {
        let input = "
        let x = 5;
        let y = false;
        let foobar = 838383;
        ";
        let expected = [
            ("x", Expr::IntegerLiteral(5)),
            ("y", Expr::BooleanLiteral(false)),
            ("foobar", Expr::IntegerLiteral(838383)),
        ];

        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);
        let program = parser.parse_program().expect("Parser errors found");
        assert_eq!(3, program.0.len());

        for (stmt, expect) in program.0.iter().zip(expected) {
            if let Stmt::Let { ident, expr } = stmt {
                assert_eq!(expect.0.to_owned(), ident.0);
                assert_eq!(&expect.1, expr)
            } else {
                panic!("Did not parse let statment");
            }
        }
    }

    #[test]
    fn parser_throws_err_with_no_ident() {
        let input = "let = 5;";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);
        let res = parser.parse_program();

        errs_contain(res.unwrap_err(), "Expected identifier");
    }

    #[test]
    fn parser_throws_err_with_no_eq_sign() {
        let input = "let x 5;";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);
        let res = parser.parse_program();

        errs_contain(res.unwrap_err(), "Expected Assign");
    }

    #[test]
    fn parse_ident_expr() {
        let lexer = Lexer::new("foobar;");
        let parser = Parser::new(lexer);
        let program = parser.parse_program().expect("Parser errors found");

        assert_eq!(1, program.0.len());
        assert_eq!(
            Stmt::Expr(Expr::Identifier(ast::Identifier::from("foobar"))),
            program.0[0]
        )
    }

    #[test]
    fn parse_integer_literal() {
        let lexer = Lexer::new("5;");
        let parser = Parser::new(lexer);
        let program = parser.parse_program().expect("Parser errors found");

        assert_eq!(1, program.0.len());
        assert_eq!(Stmt::Expr(Expr::IntegerLiteral(5)), program.0[0]);
    }

    #[test]
    fn parse_integer_errors_with_int_over_i64_limit() {
        let lexer = Lexer::new("92233720368547758073290;");
        let parser = Parser::new(lexer);
        let res = parser.parse_program();

        errs_contain(res.unwrap_err(), "Integer parsing failed");
    }

    #[test]
    fn parse_prefix_expr() {
        let inputs = ["!5", "-15", "+15"];
        let expected = [
            (ast::PrefixOp::Bang, 5),
            (ast::PrefixOp::Minus, 15),
            (ast::PrefixOp::Plus, 15),
        ];

        for (input, expect) in inputs.iter().zip(expected) {
            let lexer = Lexer::new(input);
            let parser = Parser::new(lexer);
            let program = parser.parse_program().expect("Parser errors found");

            assert_eq!(1, program.0.len());
            assert_eq!(
                Stmt::Expr(Expr::Prefix {
                    op: expect.0.clone(),
                    expr: Box::new(Expr::IntegerLiteral(expect.1))
                }),
                program.0[0]
            )
        }
    }

    #[test]
    fn parse_infix_expr() {
        macro_rules! gen_input {
            ($($op:expr),+) => {
                [$(format!("5 {} 5", $op)),*]
            };
        }
        macro_rules! gen_expected {
            ($($op:ident),+) => {
                [$((5, ast::InfixOp::$op, 5)),*]
            };
        }
        let inputs = gen_input!("+", "-", "*", "/", ">", "<", "==", "!=");
        let expected = gen_expected!(Plus, Minus, Asterisk, Slash, Gt, Lt, Eq, NotEq);

        for (input, expect) in inputs.iter().zip(expected) {
            let lexer = Lexer::new(input);
            let parser = Parser::new(lexer);
            let program = parser.parse_program().expect("Parser errors found");

            assert_eq!(1, program.0.len());
            assert_eq!(
                Stmt::Expr(Expr::Infix {
                    left: Box::new(Expr::IntegerLiteral(expect.0)),
                    op: expect.1,
                    right: Box::new(Expr::IntegerLiteral(expect.2))
                }),
                program.0[0]
            );
        }
    }

    #[test]
    fn parse_infix_expr_with_precendence() {
        let inputs = [
            "-a * b",
            "5 < 4 == 3 > 4",
            "a * b / c",
            "!-a",
            "3 + 4 * 5 <= 3 * 1 + 4 * 5",
        ];
        let expected = [
            "((-a) * b);",
            "((5 < 4) == (3 > 4));",
            "((a * b) / c);",
            "(!(-a));",
            "((3 + (4 * 5)) <= ((3 * 1) + (4 * 5)));",
        ];

        for (input, expect) in inputs.iter().zip(expected) {
            let lexer = Lexer::new(input);
            let parser = Parser::new(lexer);
            let program = parser.parse_program().expect("Parser errors found");
            assert_eq!(1, program.0.len());

            assert_eq!(expect, program.0[0].to_string());
        }
    }

    #[test]
    fn parse_bool_literal() {
        let inputs = ["true", "false", "3 == true", "!true"];
        let expected = [
            Expr::BooleanLiteral(true),
            Expr::BooleanLiteral(false),
            Expr::Infix {
                left: Box::new(Expr::IntegerLiteral(3)),
                op: ast::InfixOp::Eq,
                right: Box::new(Expr::BooleanLiteral(true)),
            },
            Expr::Prefix {
                op: ast::PrefixOp::Bang,
                expr: Box::new(Expr::BooleanLiteral(true)),
            },
        ];

        for (input, expect) in inputs.iter().zip(expected) {
            let lexer = Lexer::new(input);
            let parser = Parser::new(lexer);
            let program = parser.parse_program().expect("Parser errors found");
            assert_eq!(1, program.0.len());
            assert_eq!(Stmt::Expr(expect), program.0[0]);
        }
    }

    #[test]
    fn parse_grouped_expr() {
        let inputs = ["1 + (2 + 3) + 4", "(5 + 5) * 2", "-(5 + 5)"];
        let expected = ["((1 + (2 + 3)) + 4);", "((5 + 5) * 2);", "(-(5 + 5));"];

        for (input, expect) in inputs.iter().zip(expected) {
            let lexer = Lexer::new(input);
            let parser = Parser::new(lexer);
            let program = parser.parse_program().expect("Parser errors found");
            assert_eq!(1, program.0.len());
            assert_eq!(expect, program.0[0].to_string());
        }
    }

    #[test]
    fn parse_grouped_expr_needs_closed_paren() {
        let input = "1 + (4 + 5";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);
        let res = parser.parse_program();
        errs_contain(res.unwrap_err(), "Expected Rparen");
    }

    #[test]
    fn parse_if_expr() {
        let inputs = ["if (x < y) { x }", "if (x < y) { x } else { y }"];
        let expected_alts = [
            None,
            Some(ast::Block(vec![Stmt::Expr(Expr::Identifier(
                ast::Identifier::from("y"),
            ))])),
        ];

        for (input, alt) in inputs.iter().zip(expected_alts) {
            let lexer = Lexer::new(input);
            let parser = Parser::new(lexer);
            let program = parser.parse_program().expect("Parser errors found");

            assert_eq!(1, program.0.len());
            match &program.0[0] {
                Stmt::Expr(Expr::If {
                    condition,
                    consequence,
                    alternative,
                }) => {
                    assert_eq!(
                        &Box::new(Expr::Infix {
                            left: Box::new(Expr::Identifier(ast::Identifier::from("x"))),
                            op: ast::InfixOp::Lt,
                            right: Box::new(Expr::Identifier(ast::Identifier::from("y")))
                        }),
                        condition,
                    );
                    assert_eq!(
                        vec![Stmt::Expr(Expr::Identifier(ast::Identifier::from("x")))],
                        consequence.0
                    );
                    assert_eq!(&alt, alternative);
                }
                _ => panic!("Did not parse an if expression"),
            }
        }
    }

    #[test]
    fn parse_func_expr() {
        let inputs = ["fn(x, y) { x + y; }", "fn() { x + y; }"];
        let expected_params = [vec!["x", "y"], Vec::new()];

        for (input, expected) in inputs.iter().zip(expected_params) {
            let lexer = Lexer::new(input);
            let parser = Parser::new(lexer);
            let program = parser.parse_program().expect("Parser errors found");

            assert_eq!(1, program.0.len());
            if let Stmt::Expr(Expr::Function { params, body, .. }) = &program.0[0] {
                let expect_params: Vec<ast::Identifier> = expected
                    .iter()
                    .map(|x| ast::Identifier::from(x.to_owned()))
                    .collect();
                assert_eq!(&expect_params, params);
                assert_eq!(
                    vec![Stmt::Expr(Expr::Infix {
                        left: Box::new(Expr::Identifier(ast::Identifier::from("x"))),
                        op: ast::InfixOp::Plus,
                        right: Box::new(Expr::Identifier(ast::Identifier::from("y")))
                    })],
                    body.0
                )
            } else {
                panic!("Did not parse function expression");
            }
        }
    }

    #[test]
    fn parse_call_expr() {
        let input = "add(1, 2 * 3)";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);
        let program = parser.parse_program().expect("Parser errors found");

        assert_eq!(1, program.0.len());
        if let Stmt::Expr(Expr::Call { func, args }) = &program.0[0] {
            assert_eq!(
                &Box::new(Expr::Identifier(ast::Identifier::from("add"))),
                func
            );
            assert_eq!(
                &vec![
                    Expr::IntegerLiteral(1),
                    Expr::Infix {
                        left: Box::new(Expr::IntegerLiteral(2)),
                        op: ast::InfixOp::Asterisk,
                        right: Box::new(Expr::IntegerLiteral(3))
                    }
                ],
                args
            )
        } else {
            panic!("Did not parse call expression");
        }
    }

    #[test]
    fn parse_call_expr_operator_precedence() {
        let inputs = [
            "a + add(b * c) + d",
            "add(a + b + c * d / f + g)",
            "add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))",
            "a * [1, 2, 3, 4][b * c] * d",
        ];
        let expected = [
            "((a + add((b * c))) + d);",
            "add((((a + b) + ((c * d) / f)) + g));",
            "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)));",
            "((a * ([1, 2, 3, 4][(b * c)])) * d);",
        ];

        for (input, expect) in inputs.iter().zip(expected) {
            let lexer = Lexer::new(input);
            let parser = Parser::new(lexer);
            let program = parser.parse_program().expect("Parser errors found");

            assert_eq!(1, program.0.len());
            assert_eq!(expect, program.0[0].to_string())
        }
    }

    #[test]
    fn cannot_top_level_return() {
        let input = "return 4;";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);
        let res = parser.parse_program();
        errs_contain(
            res.unwrap_err(),
            "Cannot return outside of a function context",
        );
    }

    #[test]
    fn parse_string_literal() {
        let input = "\"Hello world\"";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);
        let res = parser.parse_program().expect("Should have no errors");
        assert_eq!(1, res.0.len());
        assert_eq!(
            Stmt::Expr(Expr::StringLiteral("Hello world".to_owned())),
            res.0[0]
        )
    }

    #[test]
    fn parse_array_literal() {
        let input = "[1, 2 * 2, true]";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);

        let res = parser.parse_program().expect("Should have no errors");
        assert_eq!(1, res.0.len());
        assert_eq!(
            Stmt::Expr(Expr::ArrayLiteral(vec![
                Expr::IntegerLiteral(1),
                Expr::Infix {
                    left: Box::new(Expr::IntegerLiteral(2)),
                    op: ast::InfixOp::Asterisk,
                    right: Box::new(Expr::IntegerLiteral(2))
                },
                Expr::BooleanLiteral(true)
            ])),
            res.0[0]
        )
    }

    #[test]
    fn parse_index_expr() {
        let input = "arr[1 + 1]";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);

        let res = parser.parse_program().expect("Should have no errors");
        assert_eq!(1, res.0.len());
        assert_eq!(
            Stmt::Expr(Expr::Index {
                expr: Box::new(Expr::Identifier(ast::Identifier::from("arr"))),
                index: Box::new(Expr::Infix {
                    left: Box::new(Expr::IntegerLiteral(1)),
                    op: ast::InfixOp::Plus,
                    right: Box::new(Expr::IntegerLiteral(1))
                })
            }),
            res.0[0]
        )
    }

    #[test]
    fn parse_hash_literal_with_literal_string_keys() {
        let input = "{\"one\": 1, \"two\": 2, \"three\": 3}";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);

        let res = parser.parse_program().expect("Should have no errors");
        assert_eq!(1, res.0.len());
        assert_eq!(
            Stmt::Expr(Expr::HashLiteral(vec![
                (
                    Expr::StringLiteral("one".to_owned()),
                    Expr::IntegerLiteral(1)
                ),
                (
                    Expr::StringLiteral("two".to_owned()),
                    Expr::IntegerLiteral(2)
                ),
                (
                    Expr::StringLiteral("three".to_owned()),
                    Expr::IntegerLiteral(3)
                )
            ])),
            res.0[0]
        )
    }

    #[test]
    fn parse_empty_hash_literal() {
        let input = "{}";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);

        let res = parser.parse_program().expect("Should have no errors");
        assert_eq!(1, res.0.len());
        assert_eq!(Stmt::Expr(Expr::HashLiteral(Vec::new())), res.0[0])
    }

    #[test]
    fn parse_hash_literal_with_expressions() {
        let input = "{\"one\": 0 + 1, \"two\": 10 - 8, \"three\": 15 / 5}";
        let lexer = Lexer::new(input);
        let parser = Parser::new(lexer);

        let res = parser.parse_program().expect("Should have no errors");
        assert_eq!(1, res.0.len());
        assert_eq!(
            Stmt::Expr(Expr::HashLiteral(vec![
                (
                    Expr::StringLiteral("one".to_owned()),
                    Expr::Infix {
                        left: Box::new(Expr::IntegerLiteral(0)),
                        op: ast::InfixOp::Plus,
                        right: Box::new(Expr::IntegerLiteral(1))
                    }
                ),
                (
                    Expr::StringLiteral("two".to_owned()),
                    Expr::Infix {
                        left: Box::new(Expr::IntegerLiteral(10)),
                        op: ast::InfixOp::Minus,
                        right: Box::new(Expr::IntegerLiteral(8))
                    }
                ),
                (
                    Expr::StringLiteral("three".to_owned()),
                    Expr::Infix {
                        left: Box::new(Expr::IntegerLiteral(15)),
                        op: ast::InfixOp::Slash,
                        right: Box::new(Expr::IntegerLiteral(5))
                    }
                )
            ])),
            res.0[0]
        )
    }
}
