use crate::frontend::token::Token;
use std::convert::TryFrom;
use std::fmt;

/// A statement represents the possible statement types in the monkey langauge.
/// There are only three, as monkey uses [expressions](Expr) for most of its
/// control flow.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Stmt {
    /// A statement of the form: `let <ident> = <expr>;`
    Let { ident: Identifier, expr: Expr },
    /// A statement of the form: `return <expr>;`
    Return { expr: Expr },
    /// A wrapper for [expressions](Expr), makes it possible to put
    /// expressions on their own line
    Expr(Expr),
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::Let { ident, expr } => write!(f, "let {} = {};", ident, expr),
            Stmt::Return { expr } => write!(f, "return {};", expr),
            Stmt::Expr(expr) => write!(f, "{};", expr),
        }
    }
}

/// An expression in the monkey language.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    /// An identifier
    Identifier(Identifier),
    /// An 64 bit integer literal
    IntegerLiteral(i64),
    /// A boolean literal
    BooleanLiteral(bool),
    StringLiteral(String),
    ArrayLiteral(Vec<Expr>),
    HashLiteral(Vec<(Expr, Expr)>),
    /// Operators prefixing other expressions, like ! or -
    Prefix {
        op: PrefixOp,
        expr: Box<Expr>,
    },
    /// Operators between two expressions, like + or /
    Infix {
        left: Box<Expr>,
        op: InfixOp,
        right: Box<Expr>,
    },
    /// An if condition of the form: `if (<expr>) { <block> } else { <block> }`.
    /// The else block is optional
    If {
        condition: Box<Expr>,
        consequence: Block,
        alternative: Option<Block>,
    },
    /// A function of the form: `fn(<param1>, ..., <paramN>) { <block> }`.
    /// Functions are first class
    Function {
        name: Option<String>,
        params: Vec<Identifier>,
        body: Block,
    },
    /// A function call of the form: `<expr>(<arg1>, ..., <argN>) { <block> }`.
    /// The expression can be anything that evaluates to a function.
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    Index {
        expr: Box<Expr>,
        index: Box<Expr>,
    },
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Identifier(Identifier(name)) => write!(f, "{name}"),
            Expr::IntegerLiteral(int) => write!(f, "{int}"),
            Expr::BooleanLiteral(b) => write!(f, "{b}"),
            Expr::StringLiteral(s) => write!(f, "\"{s}\""),
            Expr::ArrayLiteral(arr) => {
                let elems = arr
                    .iter()
                    .map(|elem| elem.to_string() + ", ")
                    .collect::<String>();
                write!(
                    f,
                    "[{}]",
                    elems.strip_suffix(", ").expect("Should have trailing ', '")
                )
            }
            Expr::HashLiteral(hashmap) => {
                let elems = hashmap
                    .iter()
                    .map(|elem| elem.0.to_string() + ": " + &elem.1.to_string())
                    .collect::<Vec<_>>();
                write!(f, "{{{}}}", elems.join(", "))
            }
            Expr::Prefix { op, expr } => write!(f, "({op}{expr})"),
            Expr::Infix { left, op, right } => write!(f, "({left} {op} {right})"),
            Expr::If {
                condition,
                consequence,
                alternative,
            } => {
                if let Some(alt) = alternative {
                    write!(f, "if {condition} {{ {consequence} }} else {{ {alt} }}")
                } else {
                    write!(f, "if {condition} {{ {consequence} }}")
                }
            }
            Expr::Function { params, body, .. } => {
                let joined = params
                    .iter()
                    .map(|ident| ident.to_string() + ", ")
                    .collect::<String>();
                write!(
                    f,
                    "fn({}) {{ {body} }}",
                    joined
                        .strip_suffix(", ")
                        .expect("Should always have a trailing ', '")
                )
            }
            Expr::Call { func, args } => {
                let joined = args
                    .iter()
                    .map(|expr| expr.to_string() + ", ")
                    .collect::<String>();
                write!(
                    f,
                    "{func}({})",
                    joined
                        .strip_suffix(", ")
                        .expect("Should always have a trailing ', '")
                )
            }
            Expr::Index { expr, index } => {
                write!(f, "({}[{}])", expr, index)
            }
        }
    }
}

/// A prefix operator that goes before an expression.
#[derive(Debug, PartialEq, Clone, Eq)]
pub enum PrefixOp {
    /// Negative operator
    Minus,
    /// Not operator
    Bang,
    /// Positive operator
    Plus,
}

impl TryFrom<&Token> for PrefixOp {
    type Error = String;

    fn try_from(token: &Token) -> Result<Self, Self::Error> {
        Ok(match token {
            Token::Minus => Self::Minus,
            Token::Bang => Self::Bang,
            Token::Plus => Self::Plus,
            _ => return Err(format!("Invalid prefix operator token: {:?}", token)),
        })
    }
}

impl fmt::Display for PrefixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrefixOp::Minus => write!(f, "-"),
            PrefixOp::Bang => write!(f, "!"),
            PrefixOp::Plus => write!(f, "+"),
        }
    }
}

/// An infix operator that goes between two expressions.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum InfixOp {
    /// Addition operator
    Plus,
    /// Subtraction operator
    Minus,
    /// Multiplication operator
    Asterisk,
    /// Division operator
    Slash,
    /// Greater-than operator
    Gt,
    /// Less-than operator
    Lt,
    /// Equal operator
    Eq,
    /// Inequality operator
    NotEq,
    /// Greater-than or equal-to operator
    Ge,
    /// Less-than or equal-to operator
    Le,
    /// Modulus operator
    Modulo,
}

impl TryFrom<&Token> for InfixOp {
    type Error = String;

    fn try_from(token: &Token) -> Result<Self, Self::Error> {
        Ok(match token {
            Token::Plus => Self::Plus,
            Token::Minus => Self::Minus,
            Token::Asterisk => Self::Asterisk,
            Token::Slash => Self::Slash,
            Token::Gt => Self::Gt,
            Token::Lt => Self::Lt,
            Token::Eq => Self::Eq,
            Token::NotEq => Self::NotEq,
            Token::Ge => Self::Ge,
            Token::Le => Self::Le,
            Token::Percent => Self::Modulo,
            _ => return Err(format!("Invalid infix operator token: {:?}", token)),
        })
    }
}

impl fmt::Display for InfixOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InfixOp::Plus => write!(f, "+"),
            InfixOp::Minus => write!(f, "-"),
            InfixOp::Asterisk => write!(f, "*"),
            InfixOp::Slash => write!(f, "/"),
            InfixOp::Gt => write!(f, ">"),
            InfixOp::Lt => write!(f, "<"),
            InfixOp::Eq => write!(f, "=="),
            InfixOp::NotEq => write!(f, "!="),
            InfixOp::Ge => write!(f, ">="),
            InfixOp::Le => write!(f, "<="),
            InfixOp::Modulo => write!(f, "%"),
        }
    }
}

/// An identifier in the monkey language.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Identifier(pub String);

impl From<&str> for Identifier {
    fn from(s: &str) -> Self {
        Self(s.to_owned())
    }
}

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A block representing a series of statements.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Block(pub Vec<Stmt>);
impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let to_str = self
            .0
            .iter()
            .map(|stmt| stmt.to_string() + " ")
            .collect::<String>();
        write!(
            f,
            "{}",
            to_str
                .strip_suffix(' ')
                .expect("Should always have a trailing ' '")
        )
    }
}

/// A special type of block at the root of the program.
pub type Program = Block;
