//! A parser for the Alethe proof format.

mod error;
mod lexer;
pub(crate) mod tests;

use std::iter::Iterator;

pub use error::{ParserError, SortError};
pub use lexer::{Lexer, Position, Reserved, Token};

use crate::{
    ast::*,
    utils::{HashCache, HashMapStack},
    CarcaraResult, Error,
};
use error::assert_num_args;
use indexmap::{IndexMap, IndexSet};
use rug::{Integer, Rational};
use std::{io::BufRead, str::FromStr};

use self::error::assert_indexed_op_args_value;

#[derive(Debug, Clone, Copy, Default)]
pub struct Config {
    /// If `true`, the parser will automatically expand function definitions introduced by
    /// `define-fun` commands in the SMT problem. If `false`, those `define-fun`s are instead
    /// interpreted as a function declaration and an `assert` command that defines the function
    /// as equal to its body (or to a lambda term, if it contains arguments). Note that function
    /// definitions in the proof are always expanded.
    pub apply_function_defs: bool,

    /// If `true`, the parser will eliminate `let` bindings from terms during parsing. This is done
    /// by replacing any occurence of a variable bound in the `let` binding with its corresponding
    /// value.
    pub expand_lets: bool,

    /// If `true`, this relaxes the type checking rules in Carcara to allow `Int`-`Real` subtyping.
    /// That is, terms of sort `Int` will be allowed in arithmetic operations where a `Real` term
    /// was expected. Note that this only applies to predefined operators --- passing an `Int` term
    /// to a function that expects a `Real` will still be an error.
    pub allow_int_real_subtyping: bool,

    /// Enables "strict" parsing. If `true`:
    /// - Unary `and`, `or` and `xor` terms are not allowed
    /// - Anchor arguments using the old syntax (i.e., `(:= <symbol> <term>)`) are not allowed
    pub strict: bool,

    /// If `true`, the parser will parse arguments to the `hole` rule, expecting them to be valid
    /// terms.
    pub parse_hole_args: bool,
}

impl Config {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Parses an SMT problem instance (in the SMT-LIB format) and its associated proof (in the Alethe
/// format).
///
/// This returns the parsed proof, as well as the `TermPool` used in parsing. Can take any type that
/// implements `BufRead`.
pub fn parse_instance<T: BufRead>(
    problem: T,
    proof: T,
    config: Config,
) -> CarcaraResult<(Problem, Proof, PrimitivePool)> {
    let mut pool = PrimitivePool::new();
    parse_instance_with_pool(problem, proof, config, &mut pool)
        .map(|(prelude, proof)| (prelude, proof, pool))
}

pub fn parse_instance_with_pool<T: BufRead>(
    problem: T,
    proof: T,
    config: Config,
    pool: &mut PrimitivePool,
) -> CarcaraResult<(Problem, Proof)> {
    let mut parser = Parser::new(pool, config, problem)?;
    let problem = parser.parse_problem()?;
    parser.reset(proof)?;
    let proof = parser.parse_proof()?;
    Ok((problem, proof))
}

/// A function definition, from a `define-fun` command.
struct FunctionDef {
    params: Vec<SortedVar>,
    body: Rc<Term>,
}

impl FunctionDef {
    fn apply(&self, p: &mut PrimitivePool, args: Vec<Rc<Term>>) -> Result<Rc<Term>, ParserError> {
        assert_num_args(&args, self.params.len())?;
        if args.is_empty() {
            return Ok(self.body.clone());
        }

        for (arg, param) in args.iter().zip(self.params.iter()) {
            SortError::assert_eq(param.1.as_sort().unwrap(), p.sort(arg).as_sort().unwrap())?;
        }

        // Build a hash map of all the parameter names and the values they will
        // take
        let substitution = self
            .params
            .iter()
            .zip(args)
            .map(|((n, s), arg)| (p.add(Term::new_var(n, s.clone())), arg))
            .collect();

        // Since we already checked the sorts of the arguments, creating this substitution
        // can never fail
        let result = Substitution::new(p, substitution)
            .unwrap()
            .apply(p, &self.body);
        Ok(result)
    }
}

/// A sort definition, from a `define-sort` command.
struct SortDef {
    params: Vec<String>,
    body: Rc<Term>,
}

/// The state of the parser.
///
/// This holds all the function, constant or sort declarations and definitions, as well as the term
/// pool used by the parser.
#[derive(Default)]
struct ParserState {
    symbol_table: HashMapStack<HashCache<String>, Rc<Term>>,
    function_defs: IndexMap<String, FunctionDef>,
    sort_declarations: HashMapStack<String, usize>,
    sort_defs: IndexMap<String, SortDef>,
    step_ids: HashMapStack<HashCache<String>, usize>,
}

/// A parser for the Alethe proof format.
pub struct Parser<'a, R> {
    pool: &'a mut PrimitivePool,
    config: Config,
    lexer: Lexer<R>,
    current_token: Token,
    current_position: Position,
    state: ParserState,
    is_real_only_logic: bool,
    problem: Option<Problem>,
}

impl<'a, R: BufRead> Parser<'a, R> {
    /// Constructs a new `Parser` from a type that implements `BufRead`.
    ///
    /// This operation can fail if there is an IO or lexer error on the first token.
    pub fn new(pool: &'a mut PrimitivePool, config: Config, input: R) -> CarcaraResult<Self> {
        let mut lexer = Lexer::new(input)?;
        let (current_token, current_position) = lexer.next_token()?;
        Ok(Parser {
            pool,
            config,
            lexer,
            current_token,
            current_position,
            state: ParserState::default(),
            is_real_only_logic: false,
            problem: None,
        })
    }

    /// Resets the parser position and sets its input to `input`. This keeps the parser state,
    /// including all function, constant and sort declarations.
    pub fn reset(&mut self, input: R) -> CarcaraResult<()> {
        let mut lexer = Lexer::new(input)?;
        let (current_token, current_position) = lexer.next_token()?;
        self.lexer = lexer;
        self.current_token = current_token;
        self.current_position = current_position;
        Ok(())
    }

    /// Advances the parser one token, and returns the previous `current_token`.
    fn next_token(&mut self) -> CarcaraResult<(Token, Position)> {
        use std::mem::replace;

        let (new_token, new_position) = self.lexer.next_token()?;
        let old_token = replace(&mut self.current_token, new_token);
        let old_position = replace(&mut self.current_position, new_position);
        Ok((old_token, old_position))
    }

    /// Inserts a `SortedVar` into the parser symbol table.
    fn insert_sorted_var(&mut self, (symbol, sort): SortedVar) {
        self.state.symbol_table.insert(HashCache::new(symbol), sort);
    }

    /// Shortcut for `self.problem.as_mut().unwrap().prelude`
    fn prelude(&mut self) -> &mut ProblemPrelude {
        &mut self.problem.as_mut().unwrap().prelude
    }

    /// Shortcut for `self.problem.as_mut().unwrap().premises`
    fn premises(&mut self) -> &mut IndexSet<Rc<Term>> {
        &mut self.problem.as_mut().unwrap().premises
    }

    /// Constructs and sort checks a variable term.
    fn make_var(&mut self, iden: String) -> Result<Rc<Term>, ParserError> {
        let cached = HashCache::new(iden);
        let sort = match self.state.symbol_table.get(&cached) {
            Some(s) => s.clone(),
            None => return Err(ParserError::UndefinedIden(cached.unwrap())),
        };
        Ok(self.pool.add(Term::Var(cached.unwrap(), sort)))
    }

    /// Return whether we should interpret integer constants as `Real`s.
    ///
    /// If we are working with a logic that contains reals but does not contain integers, and if we
    /// are parsing the problem and not the poof, this will be true.
    fn interpret_ints_as_reals(&self) -> bool {
        self.is_real_only_logic && self.problem.is_some()
    }

    /// Constructs and sort checks an operation term.
    fn make_op(&mut self, op: Operator, args: Vec<Rc<Term>>) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();
        let sorts: Vec<_> = sorts.iter().map(|s| s.as_sort().unwrap()).collect();
        match op {
            Operator::True | Operator::False => assert_num_args(&args, 0)?,
            Operator::Not => {
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::Bool, sorts[0])?;
            }
            Operator::Implies => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    SortError::assert_eq(&Sort::Bool, s)?;
                }
            }
            Operator::Or | Operator::And | Operator::Xor => {
                // If we are not in "strict" parsing mode, we allow these operators to be called
                // with just one argument
                assert_num_args(&args, if self.config.strict { 2.. } else { 1.. })?;
                for s in sorts {
                    SortError::assert_eq(&Sort::Bool, s)?;
                }
            }
            Operator::Equals | Operator::Distinct => {
                assert_num_args(&args, 2..)?;
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::Ite => {
                assert_num_args(&args, 3)?;
                SortError::assert_eq(&Sort::Bool, sorts[0])?;
                SortError::assert_eq(sorts[1], sorts[2])?;
            }
            Operator::Add | Operator::Sub | Operator::Mult => {
                // The `-` operator, in particular, can be called with only one argument, in which
                // case it means negation instead of subtraction
                if op == Operator::Sub {
                    assert_num_args(&args, 1..)?;
                } else {
                    assert_num_args(&args, 2..)?;
                }

                // All the arguments must be either Int or Real. Also, if we are not allowing
                // Int/Real subtyping, all arguments must have the same sort
                if self.config.allow_int_real_subtyping {
                    for s in sorts {
                        SortError::assert_one_of(&[Sort::Int, Sort::Real], s)?;
                    }
                } else {
                    SortError::assert_one_of(&[Sort::Int, Sort::Real], sorts[0])?;
                    SortError::assert_all_eq(&sorts)?;
                }
            }
            Operator::IntDiv => {
                assert_num_args(&args, 2..)?;
                SortError::assert_eq(&Sort::Int, sorts[0])?;
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::RealDiv => {
                assert_num_args(&args, 2..)?;

                // Normally, the `/` operator may only receive Real arguments, but if we are
                // allowing Int/Real subtyping, it may also receive Ints
                if self.config.allow_int_real_subtyping {
                    for s in sorts {
                        SortError::assert_one_of(&[Sort::Int, Sort::Real], s)?;
                    }
                } else {
                    SortError::assert_eq(&Sort::Real, sorts[0])?;
                    SortError::assert_all_eq(&sorts)?;
                }

                if let Some(r) = self.interpret_div_as_real_lit(&args[0], &args[1]) {
                    return Ok(r);
                }
            }
            Operator::Mod => {
                assert_num_args(&args, 2)?;
                SortError::assert_eq(&Sort::Int, sorts[0])?;
                SortError::assert_eq(&Sort::Int, sorts[1])?;
            }
            Operator::Abs => {
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::Int, sorts[0])?;
            }
            Operator::LessThan | Operator::GreaterThan | Operator::LessEq | Operator::GreaterEq => {
                assert_num_args(&args, 2..)?;
                // All the arguments must be either Int or Real sorted, but they don't need to all
                // have the same sort
                for s in sorts {
                    SortError::assert_one_of(&[Sort::Int, Sort::Real], s)?;
                }
            }
            Operator::ToReal => {
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::Int, sorts[0])?;
            }
            Operator::ToInt | Operator::IsInt => {
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::Real, sorts[0])?;
            }
            Operator::Select => {
                assert_num_args(&args, 2)?;
                SortError::assert_array_sort(self.pool, Some(sorts[1]), None, sorts[0])?;
            }
            Operator::Store => {
                assert_num_args(&args, 3)?;
                SortError::assert_array_sort(self.pool, Some(sorts[1]), Some(sorts[2]), sorts[0])?;
            }
            Operator::StrConcat => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    SortError::assert_eq(&Sort::String, s)?;
                }
            }
            Operator::StrLen | Operator::StrIsDigit | Operator::StrToCode | Operator::StrToInt => {
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::String, sorts[0])?;
            }
            Operator::StrLessThan
            | Operator::StrLessEq
            | Operator::PrefixOf
            | Operator::SuffixOf
            | Operator::Contains
            | Operator::ReRange => {
                assert_num_args(&args, 2)?;
                SortError::assert_eq(&Sort::String, sorts[0])?;
                SortError::assert_eq(&Sort::String, sorts[1])?;
            }
            Operator::CharAt => {
                assert_num_args(&args, 2)?;
                SortError::assert_eq(&Sort::String, sorts[0])?;
                SortError::assert_eq(&Sort::Int, sorts[1])?;
            }
            Operator::Substring => {
                assert_num_args(&args, 3)?;
                SortError::assert_eq(&Sort::String, sorts[0])?;
                SortError::assert_eq(&Sort::Int, sorts[1])?;
                SortError::assert_eq(&Sort::Int, sorts[2])?;
            }
            Operator::IndexOf => {
                assert_num_args(&args, 3)?;
                SortError::assert_eq(&Sort::String, sorts[0])?;
                SortError::assert_eq(&Sort::String, sorts[1])?;
                SortError::assert_eq(&Sort::Int, sorts[2])?;
            }
            Operator::Replace | Operator::ReplaceAll => {
                assert_num_args(&args, 3)?;
                SortError::assert_eq(&Sort::String, sorts[0])?;
                SortError::assert_eq(&Sort::String, sorts[1])?;
                SortError::assert_eq(&Sort::String, sorts[2])?;
            }
            Operator::StrFromCode | Operator::StrFromInt => {
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::Int, sorts[0])?;
            }
            Operator::StrToRe => {
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::String, sorts[0])?;
            }
            Operator::StrInRe => {
                assert_num_args(&args, 2)?;
                SortError::assert_eq(&Sort::String, sorts[0])?;
                SortError::assert_eq(&Sort::RegLan, sorts[1])?;
            }
            Operator::ReNone | Operator::ReAll | Operator::ReAllChar => {
                assert_num_args(&args, 0)?;
            }
            Operator::ReConcat
            | Operator::ReUnion
            | Operator::ReIntersection
            | Operator::ReDiff => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    SortError::assert_eq(&Sort::RegLan, s)?;
                }
            }
            Operator::ReKleeneClosure
            | Operator::ReComplement
            | Operator::ReKleeneCross
            | Operator::ReOption => {
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::RegLan, sorts[0])?;
            }
            Operator::ReplaceRe | Operator::ReplaceReAll => {
                assert_num_args(&args, 3)?;
                SortError::assert_eq(&Sort::String, sorts[0])?;
                SortError::assert_eq(&Sort::RegLan, sorts[1])?;
                SortError::assert_eq(&Sort::String, sorts[2])?;
            }
            Operator::BvNot | Operator::BvNeg => {
                assert_num_args(&args, 1)?;
                for s in sorts {
                    if !matches!(s, Sort::BitVec(_)) {
                        return Err(ParserError::ExpectedBvSort(s.clone()));
                    }
                }
            }
            Operator::BvBbTerm => {
                assert_num_args(&args, 1..)?;
                SortError::assert_eq(&Sort::Bool, sorts[0])?;
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::BvConcat => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    if !matches!(s, Sort::BitVec(_)) {
                        return Err(ParserError::ExpectedBvSort(s.clone()));
                    }
                }
            }
            Operator::BvAdd
            | Operator::BvMul
            | Operator::BvAnd
            | Operator::BvOr
            | Operator::BvXor => {
                assert_num_args(&args, 2..)?;
                if !matches!(sorts[0], Sort::BitVec(_)) {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::BvUDiv
            | Operator::BvURem
            | Operator::BvShl
            | Operator::BvLShr
            | Operator::BvULt
            | Operator::BvNAnd
            | Operator::BvNOr
            | Operator::BvXNor
            | Operator::BvComp
            | Operator::BvSub
            | Operator::BvSDiv
            | Operator::BvSRem
            | Operator::BvSMod
            | Operator::BvAShr
            | Operator::BvULe
            | Operator::BvUGt
            | Operator::BvUGe
            | Operator::BvSLt
            | Operator::BvSLe
            | Operator::BvSGt
            | Operator::BvSGe => {
                assert_num_args(&args, 2)?;
                if !matches!(sorts[0], Sort::BitVec(_)) {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                SortError::assert_all_eq(&sorts)?;
            }
            Operator::RareList => SortError::assert_all_eq(&sorts)?,
        }
        Ok(self.pool.add(Term::Op(op, args)))
    }

    fn interpret_div_as_real_lit(&mut self, a: &Rc<Term>, b: &Rc<Term>) -> Option<Rc<Term>> {
        // If the term is a division between two positive integer constants, and their GCD is 1,
        // then it should be interpreted as a rational literal. The only exception to this is the
        // term '(/ 1 1)', which is still interpreted as a divison term.

        let [a, b] = [a, b].map(|t| match t.as_ref() {
            Term::Const(Constant::Integer(i)) => Some(i),
            Term::Const(Constant::Real(r)) if self.interpret_ints_as_reals() && r.is_integer() => {
                Some(r.numer())
            }
            _ => None,
        });
        let [a, b] = [a?, b?];

        if *a > 0 && *b > 0 && !(*a == 1 && *b == 1) && a.clone().gcd(b) == 1 {
            Some(self.pool.add(Term::new_real(Rational::from((a, b)))))
        } else {
            None
        }
    }

    /// Constructs and sort checks an application term.
    fn make_app(
        &mut self,
        function: Rc<Term>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sort = self.pool.sort(&function);
        let sorts = {
            let function_sort = sort.as_sort().unwrap();
            if let Sort::Function(sorts) = function_sort {
                sorts
            } else {
                // Function does not have function sort
                return Err(ParserError::NotAFunction(function_sort.clone()));
            }
        };
        assert_num_args(&args, sorts.len() - 1)?;
        for i in 0..args.len() {
            SortError::assert_eq(
                sorts[i].as_sort().unwrap(),
                self.pool.sort(&args[i]).as_sort().unwrap(),
            )?;
        }
        Ok(self.pool.add(Term::App(function, args)))
    }

    /// Consumes the current token if it equals `expected`. Returns an error otherwise.
    fn expect_token(&mut self, expected: Token) -> CarcaraResult<()> {
        let (got, pos) = self.next_token()?;
        if got == expected {
            Ok(())
        } else {
            Err(Error::Parser(ParserError::UnexpectedToken(got), pos))
        }
    }

    /// Consumes the current token if it is a symbol, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_symbol(&mut self) -> CarcaraResult<String> {
        match self.next_token()? {
            (Token::Symbol(s), _) => Ok(s),
            (other, pos) => Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Consumes the current token if it is a keyword, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_keyword(&mut self) -> CarcaraResult<String> {
        match self.next_token()? {
            (Token::Keyword(s), _) => Ok(s),
            (other, pos) => Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Consumes the current token if it is a numeral, and returns the inner `Integer`. Returns an
    /// error otherwise.
    fn expect_numeral(&mut self) -> CarcaraResult<Integer> {
        match self.next_token()? {
            (Token::Numeral(n), _) => Ok(n),
            (other, pos) => Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Calls `parse_func` repeatedly until a closing parenthesis is reached.
    ///
    /// If `non_empty` is true, empty sequences will result in an error. This method consumes the
    /// ending `)` token.
    fn parse_sequence<T, F>(&mut self, mut parse_func: F, non_empty: bool) -> CarcaraResult<Vec<T>>
    where
        F: FnMut(&mut Self) -> CarcaraResult<T>,
    {
        let mut result = Vec::new();
        while self.current_token != Token::CloseParen {
            result.push(parse_func(self)?);
        }
        if non_empty && result.is_empty() {
            Err(Error::Parser(
                ParserError::EmptySequence,
                self.current_position,
            ))
        } else {
            self.next_token()?; // Consume `)` token
            Ok(result)
        }
    }

    /// Reads tokens until the matching closing parenthesis is reached.
    fn read_until_close_parens(&mut self) -> CarcaraResult<Vec<Token>> {
        let mut result = Vec::new();
        let mut parens_depth = 1;
        while parens_depth > 0 {
            let token = self.next_token()?;
            parens_depth += match token {
                (Token::OpenParen, _) => 1,
                (Token::CloseParen, _) => -1,
                (Token::Eof, pos) => {
                    return Err(Error::Parser(ParserError::UnexpectedToken(Token::Eof), pos));
                }
                _ => 0,
            };
            result.push(token.0);
        }
        Ok(result)
    }

    /// Consumes and drops tokens until the matching closing parenthesis is reached.
    fn ignore_until_close_parens(&mut self) -> CarcaraResult<()> {
        self.read_until_close_parens()?;
        Ok(())
    }

    /// Consumes and ignores attributes and their values until a closing parenthesis is reached.
    fn ignore_remaining_attributes(&mut self) -> CarcaraResult<()> {
        while let Token::Keyword(_) = self.current_token {
            self.next_token()?;
            match self.current_token {
                // If we reached the closing parenthesis or the end of the file, we stop
                Token::CloseParen | Token::Eof => break,

                // If there is no value for this attribute, we may encounter the next attribute, in
                // which case we must continue without consuming the keyword token
                Token::Keyword(_) => (),

                // If there is a single token as a value we consume it
                Token::Symbol(_)
                | Token::Numeral(_)
                | Token::Decimal(_)
                | Token::Bitvector { .. }
                | Token::String(_)
                | Token::ReservedWord(_) => {
                    self.next_token()?;
                }

                // And if the value is an s-expression we read tokens until it's closed
                Token::OpenParen => {
                    self.next_token()?;
                    self.ignore_until_close_parens()?;
                }
            }
            if self.current_token == Token::CloseParen {
                break;
            }
        }
        Ok(())
    }

    /// Reads an SMT-LIB script and parses the assertions, declarations and definitions.
    ///
    /// The following commands are parsed:
    ///
    /// - `assert`
    /// - `declare-const`
    /// - `declare-fun`
    /// - `declare-sort`
    /// - `define-fun`
    /// - `set-logic`
    ///
    /// All other commands are ignored. This method returns a hash set containing the premises
    /// introduced in `assert` commands.
    pub fn parse_problem(&mut self) -> CarcaraResult<Problem> {
        self.problem = Some(Problem::new());

        while self.current_token != Token::Eof {
            self.expect_token(Token::OpenParen)?;
            match self.next_token()?.0 {
                Token::ReservedWord(Reserved::DeclareFun) => {
                    let (name, sort) = self.parse_declare_fun()?;
                    self.insert_sorted_var((name.clone(), sort.clone()));
                    self.prelude().function_declarations.push((name, sort));
                }
                Token::ReservedWord(Reserved::DeclareConst) => {
                    let name = self.expect_symbol()?;
                    let sort = self.parse_sort()?;
                    self.expect_token(Token::CloseParen)?;
                    self.insert_sorted_var((name.clone(), sort.clone()));
                    self.prelude().function_declarations.push((name, sort));
                }
                Token::ReservedWord(Reserved::DeclareSort) => {
                    let (name, arity) = self.parse_declare_sort()?;

                    self.prelude().sort_declarations.push((name.clone(), arity));

                    // User declared sorts are represented with the `Atom` sort kind, and an
                    // argument which is a string terminal representing the sort name.
                    self.state.sort_declarations.insert(name, arity);
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;

                    if self.config.apply_function_defs {
                        self.state.function_defs.insert(name, func_def);
                    } else {
                        // If `self.apply_function_defs` is false, we instead add the function name
                        // to the symbol table, and add a new premise that defines the function
                        let lambda_term = if func_def.params.is_empty() {
                            func_def.body
                        } else {
                            self.pool.add(Term::Binder(
                                Binder::Lambda,
                                BindingList(func_def.params),
                                func_def.body,
                            ))
                        };
                        let sort = self.pool.sort(&lambda_term);
                        let var = (name, sort);
                        self.insert_sorted_var(var.clone());
                        let var_term = self.pool.add(var.into());
                        let assertion_term = self
                            .pool
                            .add(Term::Op(Operator::Equals, vec![var_term, lambda_term]));
                        self.premises().insert(assertion_term);
                    }
                }
                Token::ReservedWord(Reserved::DefineFunRec) => self.parse_define_fun_rec(false)?,
                Token::ReservedWord(Reserved::DefineFunsRec) => self.parse_define_fun_rec(true)?,
                Token::ReservedWord(Reserved::DefineSort) => {
                    let (name, def) = self.parse_define_sort()?;
                    self.state.sort_defs.insert(name, def);
                }
                Token::ReservedWord(Reserved::Assert) => {
                    let term = self.parse_term()?;
                    self.expect_token(Token::CloseParen)?;
                    self.premises().insert(term);
                }
                Token::ReservedWord(Reserved::CheckSatAssuming) => {
                    self.expect_token(Token::OpenParen)?;
                    let terms = self.parse_sequence(Self::parse_term, true)?;
                    self.expect_token(Token::CloseParen)?;
                    self.premises().extend(terms);
                }
                Token::ReservedWord(Reserved::SetLogic) => {
                    let logic = self.expect_symbol()?;
                    self.expect_token(Token::CloseParen)?;
                    self.prelude().logic = Some(logic.clone());

                    // When the problem's logic contains real numbers but not integers, integer
                    // literals should be parsed as reals. For instance, `1` should be interpreted
                    // as `1.0`. We must be careful to avoid false positives with non-standard
                    // logics like "HORN".
                    self.is_real_only_logic =
                        (logic.contains("LRA") || logic.contains("NRA") || logic.contains("RDL"))
                            && !logic.contains('I');
                }
                _ => {
                    // If the command is not one of the commands we care about, we just ignore it.
                    // We do that by reading tokens until the command parenthesis is closed
                    self.ignore_until_close_parens()?;
                }
            }
        }
        Ok(self.problem.take().unwrap())
    }

    /// Parses a proof in the Alethe format. All function, constant and sort declarations needed
    /// should already be in the parser state. Note that the `premises` field in the proof will not
    /// be set.
    pub fn parse_proof(&mut self) -> CarcaraResult<Proof> {
        // To avoid stack overflows in proofs with many nested subproofs, we parse the subproofs
        // iteratively, instead of recursively. Therefore, we need to manually keep a stack.
        //
        // Each frame of the stack stores the subproof that is being constructed, and the id of the
        // step that will end it. The first frame of the stack represents the root proof, so every
        // field except for the subproof commands is irrelevant.
        let mut stack: Vec<(Subproof, String)> = vec![(Subproof::default(), String::new())];

        let mut next_subproof_context_id = 0;

        let mut finished_assumes = false;

        let mut constant_definitions = Vec::new();

        // Some solvers print the satisfiability result (unsat) together with the proof. To save the
        // user from having to remove this, we consume this first "unsat" token if it exists
        if self.current_token == Token::Symbol("unsat".into()) {
            self.next_token()?;
        }

        while self.current_token != Token::Eof {
            self.expect_token(Token::OpenParen)?;
            let (token, position) = self.next_token()?;
            let (id, command) = match token {
                Token::ReservedWord(Reserved::Assume) => {
                    let (id, term) = self.parse_assume_command()?;
                    if stack.len() == 1 && finished_assumes {
                        log::warn!("`assume` command '{}' appears after `step` commands", &id);
                    }
                    (id.clone(), ProofCommand::Assume { id, term })
                }
                Token::ReservedWord(Reserved::Step) => {
                    finished_assumes = true;
                    let step = self.parse_step_command()?;
                    (step.id.clone(), ProofCommand::Step(step))
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;
                    if func_def.params.is_empty() {
                        constant_definitions.push((name.clone(), func_def.body.clone()));
                    }
                    self.state.function_defs.insert(name, func_def);
                    continue;
                }
                Token::ReservedWord(Reserved::Anchor) => {
                    let (end_step_id, args) = self.parse_anchor_command()?;

                    // When we encounter an `anchor` command, we push a new scope into the step ids
                    // symbol table, a fresh commands vector into the commands stack for the
                    // subproof to fill, and the `anchor` data (end step and arguments) into their
                    // respective stacks. All of this will be popped off at the end of the subproof.
                    // We don't need to push a new scope into the symbol table because
                    // `Parser::parse_anchor_command` already does that for us
                    self.state.step_ids.push_scope();
                    let subproof = Subproof {
                        commands: Vec::new(),
                        args,
                        context_id: next_subproof_context_id,
                    };
                    stack.push((subproof, end_step_id));
                    next_subproof_context_id += 1;
                    continue;
                }
                _ => {
                    return Err(Error::Parser(ParserError::UnexpectedToken(token), position));
                }
            };
            let id = HashCache::new(id);
            if self.state.step_ids.get(&id).is_some() {
                return Err(Error::Parser(
                    ParserError::RepeatedStepId(id.unwrap()),
                    position,
                ));
            }

            let (top_subproof, top_end_step) = stack.last_mut().unwrap();
            top_subproof.commands.push(command);
            if top_end_step == id.as_ref() {
                // If this is the last step in a subproof, we need to pop all the subproof data off
                // of the stacks and build the subproof command with it
                self.state.symbol_table.pop_scope();
                self.state.step_ids.pop_scope();
                let (subproof, _) = stack.pop().unwrap();

                // The subproof must contain at least two commands: the end step and the previous
                // command it implicitly references
                if subproof.commands.len() < 2 {
                    return Err(Error::Parser(
                        ParserError::EmptySubproof(id.unwrap()),
                        position,
                    ));
                }

                // We also need to make sure that the last command is in fact a `step`
                if !subproof.commands.last().unwrap().is_step() {
                    return Err(Error::Parser(
                        ParserError::LastSubproofStepIsNotStep(id.unwrap()),
                        position,
                    ));
                }

                let (outer, _) = stack.last_mut().unwrap();
                outer.commands.push(ProofCommand::Subproof(subproof));
            }
            let index = stack.last().unwrap().0.commands.len() - 1;
            self.state.step_ids.insert(id, index);
        }
        let commands = match stack.len() {
            0 => unreachable!(),
            1 => stack.pop().unwrap().0.commands,

            // If there is more than one layer in the stack, we are inside a subproof that should be
            // closed before the outer proof is finished
            _ => {
                return Err(Error::Parser(
                    ParserError::UnclosedSubproof(stack.pop().unwrap().1),
                    self.current_position,
                ))
            }
        };
        Ok(Proof { constant_definitions, commands })
    }

    /// Parses an `assume` proof command. This method assumes that the `(` and `assume` tokens were
    /// already consumed.
    fn parse_assume_command(&mut self) -> CarcaraResult<(String, Rc<Term>)> {
        let id = self.expect_symbol()?;
        let term = self.parse_term_expecting_sort(&Sort::Bool)?;
        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;
        Ok((id, term))
    }

    /// Parses a `step` proof command. This method assumes that the `(` and `step` tokens were
    /// already consumed.
    fn parse_step_command(&mut self) -> CarcaraResult<ProofStep> {
        let id = self.expect_symbol()?;
        let clause = self.parse_clause()?;
        self.expect_token(Token::Keyword("rule".into()))?;
        let rule = match self.next_token()? {
            (Token::Symbol(s), _) => s,
            (Token::ReservedWord(r), _) => format!("{}", r),
            (other, pos) => {
                return Err(Error::Parser(ParserError::UnexpectedToken(other), pos));
            }
        };

        let premises = if self.current_token == Token::Keyword("premises".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Self::parse_step_premise, true)?
        } else {
            Vec::new()
        };

        let args = if self.current_token == Token::Keyword("args".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;

            // If the rule is `hole` and `--parse-hole-args` is not enabled, we want to allow any
            // invalid arguments, so we read the rest of the `:args` attribute without trying to
            // parse anything
            if rule == "hole" && !self.config.parse_hole_args {
                self.ignore_until_close_parens()?;
                Vec::new()
            } else {
                self.parse_sequence(Self::parse_term, true)?
            }
        } else {
            Vec::new()
        };

        // For some rules (notably the `subproof` rule), there is also a `:discharge` attribute that
        // takes a series of command ids, in addition to the regular premises
        let discharge = if self.current_token == Token::Keyword("discharge".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(|p| p.parse_discharge_premise(&id), true)?
        } else {
            Vec::new()
        };

        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;

        Ok(ProofStep {
            id,
            clause,
            rule,
            premises,
            args,
            discharge,
        })
    }

    /// Parses a premise for a `step` command. This already converts it into the depth and command
    /// index used to reference commands in the AST.
    fn parse_step_premise(&mut self) -> CarcaraResult<(usize, usize)> {
        let position = self.current_position;
        let id = HashCache::new(self.expect_symbol()?);
        self.state
            .step_ids
            .get_with_depth(&id)
            .map(|(d, &i)| (d, i))
            .ok_or_else(|| Error::Parser(ParserError::UndefinedStepId(id.unwrap()), position))
    }

    /// Parses an argument for the `:discharge` attribute.
    ///
    /// Due to a bug in veriT, commands local to the current subproof are passed by their "relative"
    /// id. That is, the command `t5.t4.h2` is passed as simply `h2`. This behavior is not present
    /// in other SMT solvers, like cvc5. To work around that, this function tries to find the
    /// command considering both possibilities.
    fn parse_discharge_premise(&mut self, root_id: &str) -> CarcaraResult<(usize, usize)> {
        let position = self.current_position;
        let id = self.expect_symbol()?;
        let absolute_id = format!("{}.{}", root_id, &id);
        let id = HashCache::new(id);
        let absolute_id = HashCache::new(absolute_id);
        self.state
            .step_ids
            .get_with_depth(&absolute_id)
            .or_else(|| self.state.step_ids.get_with_depth(&id))
            .map(|(d, &i)| (d, i))
            .ok_or_else(|| Error::Parser(ParserError::UndefinedStepId(id.unwrap()), position))
    }

    /// Parses an `anchor` proof command. This method assumes that the `(` and `anchor` tokens were
    /// already consumed.
    ///
    /// In order to parse the subproof arguments, this method pushes a new scope into the symbol
    /// table which must be removed after parsing the subproof.
    fn parse_anchor_command(&mut self) -> CarcaraResult<(String, Vec<AnchorArg>)> {
        self.expect_token(Token::Keyword("step".into()))?;
        let end_step_id = self.expect_symbol()?;

        // We have to push a new scope into the symbol table in order to parse the subproof
        // arguments
        self.state.symbol_table.push_scope();

        let args = if self.current_token == Token::Keyword("args".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Parser::parse_anchor_argument, true)?
        } else {
            Vec::new()
        };
        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;
        Ok((end_step_id, args))
    }

    /// Parses an argument for an `anchor` proof command. This can be either a variable binding of
    /// the form `(<symbol> <sort>)` or an assignment, of the form `(:= (<symbol> <sort>) <term>)`.
    fn parse_anchor_argument(&mut self) -> CarcaraResult<AnchorArg> {
        self.expect_token(Token::OpenParen)?;
        Ok(if self.current_token == Token::Keyword("=".into()) {
            self.next_token()?;

            // To make Carcara more robust to recent changes in the Alethe format, we support
            // parsing the two versions of assign-style anchor arguments:
            // - the old version, without the sort hint: `(:= <symbol> <term>)`
            // - and the new version, with the sort hint: `(:= (<symbol> <sort>) <term>)`
            // However, if "strict" parsing is enabled, we only allow the new version
            let (var, value, sort) =
                if !self.config.strict && matches!(self.current_token, Token::Symbol(_)) {
                    let var = self.expect_symbol()?;
                    let value = self.parse_term()?;
                    let sort = self.pool.sort(&value);
                    (var, value, sort)
                } else {
                    let (var, sort) = self.parse_sorted_var()?;
                    let value = self.parse_term_expecting_sort(sort.as_sort().unwrap())?;
                    (var, value, sort)
                };
            self.insert_sorted_var((var.clone(), sort.clone()));
            self.expect_token(Token::CloseParen)?;
            AnchorArg::Assign((var, sort), value)
        } else {
            let symbol = self.expect_symbol()?;
            let sort = self.parse_sort()?;
            self.insert_sorted_var((symbol.clone(), sort.clone()));
            self.expect_token(Token::CloseParen)?;
            AnchorArg::Variable((symbol, sort))
        })
    }

    /// Parses a `declare-fun` proof command. Returns the function name and a term representing its
    /// sort. This method assumes that the `(` and `declare-fun` tokens were already consumed.
    fn parse_declare_fun(&mut self) -> CarcaraResult<(String, Rc<Term>)> {
        let name = self.expect_symbol()?;
        let sort = {
            self.expect_token(Token::OpenParen)?;
            let mut sorts = self.parse_sequence(Self::parse_sort, false)?;
            sorts.push(self.parse_sort()?);
            if sorts.len() == 1 {
                sorts.into_iter().next().unwrap()
            } else {
                self.pool.add(Term::Sort(Sort::Function(sorts)))
            }
        };
        self.expect_token(Token::CloseParen)?;
        Ok((name, sort))
    }

    /// Parses a declare-sort proof command. Returns the sort name and its arity. This method
    /// assumes that the `(` and `declare-sort` tokens were already consumed.
    fn parse_declare_sort(&mut self) -> CarcaraResult<(String, usize)> {
        let name = self.expect_symbol()?;
        let arity_pos = self.current_position;
        let arity = self.expect_numeral()?;
        self.expect_token(Token::CloseParen)?;
        let arity = arity.to_usize().ok_or(Error::Parser(
            ParserError::InvalidSortArity(arity),
            arity_pos,
        ))?;
        Ok((name, arity))
    }

    /// Parses a function declaration, of the form `(<symbol> (<sorted var>*) <sort>)`. If the
    /// parameter `consume_parens` is `false`, the opening and closing parentheses are not consumed
    fn parse_function_dec(
        &mut self,
        consume_parens: bool,
    ) -> CarcaraResult<(String, Vec<SortedVar>, Rc<Term>)> {
        if consume_parens {
            self.expect_token(Token::OpenParen)?;
        }
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let params = self.parse_sequence(Self::parse_sorted_var, false)?;
        let return_sort = self.parse_sort()?;
        if consume_parens {
            self.expect_token(Token::CloseParen)?;
        }
        Ok((name, params, return_sort))
    }

    /// Parses a `define-fun` proof command. Returns the function name and its definition. This
    /// method assumes that the `(` and `define-fun` tokens were already consumed.
    fn parse_define_fun(&mut self) -> CarcaraResult<(String, FunctionDef)> {
        let (name, params, return_sort) = self.parse_function_dec(false)?;

        // In order to correctly parse the function body, we push a new scope to the symbol table
        // and add the functions arguments to it.
        self.state.symbol_table.push_scope();
        for var in &params {
            self.insert_sorted_var(var.clone());
        }
        let body = self.parse_term_expecting_sort(return_sort.as_sort().unwrap())?;
        self.state.symbol_table.pop_scope();

        self.expect_token(Token::CloseParen)?;

        Ok((name, FunctionDef { params, body }))
    }

    /// Adds the premise corresponding to a `define-fun-rec` function definition.
    fn add_define_fun_rec_premise(&mut self, name: String, params: Vec<SortedVar>, body: Rc<Term>) {
        let application = {
            let cached = HashCache::new(name);
            let func_sort = self.state.symbol_table.get(&cached).unwrap();
            let name = cached.unwrap();
            let func_term = self.pool.add((name, func_sort.clone()).into());
            if params.is_empty() {
                func_term
            } else {
                let args = params
                    .iter()
                    .map(|var| self.pool.add(var.clone().into()))
                    .collect();
                self.pool.add(Term::App(func_term, args))
            }
        };
        let equality_term = build_term!(self.pool, (= {application} {body}));
        let premise = if params.is_empty() {
            equality_term
        } else {
            let bindings = BindingList(params);
            self.pool
                .add(Term::Binder(Binder::Forall, bindings, equality_term))
        };
        self.premises().insert(premise);
    }

    /// Parses a `define-fun-rec`/`define-funs-rec` command. Inserts the function names into the
    /// symbol table, and adds the appropriate premises. This method assumes the `(` and
    /// `define-fun-rec`/`define-funs-rec` tokens were already consumed.
    fn parse_define_fun_rec(&mut self, is_multiple: bool) -> CarcaraResult<()> {
        let declarations = if is_multiple {
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(|p| p.parse_function_dec(true), true)?
        } else {
            vec![self.parse_function_dec(false)?]
        };

        for (name, params, return_sort) in &declarations {
            let sort = if params.is_empty() {
                return_sort.as_sort().unwrap().clone()
            } else {
                let mut param_sorts: Vec<_> = params.iter().map(|(_, sort)| sort.clone()).collect();
                param_sorts.push(return_sort.clone());
                Sort::Function(param_sorts)
            };
            let sort = self.pool.add(Term::Sort(sort));
            self.insert_sorted_var((name.clone(), sort));
        }

        if is_multiple {
            self.expect_token(Token::OpenParen)?;
        }
        for (name, params, return_sort) in declarations {
            self.state.symbol_table.push_scope();
            for var in &params {
                self.insert_sorted_var(var.clone());
            }
            let body = self.parse_term_expecting_sort(return_sort.as_sort().unwrap())?;
            self.state.symbol_table.pop_scope();

            self.add_define_fun_rec_premise(name, params, body);
        }
        if is_multiple {
            self.expect_token(Token::CloseParen)?;
        }
        self.expect_token(Token::CloseParen)?;

        Ok(())
    }

    /// Parses a `define-sort` proof command. Returns the sort name and its definition. This method
    /// assumes that the `(` and `define-sort` tokens were already consumed.
    fn parse_define_sort(&mut self) -> CarcaraResult<(String, SortDef)> {
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let params = self.parse_sequence(Self::expect_symbol, false)?;

        // In order to correctly parse the sort definition, we push a new scope to the sort
        // declarations table and add the sort parameters to it.
        self.state.sort_declarations.push_scope();
        for s in &params {
            self.state.sort_declarations.insert(s.clone(), 0);
        }
        let body = self.parse_sort()?;
        self.state.sort_declarations.pop_scope();

        self.expect_token(Token::CloseParen)?;

        Ok((name, SortDef { params, body }))
    }

    /// Parses a clause of the form `(cl <term>*)`.
    fn parse_clause(&mut self) -> CarcaraResult<Vec<Rc<Term>>> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::Cl))?;
        self.parse_sequence(|p| p.parse_term_expecting_sort(&Sort::Bool), false)
    }

    /// Parses a sorted variable of the form `(<symbol> <sort>)`.
    fn parse_sorted_var(&mut self) -> CarcaraResult<SortedVar> {
        self.expect_token(Token::OpenParen)?;
        let symbol = self.expect_symbol()?;
        let sort = self.parse_sort()?;
        self.expect_token(Token::CloseParen)?;
        Ok((symbol, sort))
    }

    /// Parses a term.
    pub fn parse_term(&mut self) -> CarcaraResult<Rc<Term>> {
        let term = match self.next_token()? {
            (Token::Bitvector { value, width }, _) => Term::new_bv(value, width),
            (Token::Numeral(n), _) if self.interpret_ints_as_reals() => Term::new_real(n),
            (Token::Numeral(n), _) => Term::new_int(n),
            (Token::Decimal(r), _) => Term::new_real(r),
            (Token::String(s), _) => Term::new_string(s),
            (Token::Symbol(s), pos) => {
                // Check to see if there is a nullary function defined with this name
                return if let Some(func) = self.state.function_defs.get(&s) {
                    func.apply(self.pool, Vec::new())
                        .map_err(|err| Error::Parser(err, pos))
                } else if let Ok(op) = Operator::from_str(&s) {
                    let args = Vec::new();

                    self.make_op(op, args)
                        .map_err(|err| Error::Parser(err, pos))
                } else {
                    self.make_var(s).map_err(|err| Error::Parser(err, pos))
                };
            }
            (Token::OpenParen, _) => return self.parse_application(),
            (other, pos) => {
                return Err(Error::Parser(ParserError::UnexpectedToken(other), pos));
            }
        };
        Ok(self.pool.add(term))
    }

    pub fn parse_constant(&mut self) -> CarcaraResult<Constant> {
        let constant = match self.next_token()? {
            (Token::Bitvector { value, width }, _) => Constant::BitVec(value, width.into()),
            (Token::Numeral(n), _) if self.interpret_ints_as_reals() => Constant::Real(n.into()),
            (Token::Numeral(n), _) => Constant::Integer(n),
            (Token::Decimal(r), _) => Constant::Real(r),
            (Token::String(s), _) => Constant::String(s),
            (other, pos) => {
                return Err(Error::Parser(ParserError::UnexpectedToken(other), pos));
            }
        };
        Ok(constant)
    }
    /// Parses a term and checks that its sort matches the expected sort. If not, returns an error.
    fn parse_term_expecting_sort(&mut self, expected_sort: &Sort) -> CarcaraResult<Rc<Term>> {
        let pos = self.current_position;
        let term = self.parse_term()?;
        SortError::assert_eq(expected_sort, self.pool.sort(&term).as_sort().unwrap())
            .map_err(|e| Error::Parser(e.into(), pos))?;
        Ok(term)
    }

    /// Parses a binder term. This method assumes that the `(` and binder tokens were
    /// already consumed.
    fn parse_binder(&mut self, binder: Binder) -> CarcaraResult<Rc<Term>> {
        self.expect_token(Token::OpenParen)?;
        self.state.symbol_table.push_scope();
        let bindings = if binder == Binder::Choice {
            let var = self.parse_sorted_var()?;
            self.insert_sorted_var(var.clone());
            self.expect_token(Token::CloseParen)?;
            BindingList(vec![var])
        } else {
            BindingList(self.parse_sequence(
                |p| {
                    let var = p.parse_sorted_var()?;
                    p.insert_sorted_var(var.clone());
                    Ok(var)
                },
                true,
            )?)
        };
        let term = match binder {
            Binder::Lambda => self.parse_term()?,
            _ => self.parse_term_expecting_sort(&Sort::Bool)?,
        };
        self.state.symbol_table.pop_scope();
        self.expect_token(Token::CloseParen)?;
        Ok(self.pool.add(Term::Binder(binder, bindings, term)))
    }

    /// Parses a `let` term. This method assumes that the `(` and `let` tokens were already
    /// consumed.
    fn parse_let_term(&mut self) -> CarcaraResult<Rc<Term>> {
        self.expect_token(Token::OpenParen)?;

        // Since the let binding semantics is *simultaneous*, we first parse all bindings, and only
        // then add them to the symbol table.
        let bindings = self.parse_sequence(
            |p| {
                p.expect_token(Token::OpenParen)?;
                let name = p.expect_symbol()?;
                let value = p.parse_term()?;
                p.expect_token(Token::CloseParen)?;
                Ok((name, value))
            },
            true,
        )?;

        self.state.symbol_table.push_scope();
        for (name, value) in &bindings {
            let sort = self.pool.sort(value);
            self.insert_sorted_var((name.clone(), sort));
        }

        let inner = self.parse_term()?;
        self.expect_token(Token::CloseParen)?;

        self.state.symbol_table.pop_scope();

        if self.config.expand_lets {
            let substitution = bindings
                .into_iter()
                .map(|(name, value)| {
                    let var = Term::new_var(name, self.pool.sort(&value));
                    (self.pool.add(var), value)
                })
                .collect();

            let result = Substitution::new(self.pool, substitution)
                .unwrap()
                .apply(self.pool, &inner);

            Ok(result)
        } else {
            Ok(self.pool.add(Term::Let(BindingList(bindings), inner)))
        }
    }

    /// Parses an annotated term, of the form `(! <term> <attribute>+)`. This method assumes that
    /// the `(` and `!` tokens were already consumed.
    ///
    /// The two supported attributes are `:named` and `:pattern`, though the latter is ignored. If
    /// any other attribute is present, an error will be returned.
    fn parse_annotated_term(&mut self) -> CarcaraResult<Rc<Term>> {
        let inner = self.parse_term()?;
        self.parse_sequence(
            |p| {
                let attribute = p.expect_keyword()?;
                match attribute.as_str() {
                    "named" => {
                        // If the term has a `:named` attribute, we introduce a new nullary function
                        // definition that maps the name to the term
                        let name = p.expect_symbol()?;
                        let func_def = FunctionDef {
                            params: Vec::new(),
                            body: inner.clone(),
                        };
                        p.state.function_defs.insert(name, func_def);
                        Ok(())
                    }

                    // We allow unknown attributes, and just ignore them
                    _ => match p.current_token {
                        // If the argument is a list, we consume it until the `)` token
                        Token::OpenParen => {
                            p.next_token()?;
                            p.ignore_until_close_parens()
                        }

                        // If the attribute has no argument, we don't do anything
                        Token::Keyword(_) | Token::CloseParen | Token::Eof => Ok(()),

                        // If the argument is a single token, we consume it
                        _ => {
                            p.next_token()?;
                            Ok(())
                        }
                    },
                }
            },
            true,
        )?;
        Ok(inner)
    }

    fn parse_indexed_operator(&mut self) -> CarcaraResult<(ParamOperator, Vec<Constant>)> {
        let op_symbol = self.expect_symbol()?;

        if let Some(value) = op_symbol.strip_prefix("bv") {
            let parsed_value = value.parse::<Integer>().unwrap();
            let args = self.parse_sequence(Self::parse_term, true)?;
            let mut constant_args = Vec::new();
            for arg in args {
                if let Some(i) = arg.as_signed_integer() {
                    constant_args.push(Constant::Integer(i));
                } else {
                    return Err(Error::Parser(
                        ParserError::ExpectedIntegerConstant(arg.clone()),
                        self.current_position,
                    ));
                }
            }
            constant_args.insert(0, Constant::Integer(parsed_value));
            return Ok((ParamOperator::BvConst, constant_args));
        }

        let op = ParamOperator::from_str(op_symbol.as_str()).map_err(|_| {
            Error::Parser(
                ParserError::InvalidIndexedOp(op_symbol),
                self.current_position,
            )
        })?;
        let args = self.parse_sequence(Self::parse_term, true)?;
        let mut constant_args = Vec::new();
        for arg in args {
            if let Some(i) = arg.as_signed_integer() {
                constant_args.push(Constant::Integer(i));
            } else {
                return Err(Error::Parser(
                    ParserError::ExpectedIntegerConstant(arg.clone()),
                    self.current_position,
                ));
            }
        }
        Ok((op, constant_args))
    }

    fn parse_qualified_operator(&mut self) -> CarcaraResult<(ParamOperator, Rc<Term>)> {
        let op_symbol = self.expect_symbol()?;
        let op = ParamOperator::from_str(op_symbol.as_str()).map_err(|_| {
            Error::Parser(
                ParserError::InvalidQualifiedOp(op_symbol),
                self.current_position,
            )
        })?;
        let sort = self.parse_sort()?;
        self.expect_token(Token::CloseParen)?;
        Ok((op, sort))
    }

    /// Constructs, check operation arguments and sort checks an indexed operation term.
    fn make_indexed_op(
        &mut self,
        op: ParamOperator,
        op_args: Vec<Constant>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();
        let sorts: Vec<_> = sorts.iter().map(|s| s.as_sort().unwrap()).collect();
        match &op {
            ParamOperator::BvConst => {
                assert_num_args(&op_args, 2)?;
                assert_num_args(&args, 0)?;
                let value = op_args[0].as_integer().unwrap();
                let width = op_args[1].as_integer().unwrap();
                assert_indexed_op_args_value(&[op_args[0].clone()], 0..)?;
                assert_indexed_op_args_value(&[op_args[1].clone()], 1..)?;
                return Ok(self.pool.add(Term::Const(Constant::BitVec(value, width))));
            }
            ParamOperator::BvExtract => {
                /*
                ((_ extract i j) (_ BitVec m) (_ BitVec n))

                where
                - i, j, m, n are numerals
                - m > i ≥ j ≥ 0,
                - n = i - j + 1
                 */
                assert_num_args(&op_args, 2)?;
                assert_num_args(&args, 1)?;
                if !matches!(sorts[0], Sort::BitVec(_)) {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                for arg in &op_args {
                    SortError::assert_eq(&Sort::Int, &arg.sort())?;
                }
                assert_indexed_op_args_value(&op_args, 0..)?;
                let i = op_args[0].as_integer().unwrap();
                let j = op_args[1].as_integer().unwrap();
                let Sort::BitVec(m) = sorts[0].clone() else {
                    unreachable!()
                };
                if !(m > i && i >= j && j >= Integer::ZERO) {
                    return Err(ParserError::InvalidExtractArgs(
                        i.to_usize().unwrap(),
                        j.to_usize().unwrap(),
                        m.to_usize().unwrap(),
                    ));
                }
            }
            ParamOperator::BvBitOf | ParamOperator::ZeroExtend | ParamOperator::SignExtend => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::Int, &op_args[0].sort())?;
                if !matches!(sorts[0], Sort::BitVec(_)) {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                assert_indexed_op_args_value(&op_args, 0..)?;
            }
            ParamOperator::RePower => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                SortError::assert_eq(&Sort::Int, &op_args[0].sort())?;
                SortError::assert_eq(&Sort::RegLan, sorts[0])?;
                assert_indexed_op_args_value(&op_args, 0..)?;
            }
            ParamOperator::ReLoop => {
                assert_num_args(&op_args, 2)?;
                assert_num_args(&args, 1)?;
                for arg in &op_args {
                    SortError::assert_eq(&Sort::Int, &arg.sort())?;
                }
                SortError::assert_eq(&Sort::RegLan, sorts[0])?;
                assert_indexed_op_args_value(&op_args, 0..)?;
            }
            ParamOperator::ArrayConst => return Err(ParserError::InvalidIndexedOp(op.to_string())),
        }
        let op_args = op_args
            .into_iter()
            .map(|c| self.pool.add(Term::Const(c)))
            .collect();
        Ok(self.pool.add(Term::ParamOp { op, op_args, args }))
    }

    /// Constructs and sort checks a qualified operation term
    fn make_qualified_op(
        &mut self,
        op: ParamOperator,
        op_sort: Rc<Term>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();
        let sorts: Vec<_> = sorts.iter().map(|s| s.as_sort().unwrap()).collect();
        match &op {
            ParamOperator::ArrayConst => {
                assert_num_args(&args, 1)?;
                SortError::assert_array_sort(
                    self.pool,
                    None,
                    Some(sorts[0]),
                    op_sort.as_sort().unwrap(),
                )?;
            }
            _ => return Err(ParserError::InvalidQualifiedOp(op.to_string())),
        }
        let op_args = vec![op_sort];
        Ok(self.pool.add(Term::ParamOp { op, op_args, args }))
    }

    /// Parses any term that starts with `(`, that is, any term that is not a constant or a
    /// variable. This method assumes that the `(` token was already consumed.
    fn parse_application(&mut self) -> CarcaraResult<Rc<Term>> {
        let head_pos = self.current_position;
        match &self.current_token {
            &Token::ReservedWord(reserved) => {
                self.next_token()?;
                match reserved {
                    Reserved::Underscore => {
                        let (op, op_args) = self.parse_indexed_operator()?;
                        self.make_indexed_op(op, op_args, Vec::new())
                            .map_err(|err| Error::Parser(err, head_pos))
                    }
                    Reserved::As => {
                        let (op, sort) = self.parse_qualified_operator()?;
                        self.make_qualified_op(op, sort, Vec::new())
                            .map_err(|err| Error::Parser(err, head_pos))
                    }
                    Reserved::Exists => self.parse_binder(Binder::Exists),
                    Reserved::Forall => self.parse_binder(Binder::Forall),
                    Reserved::Choice => self.parse_binder(Binder::Choice),
                    Reserved::Lambda => self.parse_binder(Binder::Lambda),
                    Reserved::Bang => self.parse_annotated_term(),
                    Reserved::Let => self.parse_let_term(),
                    _ => Err(Error::Parser(
                        ParserError::UnexpectedToken(Token::ReservedWord(reserved)),
                        head_pos,
                    )),
                }
            }
            // Here, I would like to use an `if let` guard, like:
            //
            //     Token::Symbol(s) if let Ok(operator) = Operator::from_str(s) => { ... }
            //
            // However, `if let` guards are still nightly only. For more info, see:
            // https://github.com/rust-lang/rust/issues/51114
            Token::Symbol(s) if Operator::from_str(s).is_ok() => {
                let operator = Operator::from_str(s).unwrap();
                self.next_token()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.make_op(operator, args)
                    .map_err(|err| Error::Parser(err, head_pos))
            }
            Token::Symbol(s) if self.state.function_defs.get(s).is_some() => {
                let head_pos = self.current_position;
                let func_name = self.expect_symbol()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                let func = self.state.function_defs.get(&func_name).unwrap();

                func.apply(self.pool, args)
                    .map_err(|err| Error::Parser(err, head_pos))
            }
            Token::OpenParen => {
                self.next_token()?;
                match self.current_token {
                    Token::ReservedWord(Reserved::Underscore) => {
                        self.next_token()?;
                        let (op, op_args) = self.parse_indexed_operator()?;
                        let args = self.parse_sequence(Self::parse_term, true)?;
                        self.make_indexed_op(op, op_args, args)
                            .map_err(|err| Error::Parser(err, head_pos))
                    }
                    Token::ReservedWord(Reserved::As) => {
                        self.next_token()?;
                        let (op, op_sort) = self.parse_qualified_operator()?;
                        let args = self.parse_sequence(Self::parse_term, true)?;
                        self.make_qualified_op(op, op_sort, args)
                            .map_err(|err| Error::Parser(err, head_pos))
                    }
                    _ => {
                        let func = self.parse_application()?;
                        let args = self.parse_sequence(Self::parse_term, true)?;
                        self.make_app(func, args)
                            .map_err(|err| Error::Parser(err, head_pos))
                    }
                }
            }
            _ => {
                let func = self.parse_term()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.make_app(func, args)
                    .map_err(|err| Error::Parser(err, head_pos))
            }
        }
    }

    fn make_sort(&mut self, name: String, args: Vec<Rc<Term>>) -> Result<Rc<Term>, ParserError> {
        let sort = match name.as_str() {
            "Bool" | "Int" | "Real" | "String" | "RegLan" if !args.is_empty() => {
                Err(ParserError::WrongNumberOfArgs(0.into(), args.len()))
            }
            "Bool" => Ok(Sort::Bool),
            "Int" => Ok(Sort::Int),
            "Real" => Ok(Sort::Real),
            "String" => Ok(Sort::String),
            "RegLan" => Ok(Sort::RegLan),
            "Array" => match args.as_slice() {
                [x, y] => Ok(Sort::Array(x.clone(), y.clone())),
                _ => Err(ParserError::WrongNumberOfArgs(2.into(), args.len())),
            },
            other if self.state.sort_defs.get(other).is_some() => {
                let def = self.state.sort_defs.get(other).unwrap();
                return if def.params.len() != args.len() {
                    Err(ParserError::WrongNumberOfArgs(
                        def.params.len().into(),
                        args.len(),
                    ))
                } else if def.params.is_empty() {
                    Ok(def.body.clone())
                } else {
                    let substitution = def
                        .params
                        .iter()
                        .cloned()
                        .map(|name| self.pool.add(Term::Sort(Sort::Atom(name, Vec::new()))))
                        .zip(args)
                        .collect();

                    let result = Substitution::new(self.pool, substitution)
                        .unwrap()
                        .apply(self.pool, &def.body);
                    Ok(result)
                };
            }
            _ => match self.state.sort_declarations.get(&name) {
                Some(arity) if *arity == args.len() => Ok(Sort::Atom(name, args)),
                Some(arity) => Err(ParserError::WrongNumberOfArgs((*arity).into(), args.len())),
                None => Err(ParserError::UndefinedSort(name)),
            },
        }?;
        Ok(self.pool.add(Term::Sort(sort)))
    }

    fn make_indexed_sort(
        &mut self,
        name: String,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        match name.as_str() {
            "BitVec" => {
                if args.len() != 1 {
                    return Err(ParserError::WrongNumberOfArgs(1.into(), args.len()));
                }
                if let Some(width) = args[0].as_integer() {
                    Ok(self.pool.add(Term::Sort(Sort::BitVec(width))))
                } else {
                    Err(ParserError::ExpectedIntegerConstant(args[0].clone()))
                }
            }
            _ => Err(ParserError::UndefinedSort(name)),
        }
    }

    /// Parses a sort.
    fn parse_sort(&mut self) -> CarcaraResult<Rc<Term>> {
        let pos = self.current_position;
        let (name, args) = match self.next_token()?.0 {
            Token::Symbol(s) => (s, Vec::new()),
            Token::OpenParen if self.current_token == Token::ReservedWord(Reserved::Underscore) => {
                self.next_token()?;
                let name = self.expect_symbol()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                return self
                    .make_indexed_sort(name, args)
                    .map_err(|e| Error::Parser(e, pos));
            }
            Token::OpenParen => {
                let name = self.expect_symbol()?;
                let args = self.parse_sequence(Parser::parse_sort, true)?;
                (name, args)
            }
            other => {
                return Err(Error::Parser(ParserError::UnexpectedToken(other), pos));
            }
        };
        self.make_sort(name, args)
            .map_err(|e| Error::Parser(e, pos))
    }
}
