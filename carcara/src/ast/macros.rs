//! Some useful helper macros.

/// A macro to help pattern match terms.
///
/// Since a term holds references to its subterms in `Vec`s and `Rc`s, pattern matching a complex
/// term can be difficult and verbose. This macro helps with that. Given a term and a pattern with
/// which to match it, this macro will deconstruct the term and (if it matches the pattern) return
/// the subterms specified by the pattern.
///
/// The syntax to use this macro is `match_term!(<pattern> = <value>)`, where `<value>` is an
/// expression of type `Term` or `Rc<Term>`, and `<pattern>` is an s-expression that specifies the
/// pattern with which to match the given term. Free variables in the pattern will match any term,
/// and this term will be returned by the macro.
///
/// The return type of this macro is `Option<T>` where the exact structure of `T` will reflect the
/// pattern given. For example, `match_term!((and (= a b) c) = term)` will return an
/// `Option<((&Rc<Term>, &Rc<Term>), &Rc<Term>)>`. If the term does not match the pattern, the macro
/// returns `None`.
///
/// # Examples
///
/// Removing two leading negations from a term:
/// ```
/// # use carcara::{ast::*, build_term, match_term};
/// # let mut pool = PrimitivePool::new();
/// # let t = build_term!(pool, (not (not {pool.bool_false()})));
/// let p = match_term!((not (not p)) = t).unwrap();
/// ```
///
/// Deconstructing complex nested terms:
/// ```
/// # use carcara::{ast::*, match_term, parser::*};
/// # pub fn parse_term(input: &str) -> Rc<Term> {
/// #     let mut pool = PrimitivePool::new();
/// #     let mut parser = Parser::new(&mut pool, Config::new(), input.as_bytes()).unwrap();
/// #     parser.parse_term().unwrap()
/// # }
/// # let t = parse_term("(and (=> false false) (> (+ 0 0) 0))");
/// let ((p, q), ((a, b), c)) = match_term!((and (=> p q) (> (+ a b) c)) = t).unwrap();
/// ```
///
/// Pattern matching against boolean constants:
/// ```
/// # use carcara::{ast::*, build_term, match_term};
/// # let mut pool = PrimitivePool::new();
/// # let t = build_term!(pool, (or {pool.bool_false()} {pool.bool_false()}));
/// let (p, ()) = match_term!((or p false) = t).unwrap();
/// ```
///
/// Pattern matching quantifier terms:
/// ```
/// # use carcara::{ast::*, match_term, parser::*};
/// # pub fn parse_term(input: &str) -> Rc<Term> {
/// #     let mut pool = PrimitivePool::new();
/// #     let mut parser = Parser::new(&mut pool, Config::new(), input.as_bytes()).unwrap();
/// #     parser.parse_term().unwrap()
/// # }
/// # let t = parse_term("(forall ((x Int) (y Int)) (> x y))");
/// let (bindings, (x, y)) = match_term!((forall ... (> x y)) = t).unwrap();
/// ```
///
/// Pattern matching against a variable number of arguments:
/// ```
/// # use carcara::{ast::*, build_term, match_term};
/// # let mut pool = PrimitivePool::new();
/// # let t = build_term!(pool, (and {pool.bool_false()} {pool.bool_false()}));
/// let args: &[Rc<Term>] = match_term!((and ...) = t).unwrap();
/// ```
#[macro_export]
macro_rules! match_term {
    (true = $var:expr $(, $flag:ident)?) => {
        if $var.is_bool_true() { Some(()) } else { None }
    };
    (false = $var:expr $(, $flag:ident)?) => {
        if $var.is_bool_false() { Some(()) } else { None }
    };
    (0 = $var:expr $(, $flag:ident)?) => {
        if let Some(i) = $var.as_integer() {
            if i == 0 { Some(()) } else { None }
        } else { None }
    };
    ("" = $var:expr $(, $flag:ident)?) => {
        if $var.is_empty_string() { Some(()) } else { None }
    };
    ((forall ... $args:tt) = $var:expr) => {
        if let $crate::ast::Term::Binder($crate::ast::Binder::Forall, bindings, inner) =
            &$var as &$crate::ast::Term
        {
            match_term!($args = inner).and_then(|inner| Some((bindings, inner)))
        } else {
            None
        }
    };
    ((exists ... $args:tt) = $var:expr) => {
        if let $crate::ast::Term::Binder($crate::ast::Binder::Exists, bindings, inner) =
            &$var as &$crate::ast::Term
        {
            match_term!($args = inner).and_then(|inner| Some((bindings, inner)))
        } else {
            None
        }
    };
    ($bind:ident = $var:expr) => { Some($var) };
    (((_ $indexed_op:tt $($op_args:tt)+) $($args:tt)+) = $var:expr) => {{
        if let $crate::ast::Term::ParamOp {
            op: match_term!(@GET_VARIANT $indexed_op),
            op_args,
            args,
        } = &$var as &$crate::ast::Term {
            match_term!(@ARGS ($($op_args)+) = op_args.as_slice()).and_then(|op_args| {
                match_term!(@ARGS ($($args)+) = args.as_slice()).map(|args| {
                    (op_args, args)
                })
            })
        } else {
            None
        }
    }};
    (($op:tt $($args:tt)+) = $var:expr) => {{
        if let $crate::ast::Term::Op(match_term!(@GET_VARIANT $op), args) =
            &$var as &$crate::ast::Term
        {
            match_term!(@ARGS ($($args)+) = args.as_slice())
        } else {
            None
        }
    }};

    (@ARGS (...) = $var:expr) => { Some($var) };
    (@ARGS ($arg:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg) = $var)
    };
    (@ARGS ($arg1:tt $arg2:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2) = $var)
    };
    (@ARGS ($arg1:tt $arg2:tt $arg3:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2, arg3: $arg3) = $var)
    };
    (@ARGS ($arg1:tt $arg2:tt $arg3:tt $arg4:tt) = $var:expr) => {
        match_term!(@ARGS_IDENT (arg1: $arg1, arg2: $arg2, arg3: $arg3, arg4: $arg4) = $var)
    };
    (@ARGS_IDENT ( $($name:ident : $arg:tt),* ) = $var:expr) => {
        if let [$($name),*] = $var {
            #[allow(unused_parens)]
            #[allow(clippy::manual_map)]
            match ($(match_term!($arg = $name)),*) {
                ($(Some($name)),*) => Some(($($name),*)),
                _ => None,
            }
        } else {
            None
        }
    };
    (@GET_VARIANT not)      => { $crate::ast::Operator::Not };
    (@GET_VARIANT =>)       => { $crate::ast::Operator::Implies };
    (@GET_VARIANT and)      => { $crate::ast::Operator::And };
    (@GET_VARIANT or)       => { $crate::ast::Operator::Or };
    (@GET_VARIANT xor)      => { $crate::ast::Operator::Xor };
    (@GET_VARIANT =)        => { $crate::ast::Operator::Equals };
    (@GET_VARIANT distinct) => { $crate::ast::Operator::Distinct };
    (@GET_VARIANT ite)      => { $crate::ast::Operator::Ite };
    (@GET_VARIANT +)        => { $crate::ast::Operator::Add };
    (@GET_VARIANT -)        => { $crate::ast::Operator::Sub };
    (@GET_VARIANT *)        => { $crate::ast::Operator::Mult };
    (@GET_VARIANT div)      => { $crate::ast::Operator::IntDiv };
    (@GET_VARIANT /)        => { $crate::ast::Operator::RealDiv };
    (@GET_VARIANT mod)      => { $crate::ast::Operator::Mod };
    (@GET_VARIANT <)        => { $crate::ast::Operator::LessThan };
    (@GET_VARIANT >)        => { $crate::ast::Operator::GreaterThan };
    (@GET_VARIANT <=)       => { $crate::ast::Operator::LessEq };
    (@GET_VARIANT >=)       => { $crate::ast::Operator::GreaterEq };
    (@GET_VARIANT bbterm)   => { $crate::ast::Operator::BvBbTerm };
    (@GET_VARIANT bvult)    => { $crate::ast::Operator::BvULt };
    (@GET_VARIANT bvadd)    => { $crate::ast::Operator::BvAdd };
    (@GET_VARIANT cl)    => { $crate::ast::Operator::Cl };
    (@GET_VARIANT delete)    => { $crate::ast::Operator::Delete };

    (@GET_VARIANT extract)     => { $crate::ast::ParamOperator::BvExtract };
    (@GET_VARIANT bit_of)      => { $crate::ast::ParamOperator::BvBitOf };
    (@GET_VARIANT zero_extend) => { $crate::ast::ParamOperator::ZeroExtend };
    (@GET_VARIANT sign_extend) => { $crate::ast::ParamOperator::SignExtend };

    (@GET_VARIANT strconcat) => { $crate::ast::Operator::StrConcat };
    (@GET_VARIANT strsubstr) => { $crate::ast::Operator::Substring };
    (@GET_VARIANT strlen)    => { $crate::ast::Operator::StrLen };

    (@GET_VARIANT strinre)    => { $crate::ast::Operator::StrInRe };
    (@GET_VARIANT reinter)    => { $crate::ast::Operator::ReIntersection };
}

/// A variant of `match_term` that returns a `Result<_, CheckerError>` instead of an `Option`.
///
/// The error returned by this macro is always `CheckerError::TermOfWrongForm`.
#[macro_export]
macro_rules! match_term_err {
    ($pat:tt = $var:expr) => {{
        let var = $var;
        match_term!($pat = var).ok_or_else(|| {
            // Note: Annoyingly, the `stringify!` macro can't fully keep whitespace when turning a
            // token tree into a string. It will add spaces when they are required for the tokens
            // to make sense, but remove any other whitespace. This means that, for instance, the
            // token tree `(not (and ...))` will be stringified to `(not(and ...))`. One way to
            // solve this would be to create a procedural macro that uses the tokens `span` to
            // infer how many characters there were between each token, and assume they were all
            // spaces
            $crate::checker::error::CheckerError::TermOfWrongForm(stringify!($pat), var.clone())
        })
    }};
}

/// A macro to help build new terms.
///
/// This macro takes two arguments: the `TermPool` with which to build the term, and an s-expression
/// representing the term to be built. Subterms in that s-expression that are surrounded by `{}` are
/// evaluated as expressions, and they should have type `Rc<Term>`.
///
/// # Examples
///
/// Building the term `(and true (not false))`:
/// ```
/// # use carcara::{ast::*, build_term, match_term};
/// let mut pool = PrimitivePool::new();
/// let t = build_term!(pool, (and {pool.bool_true()} (not {pool.bool_false()})));
/// assert!(match_term!((and true (not false)) = t).is_some());
/// ```
#[macro_export]
macro_rules! build_term {
    ($pool:expr, true) => { $pool.bool_true() };
    ($pool:expr, false) => { $pool.bool_false() };
    ($pool:expr, $int:literal) => { $pool.add(Term::Const(Constant::Integer($int.into()))) };
    ($pool:expr, {$terminal:expr}) => { $terminal };
    ($pool:expr, ((_ $indexed_op:tt $($op_args:tt)+) $($args:tt)+)) => {{
        let term = $crate::ast::Term::ParamOp {
            op: match_term!(@GET_VARIANT $indexed_op),
            op_args: vec![ $(build_term!($pool, $op_args)),+ ],
            args: vec![ $(build_term!($pool, $args)),+ ],
        };
        $pool.add(term)
    }};
    ($pool:expr, ($op:tt $($args:tt)+)) => {{
        let term = $crate::ast::Term::Op(
            match_term!(@GET_VARIANT $op),
            vec![ $(build_term!($pool, $args)),+ ],
        );
        $pool.add(term)
    }};
}

/// Implements `FromStr` and `Display` for an enum, given a mapping from each variant to a string
/// literal.
///
/// This macros only supports enums that don't hold any data in any of their variants. The error
/// type for the implementation of `FromStr` will be `()`.
///
/// # Examples
///
// Since this macro is not exported, and since doctests are run as if they were a different crate,
// it's impossible to test this macro. To avoid test errors, we interpret this block as text. This
// is not a perfect solution, since we lose syntax highlighting.
// See https://github.com/rust-lang/rust/issues/63193
/// ```text
/// #[derive(Debug, PartialEq)]
/// enum Foo {
///     A,
///     B,
///     C,
/// }
///
/// impl_str_conversion_traits!(Foo {
///     A: "a",
///     B: "b",
///     C: "c",
/// });
///
/// fn main() {
///     assert_eq!(Foo::from_str("a"), Ok(Foo::A));
///     assert_eq!(format!("{}", Foo::B), "b");
///     assert_eq!(Foo::from_str("d"), Err(()));
/// }
/// ```
macro_rules! impl_str_conversion_traits {
    ($enum_name:ident { $($variant:ident: $str:literal),* $(,)? }) => {
        impl std::str::FromStr for $enum_name {
            type Err = ();

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    $($str => Ok($enum_name::$variant),)*
                    _ => Err(()),
                }
            }
        }

        impl std::fmt::Display for $enum_name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                let s = match self {
                    $($enum_name::$variant => $str,)*
                };
                write!(f, "{}", s)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::{pool::PrimitivePool, *};
    use crate::parser::tests::{parse_term, parse_terms};

    #[test]
    fn test_match_term() {
        let mut p = PrimitivePool::new();
        let [one, two, five] = [1, 2, 5].map(|n| p.add(Term::new_int(n)));

        let term = parse_term(&mut p, "(= (= (not false) (= true false)) (not true))");
        let ((a, (b, c)), d) = match_term!((= (= (not a) (= b c)) (not d)) = &term).unwrap();
        assert_eq!(a, &p.bool_false());
        assert_eq!(b, &p.bool_true());
        assert_eq!(c, &p.bool_false());
        assert_eq!(d, &p.bool_true());

        let term = parse_term(&mut p, "(ite (not true) (- 2 2) (* 1 5))");
        let (a, b, c) = match_term!((ite (not a) b c) = &term).unwrap();
        assert_eq!(a, &p.bool_true());
        assert_eq!(
            b,
            &p.add(Term::Op(Operator::Sub, vec![two.clone(), two.clone()])),
        );
        assert_eq!(c.as_ref(), &Term::Op(Operator::Mult, vec![one, five]));

        // Test the `...` pattern
        let term = parse_term(&mut p, "(not (and true false true))");
        match match_term!((not (and ...)) = &term) {
            Some([a, b, c]) => {
                assert_eq!(&p.bool_true(), a);
                assert_eq!(&p.bool_false(), b);
                assert_eq!(&p.bool_true(), c);
            }
            _ => panic!(),
        }
        let term = parse_term(&mut p, "(and (or false true) (= 2 2))");
        match match_term!((and (or ...) (= ...)) = &term) {
            Some(([a, b], [c, d])) => {
                assert_eq!(&p.bool_false(), a);
                assert_eq!(&p.bool_true(), b);
                assert_eq!(&two, c);
                assert_eq!(&two, d);
            }
            _ => panic!(),
        }

        let term = parse_term(&mut p, "((_ extract 3 1) (_ bv0 5))");
        let ((i, j), b): ((&Rc<Term>, &Rc<Term>), &Rc<Term>) =
            match_term!(((_ extract i j) b) = term).unwrap();
        assert_eq!(3, i.as_integer().unwrap());
        assert_eq!(1, j.as_integer().unwrap());
        assert_eq!(Term::new_bv(0, 5), **b);

        let term = parse_term(&mut p, "((_ bit_of 2) (_ bv0 5))");
        let (i, b): (&Rc<Term>, &[Rc<Term>]) = match_term!(((_ bit_of i) ...) = term).unwrap();
        assert_eq!(2, i.as_integer().unwrap());
        assert_eq!(Term::new_bv(0, 5), *b[0]);

        let term = parse_term(&mut p, "((_ zero_extend 3) (_ bv0 5))");
        let (i, b): (&[Rc<Term>], &[Rc<Term>]) =
            match_term!(((_ zero_extend ...) ...) = term).unwrap();
        assert_eq!(3, i[0].as_integer().unwrap());
        assert_eq!(Term::new_bv(0, 5), *b[0]);
    }

    #[test]
    fn test_build_term() {
        let definitions = "
            (declare-fun a () Int)
            (declare-fun b () Int)
            (declare-fun p () Bool)
            (declare-fun q () Bool)
        ";
        let mut pool = PrimitivePool::new();
        let bool_sort = pool.add(Term::Sort(Sort::Bool));
        let int_sort = pool.add(Term::Sort(Sort::Int));

        let [one, two, three] = [1, 2, 3].map(|n| pool.add(Term::new_int(n)));
        let [a, b] = ["a", "b"].map(|s| pool.add(Term::new_var(s, int_sort.clone())));
        let [p, q] = ["p", "q"].map(|s| pool.add(Term::new_var(s, bool_sort.clone())));
        let zeros = pool.add(Term::new_bv(0, 6));

        let cases = [
            ("(= a b)", build_term!(pool, (= {a} {b}))),
            (
                "(= 1 2)",
                build_term!(pool, (= {one.clone()} {two.clone()})),
            ),
            ("(not true)", build_term!(pool, (not {pool.bool_true()}))),
            (
                "(or p false)",
                build_term!(pool, (or {p.clone()} {pool.bool_false()})),
            ),
            (
                "(and (=> p q) (ite p false (= 1 3)))",
                build_term!(pool, (and
                    (=> {p.clone()} {q.clone()})
                    (ite {p.clone()} {pool.bool_false()} (= {one.clone()} {three.clone()}))
                )),
            ),
            (
                "(distinct p q true)",
                build_term!(pool, (distinct {p} {q} {pool.bool_true()})),
            ),
            (
                "(or (not (= 2 3)) (= 1 1))",
                build_term!(pool, (or
                    (not (= {two} {three}))
                    (= {one.clone()} {one})
                )),
            ),
            (
                "((_ bit_of 1) ((_ extract 3 2) #b000000))",
                build_term!(pool,
                    ((_ bit_of 1) ((_ extract 3 2) {zeros}))
                ),
            ),
            ("(and true false)", build_term!(pool, (and true false))),
        ];

        for (s, got) in &cases {
            let [expected] = parse_terms(&mut pool, definitions, [s]);
            assert_eq!(&expected, got);
        }
    }
}
