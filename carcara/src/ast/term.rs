use super::{PrimitivePool, Rc, TermPool};
use crate::CheckerError;
use rug::{Integer, Rational};
use std::{collections::HashSet, hash::Hash, ops::Deref};

/// A term.
///
/// Many additional methods are implemented in [`Rc<Term>`].
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A constant term.
    Const(Constant),

    /// A variable, consisting of an identifier and a sort.
    Var(String, Rc<Term>),

    /// An application of a function to one or more terms.
    App(Rc<Term>, Vec<Rc<Term>>),

    /// An application of a bulit-in operator to one or more terms.
    Op(Operator, Vec<Rc<Term>>),

    /// A sort.
    Sort(Sort),

    /// A binder term. This can be either a quantifier term (`forall`/`exists`), a `choice` term, or
    /// a `lambda` term.
    Binder(Binder, BindingList, Rc<Term>),

    /// A `let` binder term.
    Let(BindingList, Rc<Term>),

    /// A parameterized operation term, that is, an operation term whose operator receives extra
    /// parameters.
    ///
    /// This can be either:
    /// - An `indexed` operation term, that uses an indexed operator denoted by the `(_ ...)`
    ///   syntax. In this case, the operator parameters must be constants.
    /// - A `qualified` operation term, that uses a qualified operator denoted by the `(as ...)`
    ///   syntax. In this case, the single operator parameter must be a sort.
    ParamOp {
        op: ParamOperator,
        op_args: Vec<Rc<Term>>,
        args: Vec<Rc<Term>>,
    },
}

/// The sort of a term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Sort {
    /// A function sort.
    ///
    /// The last term indicates the return sort of the function. The remaining terms are the sorts
    /// of the parameters of the function.
    Function(Vec<Rc<Term>>),

    /// A user-declared sort, from a `declare-sort` command.
    ///
    /// The associated string is the sort name, and the associated terms are the sort arguments for
    /// this sort.
    Atom(String, Vec<Rc<Term>>),

    /// The `Bool` primitive sort.
    Bool,

    /// The `Int` primitive sort.
    Int,

    /// The `Real` primitive sort.
    Real,

    /// The `String` primitive sort.
    String,

    /// The `RegLan` primitive sort.
    RegLan,

    /// An `Array` sort.
    ///
    /// The two associated terms are the sort arguments for this sort.
    Array(Rc<Term>, Rc<Term>),
    ///  `BitVec` sort.
    ///
    /// The associated term is the BV width of this sort.
    BitVec(Integer),

    /// The sort of RARE lists.
    RareList,

    /// The sort of sorts.
    Type,
}

/// A variable and an associated sort.
pub type SortedVar = (String, Rc<Term>);

/// A constant term.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Constant {
    /// An integer constant term.
    Integer(Integer),

    /// A real constant term.
    Real(Rational),

    /// A string literal term.
    String(String),

    BitVec(Integer, Integer),
}

/// A binder, either a quantifier (`forall` or `exists`), `choice`, or `lambda`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Binder {
    /// The `forall` quantifier.
    Forall,

    /// The `exists` quantifier.
    Exists,

    /// The `choice` binder.
    Choice,

    /// The `lambda` binder.
    Lambda,
}

/// A list of bindings, where each binding is a variable associated with a term.
///
/// Depending on the context, it can be a "sort" binding list (like the ones present in quantifier
/// terms) where the associated term of each variable is its sort; or a "value" binding list (like
/// the ones present in `let` terms) where the associated term of each variable is its bound value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BindingList(pub Vec<SortedVar>);

/// The operator of an operation term.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operator {
    /// The `true` boolean constant.
    True,

    /// The `false` boolean constant.
    False,

    // Logic
    /// The `not` operator.
    Not,

    /// The `=>` operator.
    Implies,

    /// The `and` operator.
    And,

    /// The `or` operator.
    Or,

    /// The `xor` operator.
    Xor,

    /// The `=` operator.
    Equals,

    /// The `distinct` operator.
    Distinct,

    /// The `ite` operator.
    Ite,

    // Arithmetic
    /// The `+` operator.
    Add,

    /// The `-` operator.
    Sub,

    /// The `*` operator.
    Mult,

    /// The `div` operator.
    IntDiv,

    /// The `/` operator.
    RealDiv,

    /// The `mod` operator.
    Mod,

    /// The `abs` operator.
    Abs,

    /// The `<` operator.
    LessThan,

    /// The `>` operator.
    GreaterThan,

    /// The `<=` operator.
    LessEq,

    /// The `>=` operator.
    GreaterEq,

    /// The `to_real` operator.
    ToReal,

    /// The `to_int` operator.
    ToInt,

    /// The `is_int` operator.
    IsInt,

    // Arrays
    /// The `select` operator.
    Select,

    /// The `store` operator.
    Store,

    // Strings
    /// The `str.++` operator.
    StrConcat,

    /// The `str.len` operator.
    StrLen,

    /// The `str.<` operator.
    StrLessThan,

    /// The `str.<=` operator.
    StrLessEq,

    /// The `str.at` operator.
    CharAt,

    /// The `str.substr` operator.
    Substring,

    /// The `str.prefixof` operator.
    PrefixOf,

    /// The `str.suffixof` operator.
    SuffixOf,

    /// The `str.contains` operator.
    Contains,

    /// The `str.indexof` operator.
    IndexOf,

    /// The `str.replace` operator.
    Replace,

    /// The `str.replace_all` operator.
    ReplaceAll,

    /// The `str.replace_re` operator.
    ReplaceRe,

    /// The `str.replace_re_all` operator.
    ReplaceReAll,

    /// The `str.is_digit` operator.
    StrIsDigit,

    /// The `str.to_code` operator.
    StrToCode,

    /// The `str.from_code` operator.
    StrFromCode,

    /// The `str.to_int` operator.
    StrToInt,

    /// The `str.from_int` operator.
    StrFromInt,

    // Regular Expressions
    /// The `str.to_re` operator.
    StrToRe,

    /// The `str.in_re` operator.
    StrInRe,

    /// The `re.none` operator.
    ReNone,

    /// The `re.all` operator.
    ReAll,

    /// The `re.allchar` operator.
    ReAllChar,

    /// The `re.++` operator.
    ReConcat,

    /// The `re.union` operator.
    ReUnion,

    /// The `re.inter` operator.
    ReIntersection,

    /// The `re.*` operator.
    ReKleeneClosure,

    /// The `re.comp` operator.
    ReComplement,

    /// The `re.diff` operator.
    ReDiff,

    /// The `re.+` operator.
    ReKleeneCross,

    /// The `re.opt` operator.
    ReOption,

    /// The `re.range` operator.
    ReRange,

    // BV operators (unary)
    BvNot,
    BvNeg,
    // BV operators (binary, left-assoc)
    BvAnd,
    BvOr,
    BvAdd,
    BvMul,
    // BV operators (binary)
    BvUDiv,
    BvURem,
    BvShl,
    BvLShr,
    BvULt,

    BvConcat,
    BvNAnd,
    BvNOr,
    BvXor,
    BvXNor,
    BvComp,
    BvSub,
    BvSDiv,
    BvSRem,
    BvSMod,
    BvAShr,

    BvULe,
    BvUGt,
    BvUGe,
    BvSLt,
    BvSLe,
    BvSGt,
    BvSGe,
    BvBbTerm,

    // Misc.
    /// The `rare-list` operator, used to represent RARE lists.
    RareList,

    Cl,
    Delete
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ParamOperator {
    // Indexed operators
    BvExtract,
    BvBitOf,
    ZeroExtend,
    SignExtend,
    BvConst,

    RePower,
    ReLoop,

    // Qualified operators
    ArrayConst,
}

impl_str_conversion_traits!(Operator {
    True: "true",
    False: "false",

    Not: "not",
    Implies: "=>",
    And: "and",
    Or: "or",
    Xor: "xor",
    Equals: "=",
    Distinct: "distinct",
    Ite: "ite",

    Add: "+",
    Sub: "-",
    Mult: "*",
    IntDiv: "div",
    RealDiv: "/",
    Mod: "mod",
    Abs: "abs",
    LessThan: "<",
    GreaterThan: ">",
    LessEq: "<=",
    GreaterEq: ">=",
    ToReal: "to_real",
    ToInt: "to_int",
    IsInt: "is_int",

    Select: "select",
    Store: "store",

    StrConcat: "str.++",
    StrLen: "str.len",
    StrLessThan: "str.<",
    StrLessEq: "str.<=",
    CharAt: "str.at",
    Substring: "str.substr",
    PrefixOf: "str.prefixof",
    SuffixOf: "str.suffixof",
    Contains: "str.contains",
    IndexOf: "str.indexof",
    Replace: "str.replace",
    ReplaceAll: "str.replace_all",
    ReplaceRe: "str.replace_re",
    ReplaceReAll: "str.replace_re_all",
    StrIsDigit: "str.is_digit",
    StrToCode: "str.to_code",
    StrFromCode: "str.from_code",
    StrToInt: "str.to_int",
    StrFromInt: "str.from_int",

    StrToRe: "str.to_re",
    StrInRe: "str.in_re",
    ReNone: "re.none",
    ReAll: "re.all",
    ReAllChar: "re.allchar",
    ReConcat: "re.++",
    ReUnion: "re.union",
    ReIntersection: "re.inter",
    ReKleeneClosure: "re.*",
    ReComplement: "re.comp",
    ReDiff: "re.diff",
    ReKleeneCross: "re.+",
    ReOption: "re.opt",
    ReRange: "re.range",
    BvNot: "bvnot",
    BvNeg: "bvneg",
    BvAnd: "bvand",
    BvOr: "bvor",
    BvAdd: "bvadd",
    BvMul: "bvmul",
    BvUDiv: "bvudiv",
    BvURem: "bvurem",
    BvShl: "bvshl",
    BvLShr: "bvlshr",
    BvULt: "bvult",

    BvConcat: "concat",
    BvNAnd: "bvnand",
    BvNOr: "bvnor",
    BvXor: "bvxor",
    BvXNor: "bvxnor",
    BvComp: "bvcomp",
    BvSub: "bvsub",
    BvSDiv: "bvsdiv",
    BvSRem: "bvsrem",
    BvSMod: "bvsmod",
    BvAShr: "bvashr",

    BvULe: "bvule",
    BvUGt: "bvugt",
    BvUGe: "bvuge",
    BvSLt: "bvslt",
    BvSLe: "bvsle",
    BvSGt: "bvsgt",
    BvSGe: "bvsge",
    BvBbTerm: "bbterm",

    RareList: "rare-list",

    Cl: "cl",
    Delete: "@d"
});

impl_str_conversion_traits!(ParamOperator {
    BvExtract: "extract",
    BvBitOf: "bit_of",
    ZeroExtend: "zero_extend",
    SignExtend: "sign_extend",
    BvConst: "bv",

    RePower: "re.^",
    ReLoop: "re.loop",

    ArrayConst: "const",
});

impl std::ops::Not for Binder {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Binder::Forall => Binder::Exists,
            Binder::Exists => Binder::Forall,
            _ => panic!("logical negation is only defined for quantifier binders"),
        }
    }
}

impl AsRef<[SortedVar]> for BindingList {
    fn as_ref(&self) -> &[SortedVar] {
        &self.0
    }
}

impl Deref for BindingList {
    type Target = Vec<SortedVar>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> IntoIterator for &'a BindingList {
    type Item = &'a SortedVar;

    type IntoIter = std::slice::Iter<'a, SortedVar>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl BindingList {
    pub const EMPTY: &'static Self = &BindingList(Vec::new());
}

impl From<SortedVar> for Term {
    fn from(var: SortedVar) -> Self {
        Term::Var(var.0, var.1)
    }
}

impl Term {
    pub fn new_bool(value: impl Into<bool>) -> Self {
        let op = match value.into() {
            true => Operator::True,
            false => Operator::False,
        };
        Term::Op(op, Vec::new())
    }

    /// Constructs a new integer term.
    pub fn new_int(value: impl Into<Integer>) -> Self {
        Term::Const(Constant::Integer(value.into()))
    }

    /// Constructs a new real term.
    pub fn new_real(value: impl Into<Rational>) -> Self {
        Term::Const(Constant::Real(value.into()))
    }

    /// Constructs a new string term.
    pub fn new_string(value: impl Into<String>) -> Self {
        Term::Const(Constant::String(value.into()))
    }

    /// Constructs a new bv term.
    pub fn new_bv(value: impl Into<Integer>, widht: impl Into<Integer>) -> Self {
        Term::Const(Constant::BitVec(value.into(), widht.into()))
    }

    /// Constructs a new variable term.
    pub fn new_var(name: impl Into<String>, sort: Rc<Term>) -> Self {
        Term::Var(name.into(), sort)
    }

    /// Returns the sort of this term. This does not make use of a cache --- if possible, prefer to
    /// use `TermPool::sort`.
    pub fn raw_sort(&self) -> Sort {
        let mut pool = PrimitivePool::new();
        let added = pool.add(self.clone());
        pool.sort(&added).as_sort().unwrap().clone()
    }

    /// Returns `true` if the term is the empty String.
    pub fn is_empty_string(&self) -> bool {
        match self {
            Term::Const(Constant::String(s)) => s.is_empty(),
            _ => false,
        }
    }

    /// Returns `true` if the term is an integer or real constant.
    pub fn is_number(&self) -> bool {
        matches!(self, Term::Const(Constant::Real(_) | Constant::Integer(_)))
    }

    /// Returns `true` if the term is an integer or real constant, or one such constant negated
    /// with the `-` operator.
    pub fn is_signed_number(&self) -> bool {
        match match_term!((-x) = self) {
            Some(x) => x.is_number(),
            None => self.is_number(),
        }
    }

    /// Tries to extract a `Rational` from a term. Returns `Some` if the term is an integer or real
    /// constant.
    pub fn as_number(&self) -> Option<Rational> {
        match self {
            Term::Const(Constant::Real(r)) => Some(r.clone()),
            Term::Const(Constant::Integer(i)) => Some(i.clone().into()),
            _ => None,
        }
    }

    /// Tries to extract a `bool` from a term. Returns `Some` if the term is a boolean constant.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Term::Op(Operator::True, _) => Some(true),
            Term::Op(Operator::False, _) => Some(false),
            _ => None,
        }
    }

    /// Tries to extract a `Integer` from a term. Returns `Some` if the term is an integer constant.
    pub fn as_integer(&self) -> Option<Integer> {
        match self {
            Term::Const(Constant::Integer(i)) => Some(i.clone()),
            _ => None,
        }
    }

    /// Tries to extract a `Rational` from a term, allowing negative values represented with the
    /// unary `-` operator. Returns `Some` if the term is an integer or real constant, or one such
    /// constant negated with the `-` operator.
    pub fn as_signed_number(&self) -> Option<Rational> {
        match match_term!((-x) = self) {
            Some(x) => x.as_number().map(|r| -r),
            None => self.as_number(),
        }
    }

    /// Tries to extract a `Integer` from a term, allowing negative values represented with the
    /// unary `-` operator. Returns `Some` if the term is an integer constant, or one such
    /// constant negated with the `-` operator.
    pub fn as_signed_integer(&self) -> Option<Integer> {
        match match_term!((-x) = self) {
            Some(x) => x.as_integer().map(|r| -r),
            None => self.as_integer(),
        }
    }

    /// Tries to extract a `Rational` from a term, allowing fractions. This method will return
    /// `Some` if the term is:
    ///
    /// - A real or integer constant
    /// - An application of the `/` or `div` operators on two real or integer constants
    /// - An application of the unary `-` operator on one of the two previous cases
    pub fn as_fraction(&self) -> Option<Rational> {
        fn as_unsigned_fraction(term: &Term) -> Option<Rational> {
            match term {
                Term::Op(Operator::IntDiv | Operator::RealDiv, args) if args.len() == 2 => {
                    Some(args[0].as_signed_number()? / args[1].as_signed_number()?)
                }
                _ => term.as_number(),
            }
        }

        match match_term!((-x) = self) {
            Some(x) => as_unsigned_fraction(x).map(|r| -r),
            None => as_unsigned_fraction(self),
        }
    }

    /// Returns `true` if the term is a constant.
    pub fn is_const(&self) -> bool {
        matches!(self, Term::Const(_))
    }

    /// Returns `true` if the term is a variable.
    pub fn is_var(&self) -> bool {
        matches!(self, Term::Var(_, _))
    }

    /// Tries to extract the variable name from a term. Returns `Some` if the term is a variable.
    pub fn as_var(&self) -> Option<&str> {
        match self {
            Term::Var(var, _) => Some(var.as_str()),
            _ => None,
        }
    }

    /// Returns `true` if the term is a sort.
    pub fn is_sort(&self) -> bool {
        matches!(self, Term::Sort(_))
    }

    /// Tries to extract a sort from a term. Returns `Some` if the term is a sort.
    pub fn as_sort(&self) -> Option<&Sort> {
        match self {
            Term::Sort(s) => Some(s),
            _ => None,
        }
    }

    /// Returns `true` if the term is a user defined sort with arity zero, or a sort variable.
    pub fn is_sort_var(&self) -> bool {
        matches!(self, Term::Sort(Sort::Atom(_, args)) if args.is_empty())
    }

    /// Tries to unwrap an operation term, returning the `Operator` and the arguments. Returns
    /// `None` if the term is not an operation term.
    pub fn as_op(&self) -> Option<(Operator, &[Rc<Term>])> {
        match self {
            Term::Op(op, args) => Some((*op, args.as_slice())),
            _ => None,
        }
    }

    /// Tries to unwrap a quantifier term, returning the `Binder`, the bindings and the inner term.
    /// Returns `None` if the term is not a quantifier term.
    pub fn as_quant(&self) -> Option<(Binder, &BindingList, &Rc<Term>)> {
        match self {
            Term::Binder(q @ (Binder::Forall | Binder::Exists), b, t) => Some((*q, b, t)),
            _ => None,
        }
    }

    /// Tries to unwrap a binder term, returning the `Binder`, the bindings and the inner term.
    /// Returns `None` if the term is not a binder term.
    pub fn as_binder(&self) -> Option<(Binder, &BindingList, &Rc<Term>)> {
        match self {
            Term::Binder(binder, bindings, inner) => Some((*binder, bindings, inner)),
            _ => None,
        }
    }

    /// Tries to unwrap a `let` term, returning the bindings and the inner term. Returns `None` if
    /// the term is not a `let` term.
    pub fn as_let(&self) -> Option<(&BindingList, &Rc<Term>)> {
        match self {
            Term::Let(b, t) => Some((b, t)),
            _ => None,
        }
    }

    /// Returns `true` if the term is the boolean constant `true`.
    pub fn is_bool_true(&self) -> bool {
        *self == Term::Op(Operator::True, Vec::new())
    }

    /// Returns `true` if the term is the boolean constant `false`.
    pub fn is_bool_false(&self) -> bool {
        *self == Term::Op(Operator::False, Vec::new())
    }

    /// Returns `true` if the term is the given boolean constant `b`.
    pub fn is_bool_constant(&self, b: bool) -> bool {
        match b {
            true => self.is_bool_true(),
            false => self.is_bool_false(),
        }
    }
}

impl Rc<Term> {
    /// Returns whether the term is closed, that is, whether it contains no free variables aside
    /// from global variables.
    pub fn is_closed(&self, pool: &mut PrimitivePool, global_vars: &HashSet<Rc<Term>>) -> bool {
        pool.free_vars(self).iter().all(|x| global_vars.contains(x))
    }

    /// Removes a leading negation from the term, if it exists. Same thing as `match_term!((not t)
    /// = term)`.
    pub fn remove_negation(&self) -> Option<&Self> {
        match_term!((not t) = self)
    }

    /// Removes a leading negation from the term, if it exists. If it doesn't, returns a
    /// `CheckerError::TermOfWrongForm` error. Same thing as `match_term_err!((not t) = term)`.
    pub fn remove_negation_err(&self) -> Result<&Self, CheckerError> {
        match_term_err!((not t) = self)
    }

    /// Removes all leading negations from the term, and returns how many there were.
    pub fn remove_all_negations(&self) -> (u32, &Self) {
        let mut term = self;
        let mut n = 0;
        while let Some(t) = term.remove_negation() {
            term = t;
            n += 1;
        }
        (n, term)
    }

    /// Removes all leading negations from the term, and returns a boolean representing the term
    /// polarity.
    pub fn remove_all_negations_with_polarity(&self) -> (bool, &Self) {
        let (n, term) = self.remove_all_negations();
        (n % 2 == 0, term)
    }

    /// Similar to `Term::as_number`, but returns a `CheckerError` on failure.
    pub fn as_number_err(&self) -> Result<Rational, CheckerError> {
        self.as_number()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_integer`, but returns a `CheckerError` on failure.
    pub fn as_integer_err(&self) -> Result<Integer, CheckerError> {
        self.as_integer()
            .ok_or_else(|| CheckerError::ExpectedAnyInteger(self.clone()))
    }

    /// Similar to `Term::as_integer_err`, but also checks if non-negative.
    pub fn as_usize_err(&self) -> Result<usize, CheckerError> {
        if let Some(i) = self.as_integer() {
            if i >= 0 {
                return Ok(i.to_usize().unwrap());
            }
        }
        Err(CheckerError::ExpectedNonnegInteger(self.clone()))
    }

    /// Similar to `Term::as_signed_number`, but returns a `CheckerError` on failure.
    pub fn as_signed_number_err(&self) -> Result<Rational, CheckerError> {
        self.as_signed_number()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_fraction`, but returns a `CheckerError` on failure.
    pub fn as_fraction_err(&self) -> Result<Rational, CheckerError> {
        self.as_fraction()
            .ok_or_else(|| CheckerError::ExpectedAnyNumber(self.clone()))
    }

    /// Similar to `Term::as_bool`, but returns a `CheckerError` on failure.
    pub fn as_bool_err(&self) -> Result<bool, CheckerError> {
        self.as_bool()
            .ok_or_else(|| CheckerError::ExpectedAnyBoolConstant(self.clone()))
    }

    /// Tries to unwrap an operation term, returning the `Operator` and the arguments. Returns a
    /// `CheckerError` if the term is not an operation term.
    pub fn as_op_err(&self) -> Result<(Operator, &[Rc<Term>]), CheckerError> {
        self.as_op()
            .ok_or_else(|| CheckerError::ExpectedOperationTerm(self.clone()))
    }

    /// Tries to unwrap a quantifier term, returning the `Binder`, the bindings and the inner term.
    /// Returns a `CheckerError` if the term is not a quantifier term.
    pub fn as_quant_err(&self) -> Result<(Binder, &BindingList, &Rc<Term>), CheckerError> {
        self.as_quant()
            .ok_or_else(|| CheckerError::ExpectedQuantifierTerm(self.clone()))
    }

    /// Tries to unwrap a binder term, returning the `Binder`, the bindings and the inner term.
    /// Returns a `CheckerError` if the term is not a binder term.
    pub fn as_binder_err(&self) -> Result<(Binder, &BindingList, &Rc<Term>), CheckerError> {
        self.as_binder()
            .ok_or_else(|| CheckerError::ExpectedBinderTerm(self.clone()))
    }

    /// Tries to unwrap a `let` term, returning the bindings and the inner
    /// term. Returns a `CheckerError` if the term is not a `let` term.
    pub fn as_let_err(&self) -> Result<(&BindingList, &Rc<Term>), CheckerError> {
        self.as_let()
            .ok_or_else(|| CheckerError::ExpectedLetTerm(self.clone()))
    }
}

impl Constant {
    /// Returns the sort of a constant. In case it's a `BitVec`, we only return the width.
    pub fn sort(&self) -> Sort {
        match self {
            Constant::Integer(_) => Sort::Int,
            Constant::Real(_) => Sort::Real,
            Constant::String(_) => Sort::String,
            Constant::BitVec(_, width) => Sort::BitVec(width.clone()),
        }
    }

    pub fn as_integer(&self) -> Option<Integer> {
        match self {
            Constant::Integer(i) => Some(i.clone()),
            _ => None,
        }
    }
}
