/// AST's of a fragment of Eunoia required to mechanize Alethe proofs.

// TODO:
pub struct EunoiaTheorySignature;

// TODO: is this correct? also: pub type alias?
/// SMT-LIB version 3.0 symbol.
pub type Symbol = String;

/// Attributes of annotated type variables.
#[derive(Debug, PartialEq, Clone)]
pub enum EunoiaTypeAttr {
    // :var symbol
    Var(Symbol),

    // :implicit
    Implicit,

    // :requires (<term> <term>)
    // TODO: Internally, (! T :requires (t s)) is syntax sugar for
    // (eo::requires t s T) where eo::requires is an operator that evalutes to
    // its third argument if and only if its first two arguments are equivalent
    // (details on this operator are given in computation). Furthermore, the
    // function type (-> (eo::requires t s T) S) is treated as
    // (-> T (eo::requires t s S)). The Ethos rewrites all types of the former to
    // the latter.
    Requires(EunoiaTerm, EunoiaTerm),
}

// TODO: check if this name is adequate
/// Kind parameters: (! T :var A ...)
#[derive(Debug, PartialEq, Clone)]
pub enum EunoiaKindParam {
    // Annotated kind variable, like: (! Type :var A :implicit)

    // TODO: note that this declaration is a binder whose scope is the rest of the whole
    // term where it occurs. For example, in:
    // (declare-const ite (-> (! Type :var A :implicit) Bool A A A))
    // A is a variable introduced in (! Type :var A :implicit), whose scope
    // reaches to the end of the outer construction.

    // TODO: cannot understand the following (from Ethos' user manual):
    // Internally, (! T :var t) is syntax sugar for the type (Quote t) where t
    // is a parameter of type T and Quote is a distinguished type of kind
    // (-> (! Type :var U) U Type). When type checking applications of functions of
    // type (-> (Quote t) S), the parameter t is bound to the argument the function
    // is applied to.
    // Internally, (! T :implicit) drops T from the list of arguments of the function
    // type we are defining.

    // TODO: it looks that there are these KindParam, used to define variables that
    // refer to types that inhabit Type (or "kinds"?); while there is also a
    // "typed-param" syntactic category that refers to the parameters of a function:
    // values inhabiting some given type
    KindParam(EunoiaType, Vec<EunoiaTypeAttr>),
}

// TODO: not everything about Eunoia's type terms and kinds
// TODO: types (expressions denoting sets of values) and kinds (expressions denoting sets of types)
// types as sets? should we change that in the manual?
/// Type terms.
#[derive(Debug, PartialEq, Clone)]
pub enum EunoiaType {
    // Built-in primitive types.
    // Eunoia has 'Bool' as a built-in type
    Bool,

    // TODO: not distinguishing "types" from "kinds", for the moment
    Type,

    Real,

    // An already declared Sort.
    // TODO: what about args?
    Name(Symbol),

    // A (possible polymorphic) function type
    Fun(Vec<EunoiaKindParam>, Vec<EunoiaType>, Box<EunoiaType>),
}

// TODO: using it also for EunoiaTypedParam
/// Annotated attributes in declarations of constants.
#[derive(Debug, PartialEq)]
pub enum EunoiaConsAttr {
    // :right-assoc
    RightAssoc,
    // :left-assoc
    LeftAssoc,
    // :right-assoc-nil
    RightAssocNil(EunoiaTerm),

    // :chainable
    Chainable,

    // :pairwise
    Pairwise,

    // :binder symbol
    Binder(Symbol),
}

/// A parameter name and type.
#[derive(Debug, PartialEq)]
pub struct EunoiaTypedParam {
    pub name: Symbol,
    pub eunoia_type: EunoiaTerm,
    pub attrs: Vec<EunoiaConsAttr>,
}

/// Attributes allowed within a 'define' statement.
#[derive(Debug, PartialEq)]
pub enum EunoiaDefineAttr {
    // :type
    Type,
}

// /// Eunoia declare-consts
// pub struct EunoiaDeclareConsts {
//     pub lit_cat,
//     pub type,
// }

// // TODO: "Alethe in Eunoia" does not use 'declare-type', only 'declare-sort'.
// pub struct EunoiaDeclareSort {

// }

// TODO: see if we actually have this, rather than only "declare-const" and the
// likes

// TODO: using rug crate, as in Alethe ASTs
#[derive(Debug, PartialEq)]
pub enum EunoiaLitCategory {
    // TODO: include the following:
    // <binary> denoting the category of binary constants #b<0|1>+,
    // <hexadecimal> denoting the category of hexadecimal constants #x<hex-digit>+ where hexdigit is [0-9] | [a-f] | [A-F],
}

// NOTE: a more expressive grammar, to enforce compositional semantics
#[derive(Debug, PartialEq, Clone)]
pub enum EunoiaTerm {
    // TODO: it is not clear how to includes Types and Kinds
    Type(EunoiaType),

    // Constant terms.

    // Note: Numeral, rational and decimal values are implemented by the
    // arbitrary precision arithmetic library GMP. Binary and hexadecimal
    // values are implemented as layer on top of numeral values that
    // tracks a bit width. String values are implemented as a vector of
    // unsigned integers whose maximum value is specified by SMT-LIB
    // version 2.6, namely the character set corresponds to Unicode
    // values 0 to 196607.
    // lit-category
    // TODO: should we define this concept as a separate notion from
    // EunoiaTerm?
    // <numeral> denoting the category of numerals -?<digit>+
    Numeral(rug::Integer),

    // <decimal> denoting the category of decimals -?<digit>+.<digit>+,
    Decimal(rug::Rational),

    // <rational> denoting the category of rationals -?<digit>+/<digit>+,
    Rational(rug::Integer, rug::Integer),

    // <string> denoting the category of string literals "<char>*"
    String(String),
    // TODO: is it reasonable/required a specific syntactic category "constant"?
    // Like Const(Constant) and then define enum Constant?
    True,

    False,

    // An arbitrary identifier.
    Id(Symbol),

    // TODO: different with Id(Symbol)?
    // TODO: not using ID tag for Symbol...
    // A variable, consisting of an identifier and a sort.
    Var(Symbol, Box<EunoiaTerm>),

    // TODO: not using ID tag for Symbol...
    // TODO: actually, Eunoia's grammar does not consider
    // (<symbol> <term>+) to be an application, but rather
    // an arbitrary list of terms, beginning with a symbol.
    // This gives a context-dependent semantics for such phrases,
    // maybe going against the idea of a "compositional semantics".
    // NOTE: Eunoia's grammar is, actually, (<symbol> <term>+) (note the '+')
    List(Symbol, Vec<EunoiaTerm>),

    // Application of a built-in operator
    Op(EunoiaOperator, Vec<EunoiaTerm>),
}

/// Eunoia's built-in computational operators.
#[derive(Debug, PartialEq, Clone)]
pub enum EunoiaOperator {
    // eo::xor
    Xor,

    // eo::not
    Not,

    // eo::is_eq TODO: ?
    Eq,

    // eo::gt TODO: non-core (still used in small.eo)?
    GreaterThan,

    // eo::ge TODO: non-core (still used in small.eo)?
    GreaterEq,

    // eo::lt TODO: non-core?
    LessThan,

    // eo::le TODO: non-core?
    LessEq,
}

// /// A single 'declare-rule', with ':ethos' as its keyword.
// pub struct EunoiaDeclareRuleEthos{
//     pub symbol,
//     pub typed_params,
//     pub assumptions: Vec<Rc<EunoiaTerm>>,
//     pub premises,
//     pub arguments,
//     pub reqs,
//     pub conclusion_term,
//     pub conclusion_attrs,
// }
#[derive(Debug, PartialEq)]
pub enum EunoiaCommand {
    // Eunoia commands

    // TODO:
    // The command:
    // (assume s f)
    // can be seen as syntax sugar for:
    // (declare-const s (Proof f))
    // how to deal with these syntax sugars?
    Assume {
        name: Symbol,
        term: EunoiaTerm,
    },

    // To introduce assumptions in local context, that will be consumed by
    // step-pop.
    AssumePush {
        name: Symbol,
        term: EunoiaTerm,
    },

    // Eunoia definitions.
    Define {
        name: Symbol,
        typed_params: Vec<EunoiaTypedParam>,
        term: EunoiaTerm,
        attrs: Vec<EunoiaDefineAttr>,
    },

    // (program <symbol> <keyword> <sexpr>*) |
    // (program <symbol> (<typed-param>*) (<type>*) <type> ((<term> <term>)+)) |
    Program {
        name: Symbol,
        typed_params: Vec<EunoiaTypedParam>,
        params: Vec<EunoiaType>,
        ret: Vec<EunoiaType>,
        body: Vec<(EunoiaTerm, EunoiaTerm)>,
    },

    // TODO: why does Alethes AST for premises
    // TODO:
    // The command:
    // (step s f :rule r :premises (p1 ... pn) :args (t1 ... tm))
    // can be seen as syntax sugar for:
    // (define s () (r p1 ... pn t1 ... tm) :type (Proof f))
    /// Proof step:
    /// (step <symbol> <term>? :rule <symbol> <premises>? <arguments>?)
    Step {
        name: Symbol,
        // NOTE: this must be an application of Alethe's cl operator over
        // a possible empty list of terms
        conclusion_clause: EunoiaTerm,
        rule: Symbol,
        premises: Vec<Symbol>,
        arguments: Vec<EunoiaTerm>,
    },

    /// Step that might consume a local assumption, previously introduced by
    /// 'assume-push'.
    StepPop {
        name: Symbol,
        term: EunoiaTerm,
        rule: Symbol,
        premises: Vec<EunoiaTerm>,
        arguments: Vec<EunoiaTerm>,
    },

    // Common commands

    // TODO: for the moment, allowing an arbitrary EunoiaTerm as a type
    // TODO: how to handle declare-type:n
    // (declare-type <symbol> (<type>*)) declares a new type constructor named
    // <symbol> whose kind is Type if <type>* is empty. If <type>* is
    // <type_1> ... <type_n>, then kind of <symbol> is
    // (-> <type_1> ... <type_n> Type). This is a derived command as it is a
    // shorthand for (declare-const <symbol> Type) if <type>* is empty, and for
    // (declare-const <symbol> (-> <type>* Type)) otherwise.
    // SMT-LIB declare-const.
    DeclareConst {
        name: Symbol,
        eunoia_type: EunoiaTerm,
        attrs: Vec<EunoiaConsAttr>,
    },

    // SMT-lib 2 commands
    // (declare-sort name arity)
    DeclareSort {
        name: Symbol,
        // TODO: only a numeral
        arity: EunoiaTerm,
    },

    // (set-logic symbol)
    SetLogic {
        name: Symbol,
    },
}

/// A collection of proof rules.
pub struct EunoiaProofRules {}

pub struct EunoiaProgram;

// TODO: note that we are allowing here other concepts beyond
// proof-centric ones
pub type EunoiaProof = Vec<EunoiaCommand>;
