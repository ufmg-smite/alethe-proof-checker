//! A pretty printer for Alethe proofs.

use crate::{
    ast::*,
    parser::Token,
    utils::{is_symbol_character, DedupIterator},
};
use indexmap::IndexMap;
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fmt, io,
    sync::atomic::{AtomicBool, Ordering},
};

pub static USE_SHARING_IN_TERM_DISPLAY: AtomicBool = AtomicBool::new(false);

/// Prints a proof to the standard output.
///
/// If `use_sharing` is `true`, terms that are used multiple times will make use of sharing. The
/// first time a novel term appears, it receives a unique name using the `:named` attribute. After
/// that, any occurrence of that term will simply use this name, instead of printing the whole term.
pub fn print_proof(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    proof: &Proof,
    use_sharing: bool,
) -> io::Result<()> {
    let mut stdout = io::stdout();
    AlethePrinter::new(pool, prelude, use_sharing, &mut stdout).write_proof(proof)
}

/// Given the conclusion clause of a `lia_generic` step, this method will write to `dest` the
/// corresponding SMT problem instance.
pub fn write_lia_smt_instance(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    dest: &mut dyn io::Write,
    clause: &[Rc<Term>],
    use_sharing: bool,
) -> io::Result<()> {
    let mut printer = AlethePrinter::new(pool, prelude, use_sharing, dest);
    // We have to override the default prefix "@p_" because symbols starting with "@" are reserved
    // in SMT-LIB.
    printer.term_sharing_variable_prefix = "p_";
    // Since we are printing an SMT-LIB problem, we have to be
    // compliant. For Carcara, this means that arithmetic constants
    // cannot use the GMP notation
    printer.smt_lib_strict = true;
    printer.write_lia_smt_instance(clause)
}

pub trait PrintProof {
    fn write_proof(&mut self, proof: &Proof) -> io::Result<()>;
}

trait PrintWithSharing {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()>;
}

impl<T: PrintWithSharing> PrintWithSharing for &T {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        PrintWithSharing::print_with_sharing(*self, p)
    }
}

impl PrintWithSharing for Rc<Term> {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        if let Some(name) = p.defined_constants.get(self) {
            return write!(p.inner, "{}", quote_symbol(name));
        }
        if let Some(indices) = &mut p.term_indices {
            // There are a few cases where we don't use sharing when printing a term:
            let cannot_use_sharing =
                // - Terminal terms (i.e., constants or variables) could in theory be shared,
                // but, since they are very small, it's not worth it to give them a name.
                self.is_const() || self.is_var()
                // - Sorts are represented as terms, but they are not actually terms in the grammar,
                // so we can't use the `(! ... :named ...)` syntax to give them a name.
                || self.is_sort()
                // - If a term is only used once in the proof, there is no reason to give it a
                // name. We detect this case by checking if the number of references to it's `Rc` is
                // no more than 3: one in the pool storage, one in the pool sorts cache, and one in
                // the proof itself.
                // TODO: this is a terrible way of checking if it is only used once in the proof,
                // as it depends on internal implementation details of the term pool.
                || Rc::strong_count(self) <= 3
                // - Terms which are not closed, that is, terms which have free variables besides
                // the global variables, cannot be shared
                || !self.is_closed(p.pool, &p.global_vars);

            if !cannot_use_sharing {
                return if let Some(i) = indices.get(self) {
                    write!(p.inner, "{}{}", p.term_sharing_variable_prefix, i)
                } else {
                    let i = indices.len();
                    indices.insert(self.clone(), i);
                    write!(p.inner, "(! ")?;
                    p.write_raw_term(self)?;
                    write!(p.inner, " :named {}{})", p.term_sharing_variable_prefix, i)
                };
            }
        }
        p.write_raw_term(self)
    }
}

impl PrintWithSharing for SortedVar {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        let (name, value) = self;
        write!(p.inner, "({} ", quote_symbol(name))?;
        value.print_with_sharing(p)?;
        write!(p.inner, ")")
    }
}

impl PrintWithSharing for BindingList {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        match self.as_slice() {
            [] => write!(p.inner, "()"),
            [head, tail @ ..] => p.write_s_expr(head, tail),
        }
    }
}

impl PrintWithSharing for Constant {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        write!(p.inner, "{}", self)
    }
}

impl PrintWithSharing for Operator {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        write!(p.inner, "{}", self)
    }
}

impl PrintWithSharing for ParamOperator {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        write!(p.inner, "{}", self)
    }
}

struct AlethePrinter<'a> {
    pool: &'a mut PrimitivePool,
    inner: &'a mut dyn io::Write,
    term_indices: Option<IndexMap<Rc<Term>, usize>>,
    term_sharing_variable_prefix: &'static str,
    global_vars: HashSet<Rc<Term>>,
    defined_constants: HashMap<Rc<Term>, String>,
    smt_lib_strict: bool,
}

impl<'a> PrintProof for AlethePrinter<'a> {
    fn write_proof(&mut self, proof: &Proof) -> io::Result<()> {
        for (name, value) in &proof.constant_definitions {
            write!(self.inner, "(define-fun {} () ", quote_symbol(name))?;
            self.pool.sort(value).print_with_sharing(self)?;
            write!(self.inner, " ")?;
            value.print_with_sharing(self)?;
            writeln!(self.inner, ")")?;
        }
        self.defined_constants = proof
            .constant_definitions
            .iter()
            .cloned()
            .map(|(name, term)| (term, name))
            .collect();
        let mut iter = proof.iter();
        while let Some(command) = iter.next() {
            match command {
                ProofCommand::Assume { id, term } => {
                    write!(self.inner, "(assume {} ", quote_symbol(id))?;
                    term.print_with_sharing(self)?;
                    write!(self.inner, ")")?;
                }
                ProofCommand::Step(s) => self.write_step(&mut iter, s)?,
                ProofCommand::Subproof(s) => {
                    write!(self.inner, "(anchor :step {}", quote_symbol(command.id()))?;

                    if !s.args.is_empty() {
                        write!(self.inner, " :args (")?;
                        let mut is_first = true;
                        for arg in &s.args {
                            if !is_first {
                                write!(self.inner, " ")?;
                            }
                            is_first = false;

                            match arg {
                                AnchorArg::Variable((name, sort)) => {
                                    write!(self.inner, "({} ", quote_symbol(name))?;
                                    sort.print_with_sharing(self)?;
                                    write!(self.inner, ")")?;
                                }
                                AnchorArg::Assign(var, value) => {
                                    write!(self.inner, "(:= ")?;
                                    var.print_with_sharing(self)?;
                                    write!(self.inner, " ")?;
                                    value.print_with_sharing(self)?;
                                    write!(self.inner, ")")?;
                                }
                            }
                        }
                        write!(self.inner, ")")?;
                    }

                    write!(self.inner, ")")?;
                }
            }
            writeln!(self.inner)?;
        }
        self.defined_constants.clear();
        Ok(())
    }
}

impl<'a> AlethePrinter<'a> {
    pub fn new(
        pool: &'a mut PrimitivePool,
        prelude: &ProblemPrelude,
        use_sharing: bool,
        dest: &'a mut dyn io::Write,
    ) -> Self {
        let global_variables = if use_sharing {
            prelude
                .function_declarations
                .iter()
                .map(|var| pool.add(var.clone().into()))
                .collect()
        } else {
            HashSet::new()
        };
        Self {
            pool,
            inner: dest,
            term_indices: use_sharing.then(IndexMap::new),
            term_sharing_variable_prefix: "@p_",
            global_vars: global_variables,
            defined_constants: HashMap::new(),
            smt_lib_strict: false,
        }
    }

    fn write_s_expr<H, T>(&mut self, head: &H, tail: &[T]) -> io::Result<()>
    where
        H: PrintWithSharing + ?Sized,
        T: PrintWithSharing,
    {
        write!(self.inner, "(")?;
        head.print_with_sharing(self)?;
        self.write_s_expr_tail(tail)
    }

    fn write_s_expr_tail<T: PrintWithSharing>(&mut self, tail: &[T]) -> io::Result<()> {
        for t in tail {
            write!(self.inner, " ")?;
            t.print_with_sharing(self)?;
        }
        write!(self.inner, ")")
    }

    fn write_raw_term(&mut self, term: &Term) -> io::Result<()> {
        match term {
            Term::Const(c) => {
                if self.smt_lib_strict {
                    if let Constant::Integer(i) = c {
                        if i.is_negative() {
                            write!(self.inner, "(- {})", i.clone().abs())
                        } else {
                            write!(self.inner, "{}", i)
                        }
                    } else if let Constant::Real(r) = c {
                        if r.is_negative() {
                            write!(self.inner, "(- ")?;
                        }
                        if r.is_integer() {
                            write!(self.inner, "{}.0", r.clone().abs())?;
                        } else {
                            write!(
                                self.inner,
                                "(/ {}.0 {}.0)",
                                r.numer().clone().abs(),
                                r.denom()
                            )?;
                        }
                        if r.is_negative() {
                            write!(self.inner, ")")?;
                        }
                        Ok(())
                    } else {
                        write!(self.inner, "{}", c)
                    }
                } else {
                    write!(self.inner, "{}", c)
                }
            }
            Term::Var(name, _) => write!(self.inner, "{}", quote_symbol(name)),
            Term::App(func, args) => self.write_s_expr(func, args),
            Term::Op(op, args) => {
                if args.is_empty() {
                    write!(self.inner, "{}", op)
                } else {
                    self.write_s_expr(op, args)
                }
            }
            Term::Sort(sort) => write!(self.inner, "{}", sort),
            Term::Binder(binder, bindings, term) => {
                write!(self.inner, "({} ", binder)?;
                bindings.print_with_sharing(self)?;
                write!(self.inner, " ")?;
                term.print_with_sharing(self)?;
                write!(self.inner, ")")
            }
            Term::Let(bindings, term) => {
                write!(self.inner, "(let ")?;
                bindings.print_with_sharing(self)?;
                write!(self.inner, " ")?;
                term.print_with_sharing(self)?;
                write!(self.inner, ")")
            }
            Term::ParamOp { op, op_args, args } => {
                if !args.is_empty() {
                    write!(self.inner, "(")?;
                }
                write!(self.inner, "(_ {}", op)?;
                self.write_s_expr_tail(op_args)?;
                if !args.is_empty() {
                    self.write_s_expr_tail(args)?;
                }
                Ok(())
            }
        }
    }

    fn write_step(&mut self, iter: &mut ProofIter, step: &ProofStep) -> io::Result<()> {
        write!(self.inner, "(step {} (cl", quote_symbol(&step.id))?;

        for t in &step.clause {
            write!(self.inner, " ")?;
            t.print_with_sharing(self)?;
        }
        write!(self.inner, ")")?;

        write!(self.inner, " :rule {}", step.rule)?;

        if let [head, tail @ ..] = step.premises.as_slice() {
            let id = iter.get_premise(*head).id();
            write!(self.inner, " :premises ({}", quote_symbol(id))?;
            for premise in tail {
                let id = iter.get_premise(*premise).id();
                write!(self.inner, " {}", quote_symbol(id))?;
            }
            write!(self.inner, ")")?;
        }

        if let [head, tail @ ..] = step.args.as_slice() {
            write!(self.inner, " :args (")?;
            self.write_proof_arg(head)?;
            for arg in tail {
                write!(self.inner, " ")?;
                self.write_proof_arg(arg)?;
            }
            write!(self.inner, ")")?;
        }

        if let [head, tail @ ..] = step.discharge.as_slice() {
            let id = iter.get_premise(*head).id();
            write!(self.inner, " :discharge ({}", id)?;
            for discharge in tail {
                let id = iter.get_premise(*discharge).id();
                write!(self.inner, " {}", quote_symbol(id))?;
            }
            write!(self.inner, ")")?;
        }

        write!(self.inner, ")")?;
        Ok(())
    }

    fn write_proof_arg(&mut self, arg: &ProofArg) -> io::Result<()> {
        match arg {
            ProofArg::Term(t) => t.print_with_sharing(self),
            ProofArg::Assign(name, value) => {
                write!(self.inner, "(:= {} ", name)?;
                value.print_with_sharing(self)?;
                write!(self.inner, ")")
            }
        }
    }

    fn write_lia_smt_instance(&mut self, clause: &[Rc<Term>]) -> io::Result<()> {
        for term in clause.iter().dedup() {
            write!(self.inner, "(assert (not ")?;
            term.print_with_sharing(self)?;
            writeln!(self.inner, "))")?;
        }
        Ok(())
    }
}

fn write_s_expr<H, T>(f: &mut fmt::Formatter, head: H, tail: &[T]) -> fmt::Result
where
    H: fmt::Display,
    T: fmt::Display,
{
    write!(f, "({}", head)?;
    for e in tail {
        write!(f, " {}", e)?;
    }
    write!(f, ")")
}

fn quote_symbol(symbol: &str) -> Cow<str> {
    use crate::parser::Reserved;
    use std::str::FromStr;

    assert!(symbol.chars().all(|c| c != '|'));

    // Any symbol that:
    // - is an empty string,
    // - starts with a digit,
    // - is a reserved word, or
    // - contains non-symbol characters
    // must be quoted
    if symbol.is_empty()
        || symbol.chars().next().unwrap().is_ascii_digit()
        || Reserved::from_str(symbol).is_ok()
        || symbol.chars().any(|c| !is_symbol_character(c))
    {
        Cow::Owned(format!("|{}|", symbol))
    } else {
        Cow::Borrowed(symbol)
    }
}

fn escape_string(string: &str) -> Cow<str> {
    if string.contains('"') {
        Cow::Owned(string.replace('"', "\"\""))
    } else {
        Cow::Borrowed(string)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // If the alternate flag (`#`) is passed, or the global `USE_SHARING_IN_TERM_DISPLAY` is
        // false, we disable printing with sharing
        let use_sharing = USE_SHARING_IN_TERM_DISPLAY.load(Ordering::Relaxed) && !f.alternate();
        let mut buf = Vec::new();
        // This pool is only used for the free variables cache, so it's fine to use a fresh pool
        let mut pool = PrimitivePool::new();
        let mut printer = AlethePrinter {
            pool: &mut pool,
            inner: &mut buf,
            term_indices: use_sharing.then(IndexMap::new),
            term_sharing_variable_prefix: "@p_",
            global_vars: HashSet::new(),
            defined_constants: HashMap::new(),
            smt_lib_strict: false,
        };
        printer.write_raw_term(self).unwrap();
        let result = std::str::from_utf8(&buf).unwrap();
        write!(f, "{}", result)
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Constant::Integer(i) => write!(f, "{}", i),
            Constant::Real(r) => {
                // TODO: add option to control whether we use GMP notation
                if r.is_integer() && !r.is_negative() {
                    write!(f, "{}.0", r.numer())
                } else {
                    write!(f, "{}/{}", r.numer(), r.denom())
                }
            }
            Constant::String(s) => write!(f, "\"{}\"", escape_string(s)),
            Constant::BitVec(val, width) => write!(f, "(_ bv{} {})", val, width), // TODO: comeback to this
        }
    }
}

impl fmt::Display for Binder {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Binder::Forall => "forall",
            Binder::Exists => "exists",
            Binder::Choice => "choice",
            Binder::Lambda => "lambda",
        };
        write!(f, "{}", s)
    }
}

impl fmt::Display for BindingList {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.as_slice() {
            [] => write!(f, "()"),
            [head, tail @ ..] => {
                write!(f, "(({} {})", quote_symbol(&head.0), head.1)?;
                for (var, term) in tail {
                    write!(f, " ({} {})", quote_symbol(var), term)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // Function sorts should never be displayed, so the exact format we use is of little
            // importance
            Sort::Function(args) => write_s_expr(f, "Func", args),
            Sort::Atom(name, args) => match args.len() {
                0 => write!(f, "{}", quote_symbol(name)),
                _ => write_s_expr(f, quote_symbol(name), args),
            },
            Sort::Bool => write!(f, "Bool"),
            Sort::Int => write!(f, "Int"),
            Sort::Real => write!(f, "Real"),
            Sort::String => write!(f, "String"),
            Sort::RegLan => write!(f, "RegLan"),
            Sort::Array(x, y) => write_s_expr(f, "Array", &[x, y]),
            Sort::BitVec(w) => write!(f, "(_ BitVec {})", w),
            Sort::RareList => unreachable!("RARE list sort should never be displayed"),
            Sort::Type => write!(f, "Type"),
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::OpenParen => write!(f, "("),
            Token::CloseParen => write!(f, ")"),
            Token::Symbol(s) => write!(f, "{}", quote_symbol(s)),
            Token::Keyword(k) => write!(f, ":{}", k),
            Token::Numeral(n) => write!(f, "{}", n),
            Token::Decimal(r) => write!(f, "{}", r),
            Token::Bitvector { value, width } => {
                write!(f, "#b{v:0>w$b}", v = value, w = *width as usize)
            }
            Token::String(s) => write!(f, "\"{}\"", escape_string(s)),
            Token::ReservedWord(r) => write!(f, "{}", r),
            Token::Eof => write!(f, "EOF"),
        }
    }
}

impl fmt::Display for ProblemPrelude {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "(set-logic {})", self.logic.as_deref().unwrap_or("ALL"))?;

        for (name, arity) in &self.sort_declarations {
            writeln!(f, "(declare-sort {} {})", quote_symbol(name), arity)?;
        }

        for (name, sort) in &self.function_declarations {
            write!(f, "(declare-fun {} ", quote_symbol(name))?;
            if let Sort::Function(sorts) = sort.as_sort().unwrap() {
                write_s_expr(f, &sorts[0], &sorts[1..sorts.len() - 1])?;
                writeln!(f, " {})", sorts.last().unwrap())?;
            } else {
                writeln!(f, "() {})", sort)?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sharing() {
        use crate::parser;

        let definitions: &[u8] = b"
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const y Bool)
            (declare-const z Bool)
        ";
        let proof: &[u8] = b"
            (step t1 (cl (and (= 1 2) (= 1 2))) :rule hole)
            (step t2 (cl (and (or a b) (not (or a b)))) :rule hole)
            (step t3 (cl (and (forall ((x Int)) (or (= x 2) (= 2 3))) (= 2 3))) :rule hole)
            (step t4 (cl (forall ((x Int)) (= (+ x 2) (+ x 2)))) :rule hole)
            (step t5 (cl (and (forall ((p Bool)) p) (forall ((p Bool)) p))) :rule hole)
            (anchor :step t6 :args ((x Int)))
            (step t6.t1 (cl (= (+ x 2) (+ x 2))) :rule hole)
            (step t6 (cl) :rule hole)
        ";
        let expected = "\
            (step t1 (cl (and (! (= 1 2) :named @p_0) @p_0)) :rule hole)\n\
            (step t2 (cl (and (! (or a b) :named @p_1) (not @p_1))) :rule hole)\n\
            (step t3 (cl (and (forall ((x Int)) (or (= x 2) (! (= 2 3) :named @p_2))) @p_2)) :rule hole)\n\
            (step t4 (cl (forall ((x Int)) (= (+ x 2) (+ x 2)))) :rule hole)\n\
            (step t5 (cl (and (! (forall ((p Bool)) p) :named @p_3) @p_3)) :rule hole)\n\
            (anchor :step t6 :args ((x Int)))\n\
            (step t6.t1 (cl (= (+ x 2) (+ x 2))) :rule hole)\n\
            (step t6 (cl) :rule hole)\n\
        ";
        let (problem, proof, mut pool) =
            parser::parse_instance(definitions, proof, parser::Config::new()).unwrap();

        let mut buf = Vec::new();
        AlethePrinter::new(&mut pool, &problem.prelude, true, &mut buf)
            .write_proof(&proof)
            .unwrap();

        println!("{}", std::str::from_utf8(&buf).unwrap());
        println!("{}", expected);

        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }
}
