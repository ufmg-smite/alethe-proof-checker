use super::{
    assert_clause_len, assert_eq, assert_num_args, assert_num_premises, assert_polyeq_expected,
    get_premise_term, RuleArgs, RuleResult,
};
use crate::{
    ast::*,
    checker::{error::CheckerError, rules::assert_polyeq},
};
use std::{cmp, time::Duration};

/// A function that takes an `Rc<Term>` and returns a vector corresponding to
/// the flat form of that term.
///
/// In this flat form, all `str.++` applications are dissolved and every
/// argument of those applications is inserted into the vector (e.g., `(str.++
/// a (str.++ b c))` would lead to `[a, b, c]`, where `a`, `b` and `c` are
/// arbitrary String terms). Furthermore, all String constants are broken
/// into constants of size one and are inserted into the vector too.
///
/// All String terms that aren't `str.++` applications can be seen as `(str.++ term "")`.
/// So, applying `flatten` to them would lead to `[term]`. Furthermore,
/// the empty String isn't mapped to any entry in the vector, so `flatten`
/// applied to `""` leads to an empty vector.
fn flatten(pool: &mut dyn TermPool, term: Rc<Term>) -> Vec<Rc<Term>> {
    let mut flattened = Vec::new();
    if let Term::Const(Constant::String(s)) = term.as_ref() {
        flattened.extend(
            s.chars()
                .map(|c| pool.add(Term::Const(Constant::String(c.to_string())))),
        );
    } else if let Some(args) = match_term!((strconcat ...) = term) {
        for arg in args {
            flattened.extend(flatten(pool, arg.clone()));
        }
    } else {
        flattened.push(term.clone());
    }
    flattened
}

fn is_compatible(s: Vec<Rc<Term>>, t: Vec<Rc<Term>>) -> bool {
    match (&s[..], &t[..]) {
        (_, []) => true,
        ([], _) => true,
        ([h1, t1 @ ..], [h2, t2 @ ..]) => {
            if h1 == h2 {
                is_compatible(t1.to_vec(), t2.to_vec())
            } else {
                false
            }
        }
    }
}

fn overlap(s: Vec<Rc<Term>>, t: Vec<Rc<Term>>) -> usize {
    match &s[..] {
        [] | [_] => 0,
        [_, tail @ ..] => {
            if is_compatible(s.clone(), t.clone()) {
                0
            } else {
                1 + overlap(tail.to_vec(), t.clone())
            }
        }
    }
}

/// A function to standardize String constants and `str.++` applications
/// across a term.
///
/// It takes an `Rc<Term>` and returns an equivalent `Rc<Term>` where all String
/// constants of size greater than one are broken into `str.++` applications
/// of their characters (`"abc"` would become `(str.++ "a" "b" "c")`), and
/// nested `str.++` applications are dissolved, remaining just one application
/// with all the previous nested arguments (e.g., `(str.++ a (str.++ b (str.++ c "")))` would lead to `(str.++ a b c)`).
fn expand_string_constants(pool: &mut dyn TermPool, term: &Rc<Term>) -> Rc<Term> {
    match term.as_ref() {
        Term::Const(Constant::String(s)) => {
            let args: Vec<Rc<Term>> = s
                .chars()
                .map(|c| pool.add(Term::Const(Constant::String(c.to_string()))))
                .collect();
            match args.len() {
                0 => pool.add(Term::new_string("")),
                1 => args[0].clone(),
                _ => pool.add(Term::Op(Operator::StrConcat, args)),
            }
        }
        Term::Op(op, args) => match op {
            Operator::StrConcat => {
                let mut new_args = Vec::new();
                // (str.++ "a" (str.++ "b" "c")) => (str.++ "a" "b" "c")
                for arg in args {
                    new_args.extend(flatten(pool, arg.clone()));
                }
                pool.add(Term::Op(*op, new_args))
            }
            _ => {
                let new_args = args
                    .iter()
                    .map(|a| expand_string_constants(pool, a))
                    .collect();
                pool.add(Term::Op(*op, new_args))
            }
        },
        Term::App(func, args) => {
            let new_args = args
                .iter()
                .map(|term| expand_string_constants(pool, term))
                .collect();
            pool.add(Term::App(func.clone(), new_args))
        }
        Term::Let(binding, inner) => {
            let new_inner = expand_string_constants(pool, inner);
            pool.add(Term::Let(binding.clone(), new_inner))
        }
        Term::Binder(q, bindings, inner) => {
            let new_inner = expand_string_constants(pool, inner);
            pool.add(Term::Binder(*q, bindings.clone(), new_inner))
        }
        Term::ParamOp { op, op_args, args } => {
            let new_args = args
                .iter()
                .map(|term| expand_string_constants(pool, term))
                .collect();
            pool.add(Term::ParamOp {
                op: *op,
                op_args: op_args.clone(),
                args: new_args,
            })
        }
        Term::Var(..) | Term::Const(_) | Term::Sort(_) => term.clone(),
    }
}

/// A function to reconstruct a term given its flat form.
///
/// It takes a vector of `Rc<Term>` and returns a new term based on the length
/// of the flat form vector. If the vector is empty, it's equivalent to the
/// empty String. If the length is equal to one, the only term of the vector
/// is returned. Finally, if the length is greater than one, an `str.++`
/// application is returned with the flat form vector as its arguments (e.g.,
/// `[a, "b", c]` would lead to `(str.++ a "b" c)`, where `a` and `c` are
/// arbitrary terms).
fn concat(pool: &mut dyn TermPool, terms: Vec<Rc<Term>>) -> Rc<Term> {
    match terms.len() {
        0 => pool.add(Term::new_string("")),
        1 => terms[0].clone(),
        _ => pool.add(Term::Op(Operator::StrConcat, terms)),
    }
}

/// A function to check if a term is a prefix or suffix of another.
///
/// It takes two `Rc<Term>` and a reverse parameter. If the reverse parameter is
/// set to `false`, it checks if the second term is a prefix of the first one,
/// and if it's set to `true`, it checks if it's a suffix.
///
/// The function throws an error if the prefix/suffix is larger than the main
/// term. It returns the prefix/suffix in flat form if the check was successful.
fn is_prefix_or_suffix(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    pref: Rc<Term>,
    rev: bool,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    let mut t_flat = flatten(pool, term.clone());
    let mut p_flat = flatten(pool, pref.clone());
    if rev {
        t_flat.reverse();
        p_flat.reverse();
    }
    if p_flat.len() > t_flat.len() {
        if rev {
            return Err(CheckerError::ExpectedToBeSuffix(pref, term));
        } else {
            return Err(CheckerError::ExpectedToBePrefix(pref, term));
        }
    }
    for (i, el) in p_flat.iter().enumerate() {
        assert_polyeq_expected(el, t_flat[i].clone(), polyeq_time)?;
    }
    if rev {
        p_flat.reverse();
    }
    Ok(p_flat)
}

/// An application of `is_prefix_or_suffix` where the reverse parameter is set
/// to `false` by default.
fn is_prefix(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    pref: Rc<Term>,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    is_prefix_or_suffix(pool, term, pref, false, polyeq_time)
}

/// An application of `is_prefix_or_suffix` where the reverse parameter is set
/// to `true` by default.
fn is_suffix(
    pool: &mut dyn TermPool,
    term: Rc<Term>,
    pref: Rc<Term>,
    polyeq_time: &mut Duration,
) -> Result<Vec<Rc<Term>>, CheckerError> {
    is_prefix_or_suffix(pool, term, pref, true, polyeq_time)
}

type Suffixes = (Vec<Rc<Term>>, Vec<Rc<Term>>);

/// A function to remove the longest common prefix or suffix.
///
/// It takes two `Rc<Term>` and a reverse parameter. If the parameter is set to
/// `false`, it removes the longest common prefix, and if it's set to `true`,
/// the longest common suffix.
///
/// The function throws an error if the terms aren't `str.++` applications.
/// It returns two vectors with the remaining terms after the removal in flat
/// form (e.g., the remaining suffixes after a prefix removal or vice versa).
///
/// If the terms don't share common prefixes or suffixes, the function
/// doesn't remove anything, so the tuple returned is the flat form for both of
/// them.
fn strip_prefix_or_suffix(
    pool: &mut dyn TermPool,
    s: Rc<Term>,
    t: Rc<Term>,
    rev: bool,
    polyeq_time: &mut Duration,
) -> Result<Suffixes, CheckerError> {
    let mut s_flat = flatten(pool, s.clone());
    let mut t_flat = flatten(pool, t.clone());
    if rev {
        s_flat.reverse();
        t_flat.reverse();
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s));
    }
    if t_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t));
    }
    let mut prefix = 0;
    while (prefix < cmp::min(s_flat.len(), t_flat.len()))
        && polyeq(&s_flat[prefix], &t_flat[prefix], polyeq_time)
    {
        prefix += 1;
    }
    let mut s_suffix = s_flat.get(prefix..).unwrap_or_default().to_vec();
    let mut t_suffix = t_flat.get(prefix..).unwrap_or_default().to_vec();
    if rev {
        s_suffix.reverse();
        t_suffix.reverse();
    }
    Ok((s_suffix, t_suffix))
}

/// A function to check if a String has a length equal to one.
///
/// It takes an `Rc<Term>` and throws an error if the term isn't a String
/// constant (we can't compute lengths properly in this case) or isn't a String
/// constant of size one.
fn string_check_length_one(term: Rc<Term>) -> Result<(), CheckerError> {
    if let Term::Const(Constant::String(s)) = term.as_ref() {
        if s.len() == 1 {
            return Ok(());
        }
    }
    Err(CheckerError::ExpectedStringConstantOfLengthOne(term))
}

fn build_skolem_prefix(pool: &mut dyn TermPool, u: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(pool, (strsubstr {u.clone()} 0 {n.clone()}))
}

fn build_skolem_suffix_rem(pool: &mut dyn TermPool, u: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(pool, (strsubstr {u.clone()} {n.clone()} (- (strlen {u.clone()}) {n})))
}

fn build_skolem_unify_split_prefix(pool: &mut dyn TermPool, t: Rc<Term>, s: Rc<Term>) -> Rc<Term> {
    let t_len = pool.add(Term::Op(Operator::StrLen, vec![t.clone()]));
    let s_len = pool.add(Term::Op(Operator::StrLen, vec![s.clone()]));
    let true_branch = build_skolem_suffix_rem(pool, t.clone(), s_len).clone();
    let false_branch = build_skolem_suffix_rem(pool, s.clone(), t_len).clone();
    build_term!(pool, (ite (>= (strlen {t.clone()}) (strlen {s.clone()})) {true_branch} {false_branch}))
}

fn build_skolem_unify_split_suffix(pool: &mut dyn TermPool, t: Rc<Term>, s: Rc<Term>) -> Rc<Term> {
    let t_len = pool.add(Term::Op(Operator::StrLen, vec![t.clone()]));
    let s_len = pool.add(Term::Op(Operator::StrLen, vec![s.clone()]));
    let n_t = build_term!(pool, (- {t_len.clone()} {s_len.clone()}));
    let n_s = build_term!(pool, (- {s_len.clone()} {t_len.clone()}));
    let true_branch = build_skolem_prefix(pool, t.clone(), n_t).clone();
    let false_branch = build_skolem_prefix(pool, s.clone(), n_s).clone();
    build_term!(pool, (ite (>= (strlen {t.clone()}) (strlen {s.clone()})) {true_branch} {false_branch}))
}

fn build_str_suffix_len(pool: &mut dyn TermPool, s: Rc<Term>, n: Rc<Term>) -> Rc<Term> {
    build_term!(pool, (strsubstr {s.clone()} (- (strlen {s.clone()}) {n.clone()}) {n.clone()}))
}

fn extract_arguments(t: &Rc<Term>) -> Result<Vec<Rc<Term>>, CheckerError> {
    let args_t = match t.as_ref() {
        Term::Op(Operator::StrConcat, args) => {
            if args.len() != 3 {
                return Err(CheckerError::TermOfWrongForm(
                    "(str.++ t1 t2 t3)",
                    t.clone(),
                ));
            }
            args
        }
        _ => {
            return Err(CheckerError::TermOfWrongForm(
                "(str.++ t1 t2 t3)",
                t.clone(),
            ))
        }
    };
    Ok(args_t.clone())
}

pub fn concat_eq(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= x y) = &conclusion[0])?;

    let term = get_premise_term(&premises[0])?;
    let rev = args[0].as_bool_err()?;
    let (s, t) = match_term_err!((= s t) = term)?;

    let (ss, ts) = strip_prefix_or_suffix(pool, s.clone(), t.clone(), rev, polyeq_time)?;
    let ss_concat = concat(pool, ss);
    let ts_concat = concat(pool, ts);
    let expected = build_term!(
        pool,
        (= {ss_concat.clone()} {ts_concat.clone()})
    );

    let expanded = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_unify(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= x y) = &conclusion[0])?;

    let term = get_premise_term(&premises[0])?;
    let prefixes = get_premise_term(&premises[1])?;
    let rev = args[0].as_bool_err()?;
    let (s, t) = match_term_err!((= s t) = term)?;
    let (s_1, t_1) = match_term_err!((= (strlen s_1) (strlen t_1)) = prefixes)?;

    let s_1 = is_prefix_or_suffix(pool, s.clone(), s_1.clone(), rev, polyeq_time)?;
    let t_1 = is_prefix_or_suffix(pool, t.clone(), t_1.clone(), rev, polyeq_time)?;
    let s_concat = concat(pool, s_1);
    let t_concat = concat(pool, t_1);
    let expected = build_term!(
        pool,
        (= {s_concat.clone()} {t_concat.clone()})
    );

    let expanded = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_conflict(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let rev = args[0].as_bool_err()?;
    if conclusion[0].as_bool_err()? {
        return Err(CheckerError::ExpectedBoolConstant(
            false,
            conclusion[0].clone(),
        ));
    }

    let (s, t) = match_term_err!((= s t) = term)?;
    let (mut ss, mut ts) = strip_prefix_or_suffix(pool, s.clone(), t.clone(), rev, polyeq_time)?;
    if rev {
        ss.reverse();
        ts.reverse();
    }

    if let Some(ss_head) = ss.first() {
        string_check_length_one(ss_head.clone())?;
        if let Some(ts_head) = ts.first() {
            string_check_length_one(ts_head.clone())?;
        }
    } else if let Some(ts_head) = ts.first() {
        string_check_length_one(ts_head.clone())?;
    } else {
        return Err(CheckerError::ExpectedDifferentConstantPrefixes(
            s.clone(),
            t.clone(),
        ));
    }

    Ok(())
}

pub fn concat_csplit_prefix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_1 x) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_1, _) = match_term_err!((not (= (strlen t_1) 0)) = length)?;

    let s_flat = flatten(pool, s.clone());
    if flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_prefix(pool, t.clone(), t_1.clone(), polyeq_time)?;
    let mut right_eq: Vec<Rc<Term>> = vec![];
    if let Some(c) = s_flat.first() {
        string_check_length_one(c.clone())?;
        right_eq.push(c.clone());
        let n = pool.add(Term::new_int(1));
        right_eq.push(build_skolem_suffix_rem(pool, t_1.clone(), n).clone());
    }

    let t_1 = expand_string_constants(pool, t_1);
    let right_eq_concat = concat(pool, right_eq);
    let expected = build_term!(
        pool,
        (= {t_1.clone()} {right_eq_concat.clone()})
    );

    let expanded = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_csplit_suffix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_2 x) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_2, _) = match_term_err!((not (= (strlen t_2) 0)) = length)?;

    let s_flat = flatten(pool, s.clone());
    if flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if s_flat.is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_suffix(pool, t.clone(), t_2.clone(), polyeq_time)?;
    let mut right_eq: Vec<Rc<Term>> = vec![];
    if let Some(c) = s_flat.last() {
        string_check_length_one(c.clone())?;
        let n = build_term!(pool, (- (strlen {t_2.clone()}) 1));
        right_eq.push(build_skolem_prefix(pool, t_2.clone(), n).clone());
        right_eq.push(c.clone());
    }

    let t_2 = expand_string_constants(pool, t_2);
    let right_eq_concat = concat(pool, right_eq);
    let expected = build_term!(
        pool,
        (= {t_2.clone()} {right_eq_concat.clone()})
    );

    let expanded = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_split_prefix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (or (= t_1 x) (= s_1 y))
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_1, s_1) = match_term_err!((not (= (strlen t_1) (strlen s_1))) = length)?;

    if flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if flatten(pool, s.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_prefix(pool, t.clone(), t_1.clone(), polyeq_time)?;
    is_prefix(pool, s.clone(), s_1.clone(), polyeq_time)?;
    let t_1 = expand_string_constants(pool, t_1);
    let s_1 = expand_string_constants(pool, s_1);
    let r = build_skolem_unify_split_prefix(pool, t_1.clone(), s_1.clone());

    let or = build_term!(
        pool,
        (or
            (=
                {t_1.clone()}
                (strconcat {s_1.clone()} {r.clone()})
            )
            (=
                {s_1.clone()}
                (strconcat {t_1.clone()} {r.clone()})
            )
        )
    );

    let empty = pool.add(Term::new_string(""));
    let expanded = build_term!(
        pool,
        (and
            {or.clone()}
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_split_suffix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (or (= t_2 x) (= s_2 y))
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_2, s_2) = match_term_err!((not (= (strlen t_2) (strlen s_2))) = length)?;

    if flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if flatten(pool, s.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_suffix(pool, t.clone(), t_2.clone(), polyeq_time)?;
    is_suffix(pool, s.clone(), s_2.clone(), polyeq_time)?;
    let t_2 = expand_string_constants(pool, t_2);
    let s_2 = expand_string_constants(pool, s_2);
    let r = build_skolem_unify_split_suffix(pool, t_2.clone(), s_2.clone());

    let or = build_term!(
        pool,
        (or
            (=
                {t_2.clone()}
                (strconcat {r.clone()} {s_2.clone()})
            )
            (=
                {s_2.clone()}
                (strconcat {r.clone()} {t_2.clone()})
            )
        )
    );

    let empty = pool.add(Term::new_string(""));
    let expanded = build_term!(
        pool,
        (and
            {or.clone()}
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_lprop_prefix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (= t_1 x)
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_1, s_1) = match_term_err!((> (strlen t_1) (strlen s_1)) = length)?;

    if flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if flatten(pool, s.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_prefix(pool, t.clone(), t_1.clone(), polyeq_time)?;
    is_prefix(pool, s.clone(), s_1.clone(), polyeq_time)?;
    let t_1 = expand_string_constants(pool, t_1);
    let s_1 = expand_string_constants(pool, s_1);
    let r = build_skolem_unify_split_prefix(pool, t_1.clone(), s_1.clone());

    let eq = build_term!(pool, (strconcat {s_1.clone()} {r.clone()}));
    let empty = pool.add(Term::new_string(""));
    let expanded = build_term!(
        pool,
        (and
            (= {t_1.clone()} {eq.clone()})
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_lprop_suffix(
    RuleArgs {
        premises,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!(
        (and
            (= t_2 x)
            (not (= r ""))
            (> (strlen r) 0)
        ) = &conclusion[0]
    )?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_2, s_2) = match_term_err!((> (strlen t_2) (strlen s_2)) = length)?;

    if flatten(pool, t.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", t.clone()));
    }
    if flatten(pool, s.clone()).is_empty() {
        return Err(CheckerError::TermOfWrongForm("(str.++ ...)", s.clone()));
    }

    is_suffix(pool, t.clone(), t_2.clone(), polyeq_time)?;
    is_suffix(pool, s.clone(), s_2.clone(), polyeq_time)?;
    let t_2 = expand_string_constants(pool, t_2);
    let s_2 = expand_string_constants(pool, s_2);
    let r = build_skolem_unify_split_suffix(pool, t_2.clone(), s_2.clone());

    let eq = build_term!(pool, (strconcat {r.clone()} {s_2.clone()}));
    let empty = pool.add(Term::new_string(""));
    let expanded = build_term!(
        pool,
        (and
            (= {t_2.clone()} {eq.clone()})
            (not (= {r.clone()} {empty.clone()}))
            (> (strlen {r.clone()}) 0)
        )
    );

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_cprop_prefix(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_1 (strconcat t_3 r)) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_1, _) = match_term_err!((not (= (strlen t_1) 0)) = length)?;

    let args_t = extract_arguments(t)?;

    assert_eq(&args_t[0], t_1)?;

    let empty = pool.add(Term::new_string(""));
    let ss = match s.as_ref() {
        Term::Const(Constant::String(text)) => {
            if text.is_empty() {
                return Err(CheckerError::ExpectedToNotBeEmpty(s.clone()));
            }
            vec![s.clone(), empty.clone()]
        }
        Term::Op(Operator::StrConcat, args) => args.clone(),
        _ => return Err(CheckerError::TermOfWrongForm("(str.++ s1 s2)", s.clone())),
    };

    let sc = flatten(pool, ss[0].clone());
    let sc_tail = sc[1..].to_vec();

    let t_2_flat = flatten(pool, args_t[1].clone());

    let v = 1 + overlap(sc_tail.clone(), t_2_flat.clone());
    let v = pool.add(Term::new_int(v));
    let oc = build_skolem_prefix(pool, ss[0].clone(), v);
    let oc_len = build_term!(pool, (strlen {oc.clone()}));

    let r = build_skolem_suffix_rem(pool, t_1.clone(), oc_len);
    let expanded = build_term!(pool, (= {t_1.clone()} (strconcat {oc.clone()} {r.clone()})));

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn concat_cprop_suffix(RuleArgs { premises, conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_num_premises(premises, 2)?;
    assert_clause_len(conclusion, 1)?;

    match_term_err!((= t_2 (strconcat r t_3)) = &conclusion[0])?;

    let terms = get_premise_term(&premises[0])?;
    let length = get_premise_term(&premises[1])?;
    let (t, s) = match_term_err!((= t s) = terms)?;
    let (t_2, _) = match_term_err!((not (= (strlen t_2) 0)) = length)?;

    let args_t = extract_arguments(t)?;

    assert_eq(&args_t[2], t_2)?;

    let empty = pool.add(Term::new_string(""));
    let ss = match s.as_ref() {
        Term::Const(Constant::String(text)) => {
            if text.is_empty() {
                return Err(CheckerError::ExpectedToNotBeEmpty(s.clone()));
            }
            vec![empty.clone(), s.clone()]
        }
        Term::Op(Operator::StrConcat, args) => args.clone(),
        _ => return Err(CheckerError::TermOfWrongForm("(str.++ s1 s2)", s.clone())),
    };

    let mut sc = flatten(pool, ss[1].clone());
    sc.reverse();
    let sc_tail = &sc[1..];

    let mut t_2_flat = flatten(pool, args_t[1].clone());
    t_2_flat.reverse();

    let v = 1 + overlap(sc_tail.to_vec(), t_2_flat.clone());
    let v = pool.add(Term::new_int(v));
    let oc = build_str_suffix_len(pool, ss[1].clone(), v);

    let rhs = build_term!(pool, (- (strlen {t_2.clone()}) (strlen {oc.clone()})));
    let r = build_skolem_prefix(pool, t_2.clone(), rhs.clone());
    let expanded = build_term!(pool, (= {t_2.clone()} (strconcat {r.clone()} {oc.clone()})));

    let expanded = expand_string_constants(pool, &expanded);
    let expected = expand_string_constants(pool, &conclusion[0]);

    assert_eq(&expected, &expanded)
}

pub fn string_decompose(
    RuleArgs {
        premises,
        args,
        conclusion,
        pool,
        polyeq_time,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let rev = args[0].as_bool_err()?;
    let (t, n) = match_term_err!((>= (strlen t) n) = term)?;

    match_term_err!(
        (and
            (= t x)
            (= (strlen y) n)
        ) = &conclusion[0]
    )?;

    let w_1 = build_skolem_prefix(pool, t.clone(), n.clone());
    let w_2 = build_skolem_suffix_rem(pool, t.clone(), n.clone());
    let len_term = if rev { w_2.clone() } else { w_1.clone() };

    let expanded = build_term!(
            pool,
            (and
                (= {t.clone()} (strconcat {w_1.clone()} {w_2.clone()}))
                (= (strlen {len_term.clone()}) {n.clone()})
            )
    );

    assert_polyeq(&conclusion[0], &expanded, polyeq_time)
}

pub fn string_length_pos(RuleArgs { args, conclusion, polyeq_time, .. }: RuleArgs) -> RuleResult {
    assert_num_args(args, 1)?;
    assert_clause_len(conclusion, 1)?;

    let t = &args[0];
    let (((t_1, _), (t_2, _)), (t_3, _)) = match_term_err!(
        (or
            (and
                (= (strlen t) 0)
                (= t "")
            )
            (> (strlen t) 0)
        ) = &conclusion[0]
    )?;

    assert_polyeq(t_1, t, polyeq_time)?;
    assert_polyeq(t_2, t, polyeq_time)?;
    assert_polyeq(t_3, t, polyeq_time)?;

    Ok(())
}

pub fn string_length_non_empty(
    RuleArgs {
        premises, conclusion, polyeq_time, ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 1)?;
    assert_clause_len(conclusion, 1)?;

    let term = get_premise_term(&premises[0])?;
    let (t, _) = match_term_err!((not (= t "")) = term)?;

    let (t_conc, _) = match_term_err!(
        (not
            (= (strlen t) 0)
        ) = &conclusion[0]
    )?;

    assert_polyeq(t_conc, t, polyeq_time)?;

    Ok(())
}

mod tests {
    #[test]
    fn concat_eq() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= "0A" (str.++ "0" (str.from_code (str.len a)))))
                   (step t1 (cl (= "A" (str.from_code (str.len a)))) :rule concat_eq :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= (str.++ "0" "A") (str.++ "0" (str.from_code (str.len a)))))
                   (step t1 (cl (= "A" (str.from_code (str.len a)))) :rule concat_eq :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ "AA" (str.at c (str.len c)))))
                   (step t1 (cl (= (str.++ b "A") (str.++ "A" (str.at c (str.len c))))) :rule concat_eq :premises (h1) :args (false))"#: true,
            }
            "Term are not a str.++ application" {
                r#"(assume h1 (= (str.++ "0" (str.from_int (str.len c))) ""))
                   (step t1 (cl (= (str.from_int (str.len c)) "")) :rule concat_eq :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= "0" (str.++ "" (str.from_int (str.len b)))))
                   (step t1 (cl (= "" (str.from_int (str.len b)))) :rule concat_eq :premises (h1) :args (false))"#: false,
            }
            "Terms with no common prefixes" {
                r#"(assume h1 (= "yxzw" (str.++ "xy" "z" a)))
                   (step t1 (cl (= "yxzw" (str.++ "xy" "z" a))) :rule concat_eq :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= (str.++ a (str.from_int (str.len b))) (str.++ "0" (str.++ "A" c))))
                   (step t1 (cl (= (str.++ a (str.from_int (str.len b))) (str.++ "0" (str.++ "A" c)))) :rule concat_eq :premises (h1) :args (false))"#: true,
            }
            "Concatenation with more than 2 arguments" {
                r#"(assume h1 (= "xyzw" (str.++ "xy" "z" a)))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= "xyzw" (str.++ "x" (str.++ "y" "z") a)))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: true,
            }
            "Reverse argument set to true" {
                r#"(assume h1 (= "wzyx" (str.++ a "z" "yx")))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (true))"#: true,
                r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ (str.at c (str.len c)) "AA")))
                   (step t1 (cl (= (str.++ "A" b) (str.++ (str.at c (str.len c)) "A"))) :rule concat_eq :premises (h1) :args (true))"#: true,
                r#"(assume h1 (= (str.++ (str.from_int (str.len c)) "0") "0"))
                   (step t1 (cl (= (str.from_int (str.len c)) "")) :rule concat_eq :premises (h1) :args (true))"#: true,
                r#"(assume h1 (= "0" (str.++ (str.from_int (str.len b)) "0")))
                   (step t1 (cl (= "" (str.from_int (str.len b)))) :rule concat_eq :premises (h1) :args (true))"#: true,
            }
            "Invalid argument type" {
                r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (1))"#: false,
                r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (1.5))"#: false,
                r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args ((- 1)))"#: false,
                r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args ("test"))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= "xyzw" (str.++ "xy" (str.++ "z" a)))))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: false,
            }
            "Conclusion term is not an equality" {
                r#"(assume h1 (= "xyzw" (str.++ "xy" "z" a)))
                   (step t1 (cl (not (= "w" a))) :rule concat_eq :premises (h1) :args (false))"#: false,
            }
            "Switched conclusion terms" {
                r#"(assume h1 (= "xyzw" (str.++ "xy" (str.++ "z" a))))
                   (step t1 (cl (= a "w")) :rule concat_eq :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "xy" (str.++ "z" a)) (str.++ "x" "yzw")))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ "AA" (str.at c (str.len c)))))
                   (step t1 (cl (= (str.++ "A" (str.at c (str.len c))) (str.++ b "A"))) :rule concat_eq :premises (h1) :args (false))"#: false,
            }
            "Prefix was not fully consumed" {
                r#"(assume h1 (= (str.++ "a" "b" b (str.++ "c" "d")) (str.++ "a" "b" (str.++ b c))))
                   (step t1 (cl (= (str.++ b "cd") (str.++ b c))) :rule concat_eq :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "A" (str.++ b "AA")) (str.++ (str.at c (str.len c)) "AA")))
                   (step t1 (cl (= (str.++ "A" (str.++ b "A")) (str.++ (str.at c (str.len c)) "A"))) :rule concat_eq :premises (h1) :args (true))"#: false,
            }
            "Inverted argument value" {
                r#"(assume h1 (= (str.++ "w" (str.++ "z" "y" "x")) (str.++ a "z" "yx")))
                   (step t1 (cl (= "w" a)) :rule concat_eq :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "A" (str.++ b "A")) (str.++ (str.at c (str.len c)) "AA")))
                   (step t1 (cl (= (str.++ "A" b) (str.++ (str.at c (str.len c)) "A"))) :rule concat_eq :premises (h1) :args (false))"#: false,
            }
        }
    }

    #[test]
    fn concat_unify() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= "abcd" "abcd"))
                   (assume h2 (= (str.len "abc") (str.len "abc")))
                   (step t1 (cl (= "abc" "abc")) :rule concat_unify :premises (h1 h2) :args (false))"#: true,
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" b)) (str.len "a")))
                   (step t1 (cl (= (str.++ "a" b) "a")) :rule concat_unify :premises (h1 h2) :args (false))"#: true,
                r#"(assume h1 (= (str.++ a b c) d))
                   (assume h2 (= (str.len (str.++ a b)) (str.len "")))
                   (step t1 (cl (= (str.++ a b) "")) :rule concat_unify :premises (h1 h2) :args (false))"#: true,
            }
            "Reverse argument set to true" {
                r#"(assume h1 (= "abcd" "abcd"))
                   (assume h2 (= (str.len "cd") (str.len "cd")))
                   (step t1 (cl (= "cd" "cd")) :rule concat_unify :premises (h1 h2) :args (true))"#: true,
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ d "e")) (str.len (str.++ "d" "e"))))
                   (step t1 (cl (= (str.++ d "e") "de")) :rule concat_unify :premises (h1 h2) :args (true))"#: true,
            }
            "Failing examples" {
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ a c "de")))
                   (assume h2 (= (str.len (str.++ "a" "b")) (str.len a)))
                   (step t1 (cl (= (str.++ "a" b) a)) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ a c "de")))
                   (assume h2 (= (str.len (str.++ "a" "b")) (str.len a)))
                   (step t1 (cl (= (str.++ a b) "")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Invalid argument type" {
                r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
                   (assume h2 (= (str.len a) (str.len "")))
                   (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args (1))"#: false,
                r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
                   (assume h2 (= (str.len a) (str.len "")))
                   (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args ((- 1)))"#: false,
                r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
                   (assume h2 (= (str.len a) (str.len "")))
                   (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args ("test"))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ a "b" c) (str.++ a d "e"))))
                   (assume h2 (= (str.len a) (str.len "")))
                   (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
                   (assume h2 (not (= (str.len a) (str.len ""))))
                   (step t1 (cl (= a "")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Conclusion term is not an equality" {
                r#"(assume h1 (= (str.++ a "b" c) (str.++ a d "e")))
                   (assume h2 (= (str.len a) (str.len "")))
                   (step t1 (cl (not (= a ""))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Switched conclusion terms" {
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" b)) (str.len "a")))
                   (step t1 (cl (= "a" (str.++ "a" b))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "a" c "de") (str.++ "a" b "c" (str.++ d "e"))))
                   (assume h2 (= (str.len "a") (str.len (str.++ "a" b))))
                   (step t1 (cl (= (str.++ "a" b) "a")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Inverted argument value" {
                r#"(assume h1 (= (str.++ "x" (str.++ a "y") b) (str.++ "x" c "de")))
                   (assume h2 (= (str.len (str.++ "y" b)) (str.len (str.++ c "d"))))
                   (step t1 (cl (= (str.++ "y" b) (str.++ c "d"))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ d "e")) (str.len (str.++ c "de"))))
                   (step t1 (cl (= (str.++ d "e") (str.++ c "de"))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Invalid prefixes" {
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" "b")) (str.len "a")))
                   (step t1 (cl (= (str.++ "a" "b") "a")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "a" b "c" (str.++ d "e")) (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" b)) (str.len "b")))
                   (step t1 (cl (= (str.++ "a" b) "b")) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
            "Prefix is bigger than the term" {
                r#"(assume h1 (= (str.++ "a" b "c") (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" b "c" "d")) (str.len (str.++ "a" c))))
                   (step t1 (cl (= (str.++ "a" b "c" "d") (str.++ "a" c))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "a" b "c") (str.++ "a" c "de")))
                   (assume h2 (= (str.len (str.++ "a" b)) (str.len (str.++ "a" c "de" "f"))))
                   (step t1 (cl (= (str.++ "a" b) (str.++ "a" c (str.++ "de" "f")))) :rule concat_unify :premises (h1 h2) :args (false))"#: false,
            }
        }
    }

    #[test]
    fn concat_conflict() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
                (declare-fun e () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= (str.++ "abc" d) (str.++ "abd" (str.++ c e))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: true,
                r#"(assume h1 (= (str.++ "ac" (str.++ b d)) (str.++ "abd" (str.++ a b))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: true,
            }
            "Reverse argument set to true" {
                r#"(assume h1 (= (str.++ d "cba") (str.++ (str.++ e c) "dba")))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: true,
                r#"(assume h1 (= (str.++ (str.++ d b) "ac") (str.++ (str.++ b a) "dba")))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: true,
            }
            "All possible constants are prefixes of each other" {
                r#"(assume h1 (= (str.++ "ac" "bd" c e) (str.++ "acb" b c)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "d" a b) (str.++ "de" c d)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" a b) (str.++ "ab" c d)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Remaining suffix is empty" {
                r#"(assume h1 (= "ab" (str.++ "ab" c d)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= "ab" (str.++ "ab" (str.++ "" c d))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= "cbd" (str.++ "c" "bd")))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "cbd" a) (str.++ "c" (str.++ "bd" a))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" c d) "ab"))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" (str.++ "" c d)) "ab"))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Term does not have a constant prefix" {
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ "ab" c)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "b" "cd" e) (str.++ b "cb" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Term are not a str.++ application" {
                r#"(assume h1 (= (str.++ "ac" "bd" c e) ""))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= "" (str.++ "ab" c)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Invalid argument type" {
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (1))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (1.5))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args ((- 1)))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args ("test"))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ "ab" c) (str.++ "c" e))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Conclusion term is not the false bool constant" {
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl true) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl (= "a" b)) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl (= "a" "b")) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl (not (= "a" "b"))) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
            "Inverted argument value" {
                r#"(assume h1 (= (str.++ "ab" c) (str.++ "c" e)))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: false,
                r#"(assume h1 (= (str.++ "abc" d) (str.++ "abd" (str.++ c e))))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (true))"#: false,
                r#"(assume h1 (= (str.++ d "cba") (str.++ (str.++ e c) "dba")))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
                r#"(assume h1 (= (str.++ (str.++ d b) "ac") (str.++ (str.++ b a) "dba")))
                   (step t1 (cl false) :rule concat_conflict :premises (h1) :args (false))"#: false,
            }
        }
    }

    #[test]
    fn concat_csplit_prefix() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ a "b" c) (str.++ "ab" c)))
                   (assume h2 (not (= (str.len (str.++ a "b")) 0)))
                   (step t1 (cl (= (str.++ a "b") (str.++ "a" (str.substr (str.++ a "b") 1 (- (str.len (str.++ a "b")) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: true,
            }
            "Term does not have a constant prefix" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ b (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ b (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
            }
            "The term of the second premise is not a prefix of the first one" {
                r#"(assume h1 (= (str.++ a "b" c) (str.++ "ab" c)))
                   (assume h2 (not (= (str.len (str.++ "b" a)) 0)))
                   (step t1 (cl (= (str.++ a "b") (str.++ "a" (str.substr (str.++ a "b") 1 (- (str.len (str.++ a "b")) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
            }
            "Term are not a str.++ application" {
                r#"(assume h1 (= (str.++ "a" "b" b) ""))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= "" (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") 0)))
                   (step t1 (cl (= "a" (str.++ "a" (str.substr "a" 1 (- (str.len "a") 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d)))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
            }
            "Premise term is not an inequality of the form (not (= (str.len str) 0))" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (= (str.len (str.++ d c)) 0))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.to_code (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 1)))
                   (step t1 (cl (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
            }
            "Conclusion term is not an equality" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (not (= (str.++ d c) (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1)))))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
            }
            "Switched conclusion terms" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ b "a"))) (str.++ "b" (str.++ "c" d))))
                   (assume h2 (not (= (str.len (str.++ d c)) 0)))
                   (step t1 (cl (= (str.++ "b" (str.substr (str.++ d c) 1 (- (str.len (str.++ d c)) 1))) (str.++ d c))) :rule concat_csplit_prefix :premises (h1 h2))"#: false,
            }
        }
    }

    #[test]
    fn concat_csplit_suffix() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "c" "b" a) (str.++ a (str.++ c "b"))))
                   (assume h2 (not (= (str.len (str.++ "b" a)) 0)))
                   (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit_suffix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
                   (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit_suffix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ d (str.++ "c" (str.++ "b" a))) (str.++ "b" (str.++ c "d"))))
                   (assume h2 (not (= (str.len (str.++ "c" (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ "c" (str.++ "b" a)) (str.++ (str.substr (str.++ "c" (str.++ "b" a)) 0 (- (str.len (str.++ "c" (str.++ "b" a))) 1)) "d"))) :rule concat_csplit_suffix :premises (h1 h2))"#: true,
            }
            "Term does not have a constant suffix" {
                r#"(assume h1 (= (str.++ "c" "b" a) (str.++ a (str.++ c b))))
                   (assume h2 (not (= (str.len (str.++ "b" a)) 0)))
                   (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
            }
            "The term of the second premise is not a suffix of the first one" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
                   (assume h2 (not (= (str.len (str.++ c (str.++ a "b"))) 0)))
                   (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
            }
            "Term are not a str.++ application" {
                r#"(assume h1 (= "" (str.++ "b" (str.++ "c" "de"))))
                   (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) ""))
                   (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ d (str.++ "c" (str.++ "b" a))) (str.++ "b" (str.++ c "d")))))
                   (assume h2 (not (= (str.len (str.++ "c" (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ "c" (str.++ "b" a)) (str.++ (str.substr (str.++ "c" (str.++ "b" a)) 0 (- (str.len (str.++ "c" (str.++ "b" a))) 1)) "d"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
            }
            "Premise term is not an inequality of the form (not (= (str.len str) 0))" {
                r#"(assume h1 (= (str.++ "c" "b" a) (str.++ a (str.++ c "b"))))
                   (assume h2 (= (str.len (str.++ "b" a)) 0))
                   (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "c" "b" a) (str.++ a (str.++ c "b"))))
                   (assume h2 (not (= (str.to_code (str.++ "b" a)) 0)))
                   (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "c" "b" a) (str.++ a (str.++ c "b"))))
                   (assume h2 (not (= (str.len (str.++ "b" a)) 1)))
                   (step t1 (cl (= (str.++ "b" a) (str.++ (str.substr (str.++ "b" a) 0 (- (str.len (str.++ "b" a)) 1)) "b"))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
            }
            "Conclusion term is not an equality" {
                r#"(assume h1 (= (str.++ d (str.++ c (str.++ "b" a))) (str.++ "b" (str.++ "c" "de"))))
                   (assume h2 (not (= (str.len (str.++ c (str.++ "b" a))) 0)))
                   (step t1 (cl (not (= (str.++ c (str.++ "b" a)) (str.++ (str.substr (str.++ c (str.++ "b" a)) 0 (- (str.len (str.++ c (str.++ "b" a))) 1)) "e")))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
            }
            "Switched conclusion terms" {
                r#"(assume h1 (= (str.++ d (str.++ "c" (str.++ "b" a))) (str.++ "b" (str.++ c "d"))))
                   (assume h2 (not (= (str.len (str.++ "c" (str.++ "b" a))) 0)))
                   (step t1 (cl (= (str.++ (str.substr (str.++ "c" (str.++ "b" a)) 0 (- (str.len (str.++ "c" (str.++ "b" a))) 1)) "d") (str.++ "c" (str.++ "b" a)))) :rule concat_csplit_suffix :premises (h1 h2))"#: false,
            }
        }
    }

    #[test]
    fn concat_split_prefix() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
                (declare-fun e () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") (str.len (str.++ "a" c)))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: true,
            }
            "The term of the second premise is not a prefix of the first one" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len a) (str.len (str.++ "a" c)))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") (str.len (str.++ c "a")))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            }
            "Terms are not str.++ applications" {
                r#"(assume h1 (= "" (str.++ "a" c)))
                   (assume h2 (not (= (str.len "a") (str.len (str.++ "a" c)))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) ""))
                   (assume h2 (not (= (str.len "a") (str.len (str.++ "a" c)))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ a b c) (str.++ c d e))))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            }
            "Premise term is not an inequality of the form (not (= (str.len t_1) (str.len s_1)))" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (= (str.len "a") (str.len (str.++ "a" c))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.to_code "a") (str.to_code (str.++ "a" c)))))
                   (define-fun r_skolem () String (ite (>= (str.len "a") (str.len (str.++ "a" c))) (str.substr "a" (str.len (str.++ "a" c)) (- (str.len "a") (str.len (str.++ "a" c)))) (str.substr (str.++ "a" c) (str.len "a") (- (str.len (str.++ "a" c)) (str.len "a")))))
                   (step t1 (cl (and (or (= "a" (str.++ "a" c r_skolem)) (= (str.++ "a" c) (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            }
            "Conclusion term is not of the form (and (or (= x y) (= z w)) (not (= r \"\")) (> (str.len r) 0))" {
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (or (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (and (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (not (= (str.++ a b) (str.++ c r_skolem))) (not (= c (str.++ a b r_skolem)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (= r_skolem "") (> (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 1))) :rule concat_split_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c) (str.++ c d e)))
                   (assume h2 (not (= (str.len (str.++ a b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ a b)) (str.len c)) (str.substr (str.++ a b) (str.len c) (- (str.len (str.++ a b)) (str.len c))) (str.substr c (str.len (str.++ a b)) (- (str.len c) (str.len (str.++ a b))))))
                   (step t1 (cl (and (or (= (str.++ a b) (str.++ c r_skolem)) (= c (str.++ a b r_skolem))) (not (= r_skolem "")) (< (str.len r_skolem) 0))) :rule concat_split_prefix :premises (h1 h2))"#: false,
            }
        }
    }

    #[test]
    fn concat_split_suffix() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
                (declare-fun e () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len (str.++ "b" b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: true,
            }
            "The term of the second premise is not a suffix of the first one" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len (str.++ b "b")) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.len (str.++ "b" b)) (str.len "a"))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            }
            "Terms are not str.++ applications" {
                r#"(assume h1 (= "" (str.++ "a" c)))
                   (assume h2 (not (= (str.len (str.++ "b" b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) ""))
                   (assume h2 (not (= (str.len (str.++ "b" b)) (str.len c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ a b c d) (str.++ b c d e))))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            }
            "Premise term is not an inequality of the form (not (= (str.len t_2) (str.len s_2)))" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (= (str.len (str.++ "b" b)) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (not (= (str.to_code (str.++ "b" b)) (str.to_code c))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (or (= (str.++ "b" b) (str.++ r_skolem c)) (= c (str.++ r_skolem (str.++ "b" b)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            }
            "Conclusion term is not of the form (and (or (= x y) (= z w)) (not (= r \"\")) (> (str.len r) 0))" {
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (or (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (and (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (not (= (str.++ c d e) (str.++ r_skolem (str.++ c d))))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (= r_skolem "") (> (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (> (str.len r_skolem) 1))) :rule concat_split_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b c d) (str.++ b c d e)))
                   (assume h2 (not (= (str.len (str.++ c d)) (str.len (str.++ c d e)))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c d)) (str.len (str.++ c d e))) (str.substr (str.++ c d) 0 (- (str.len (str.++ c d)) (str.len (str.++ c d e)))) (str.substr (str.++ c d e) 0 (- (str.len (str.++ c d e)) (str.len (str.++ c d))))))
                   (step t1 (cl (and (or (= (str.++ c d) (str.++ r_skolem (str.++ c d e))) (= (str.++ c d e) (str.++ r_skolem (str.++ c d)))) (not (= r_skolem "")) (< (str.len r_skolem) 0))) :rule concat_split_suffix :premises (h1 h2))"#: false,
            }
        }
    }

    #[test]
    fn concat_lprop_prefix() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
                   (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
                   (assume h2 (> (str.len (str.++ d c b)) (str.len (str.++ "d" b))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ d c b)) (str.len (str.++ "d" b))) (str.substr (str.++ d c b) (str.len (str.++ "d" b)) (- (str.len (str.++ d c b)) (str.len (str.++ "d" b)))) (str.substr (str.++ "d" b) (str.len (str.++ d c b)) (- (str.len (str.++ "d" b)) (str.len (str.++ d c b))))))
                   (step t1 (cl (and (= (str.++ d c b) (str.++ "d" b r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: true,
            }
            "The term of the second premise is not a prefix of the first one" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "a" b)) (str.len "a")))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
                   (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "a" "b")) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
                   (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            }
            "Term are not a str.++ application" {
                r#"(assume h1 (= "" (str.++ "d" b (str.++ c "a"))))
                   (assume h2 (> (str.len (str.++ d c b)) (str.len (str.++ "d" b))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ d c b)) (str.len (str.++ "d" b))) (str.substr (str.++ d c b) (str.len (str.++ "d" b)) (- (str.len (str.++ d c b)) (str.len (str.++ "d" b)))) (str.substr (str.++ "d" b) (str.len (str.++ d c b)) (- (str.len (str.++ "d" b)) (str.len (str.++ d c b))))))
                   (step t1 (cl (and (= (str.++ d c b) (str.++ "d" b r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d c b a) ""))
                   (assume h2 (> (str.len (str.++ d c b)) (str.len (str.++ "d" b))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ d c b)) (str.len (str.++ "d" b))) (str.substr (str.++ d c b) (str.len (str.++ "d" b)) (- (str.len (str.++ d c b)) (str.len (str.++ "d" b)))) (str.substr (str.++ "d" b) (str.len (str.++ d c b)) (- (str.len (str.++ "d" b)) (str.len (str.++ d c b))))))
                   (step t1 (cl (and (= (str.++ d c b) (str.++ "d" b r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ "a" "b" b) (str.++ "a" c))))
                   (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
                   (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            }
            "Premise term is not of the form (> (strlen t_1) (strlen s_1))" {
                r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
                   (assume h2 (< (str.len (str.++ d c b)) (str.len (str.++ "d" b))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ d c b)) (str.len (str.++ "d" b))) (str.substr (str.++ d c b) (str.len (str.++ "d" b)) (- (str.len (str.++ d c b)) (str.len (str.++ "d" b)))) (str.substr (str.++ "d" b) (str.len (str.++ d c b)) (- (str.len (str.++ "d" b)) (str.len (str.++ d c b))))))
                   (step t1 (cl (and (= (str.++ d c b) (str.++ "d" b r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
                   (assume h2 (> (str.to_code (str.++ d c b)) (str.to_code (str.++ "d" b))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ d c b)) (str.len (str.++ "d" b))) (str.substr (str.++ d c b) (str.len (str.++ "d" b)) (- (str.len (str.++ d c b)) (str.len (str.++ "d" b)))) (str.substr (str.++ "d" b) (str.len (str.++ d c b)) (- (str.len (str.++ "d" b)) (str.len (str.++ d c b))))))
                   (step t1 (cl (and (= (str.++ d c b) (str.++ "d" b r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            }
            r#"Conclusion term is not of the form (and (= t_1 x) (not (= r "")) (> (str.len r) 0))"# {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
                   (step t1 (cl (or (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
                   (step t1 (cl (and (not (= (str.++ "a" "b") (str.++ "a" r_skolem))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
                   (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (= r_skolem "") (> (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
                   (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (< (str.len r_skolem) 0))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "a" "b")) (str.len "a")))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "a" "b")) (str.len "a")) (str.substr (str.++ "a" "b") (str.len "a") (- (str.len (str.++ "a" "b")) (str.len "a"))) (str.substr "a" (str.len (str.++ "a" "b")) (- (str.len "a") (str.len (str.++ "a" "b"))))))
                   (step t1 (cl (and (= (str.++ "a" "b") (str.++ "a" r_skolem)) (not (= r_skolem "")) (> (str.len r_skolem) 1))) :rule concat_lprop_prefix :premises (h1 h2))"#: false,
            }
        }
    }

    #[test]
    fn concat_lprop_suffix() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
                   (assume h2 (> (str.len (str.++ c (str.++ b a))) (str.len (str.++ c "a"))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c b a)) (str.len (str.++ c "a"))) (str.substr (str.++ c b a) 0 (- (str.len (str.++ c b a)) (str.len (str.++ c "a")))) (str.substr (str.++ c "a") 0 (- (str.len (str.++ c "a")) (str.len (str.++ c b a))))))
                   (step t1 (cl (and (= (str.++ c (str.++ b a)) (str.++ r_skolem c "a")) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: true,
            }
            "The term of the second premise is not a suffix of the first one" {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ b "b")) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "b" b)) (str.len "a")))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            }
            "Term are not a str.++ application" {
                r#"(assume h1 (= "" (str.++ "d" b (str.++ c "a"))))
                   (assume h2 (> (str.len (str.++ c (str.++ b a))) (str.len (str.++ c "a"))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c b a)) (str.len (str.++ c "a"))) (str.substr (str.++ c b a) 0 (- (str.len (str.++ c b a)) (str.len (str.++ c "a")))) (str.substr (str.++ c "a") 0 (- (str.len (str.++ c "a")) (str.len (str.++ c b a))))))
                   (step t1 (cl (and (= (str.++ c (str.++ b a)) (str.++ r_skolem c "a")) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d c b a) ""))
                   (assume h2 (> (str.len (str.++ c (str.++ b a))) (str.len (str.++ c "a"))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c b a)) (str.len (str.++ c "a"))) (str.substr (str.++ c b a) 0 (- (str.len (str.++ c b a)) (str.len (str.++ c "a")))) (str.substr (str.++ c "a") 0 (- (str.len (str.++ c "a")) (str.len (str.++ c b a))))))
                   (step t1 (cl (and (= (str.++ c (str.++ b a)) (str.++ r_skolem c "a")) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ "a" "b" b) (str.++ "a" c))))
                   (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            }
            "Premise term is not of the form (> (strlen t_2) (strlen s_2))" {
                r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
                   (assume h2 (< (str.len (str.++ c (str.++ b a))) (str.len (str.++ c "a"))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c b a)) (str.len (str.++ c "a"))) (str.substr (str.++ c b a) 0 (- (str.len (str.++ c b a)) (str.len (str.++ c "a")))) (str.substr (str.++ c "a") 0 (- (str.len (str.++ c "a")) (str.len (str.++ c b a))))))
                   (step t1 (cl (and (= (str.++ c (str.++ b a)) (str.++ r_skolem c "a")) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d c b a) (str.++ "d" b (str.++ c "a"))))
                   (assume h2 (> (str.to_code (str.++ c (str.++ b a))) (str.to_code (str.++ c "a"))))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ c b a)) (str.len (str.++ c "a"))) (str.substr (str.++ c b a) 0 (- (str.len (str.++ c b a)) (str.len (str.++ c "a")))) (str.substr (str.++ c "a") 0 (- (str.len (str.++ c "a")) (str.len (str.++ c b a))))))
                   (step t1 (cl (and (= (str.++ c (str.++ b a)) (str.++ r_skolem c "a")) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            }
            r#"Conclusion term is not of the form (and (= t_2 x) (not (= r "")) (> (str.len r) 0))"# {
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (or (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (not (= (str.++ "b" b) (str.++ r_skolem c))) (not (= r_skolem "")) (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (= r_skolem "") (> (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (< (str.len r_skolem) 0))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "a" "b" b) (str.++ "a" c)))
                   (assume h2 (> (str.len (str.++ "b" b)) (str.len c)))
                   (define-fun r_skolem () String (ite (>= (str.len (str.++ "b" b)) (str.len c)) (str.substr (str.++ "b" b) 0 (- (str.len (str.++ "b" b)) (str.len c))) (str.substr c 0 (- (str.len c) (str.len (str.++ "b" b))))))
                   (step t1 (cl (and (= (str.++ "b" b) (str.++ r_skolem c)) (not (= r_skolem "")) (> (str.len r_skolem) 1))) :rule concat_lprop_suffix :premises (h1 h2))"#: false,
            }
        }
    }

    #[test]
    fn concat_cprop_prefix() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
                (declare-fun e () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ "aabc" e)))
                   (assume h2 (not (= (str.len a) 0)))
                   (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: true,
            }
            "Term is not a str.++ application" {
                r#"(assume h1 (= a (str.++ "aabc" e)))
                   (assume h2 (not (= (str.len a) 0)))
                   (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= "abc" (str.++ "aabc" e)))
                   (assume h2 (not (= (str.len a) 0)))
                   (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            }
            "Term is not a str.++ application with 3 arguments" {
                r#"(assume h1 (= (str.++ "dcba" e) "acda"))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a b "dcba" e) "acda"))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            }
            "Term is not a String constant or a str.++ application" {
                r#"(assume h1 (= (str.++ a "bc" d) a))
                   (assume h2 (not (= (str.len a) 0)))
                   (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a "bc" d) ""))
                   (assume h2 (not (= (str.len a) 0)))
                   (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not(= (str.++ d "dcba" e) "acda")))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            }
            "Premise term is not of the form (not (= (str.len t_1) 0))" {
                r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
                   (assume h2 (= (str.len d) 0))
                   (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
                   (assume h2 (not (> (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
                   (assume h2 (not (= (str.to_code d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
                   (assume h2 (not (> (str.len d) 1)))
                   (step t1 (cl (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            }
            "Term shared between the premises is not the same" {
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ "aabc" e)))
                   (assume h2 (not (= (str.len b) 0)))
                   (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ (str.++ "ab" "c") "bc" d) (str.++ "aabc" e)))
                   (assume h2 (not (= (str.len "abc") 0)))
                   (step t1 (cl (= a (str.++ (str.substr "aabc" 0 2) (str.substr a (str.len (str.substr "aabc" 0 2)) (- (str.len a) (str.len (str.substr "aabc" 0 2))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            }
            "Conclusion term is not of the form (= t_1 (str.++ t_3 r))" {
                r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= a (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (not (= d (str.++ (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3)))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= a (str.++ a (str.substr "acda" 0 3) (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3))))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d "dcba" e) "acda"))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= a (str.substr d (str.len (str.substr "acda" 0 3)) (- (str.len d) (str.len (str.substr "acda" 0 3)))))) :rule concat_cprop_prefix :premises (h1 h2))"#: false,
            }
        }
    }

    #[test]
    fn concat_cprop_suffix() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
                (declare-fun e () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: true,
                r#"(assume h1 (= (str.++ d "dcba" (str.++ a b)) "acda"))
                   (assume h2 (not (= (str.len (str.++ a b)) 0)))
                   (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: true,
            }
            "Term is not a str.++ application" {
                r#"(assume h1 (= b (str.++ e "aabc")))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= "abcd" (str.++ e "aabc")))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            }
            "Term is not a str.++ application with 3 arguments" {
                r#"(assume h1 (= (str.++ "dcba" (str.++ a b)) "acda"))
                   (assume h2 (not (= (str.len (str.++ a b)) 0)))
                   (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ "abc" d "dcba" (str.++ a b)) "acda"))
                   (assume h2 (not (= (str.len (str.++ a b)) 0)))
                   (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            }
            "Term is not a String constant or a str.++ application" {
                r#"(assume h1 (= (str.++ a "bc" d) b))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a "bc" d) ""))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            }
            "Premise term is not an equality" {
                r#"(assume h1 (not (= (str.++ d "dcba" (str.++ a b)) "acda")))
                   (assume h2 (not (= (str.len (str.++ a b)) 0)))
                   (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            }
            "Premise term is not of the form (not (= (str.len t_2) 0))" {
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
                   (assume h2 (= (str.len d) 0))
                   (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
                   (assume h2 (not (> (str.len d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
                   (assume h2 (not (= (str.to_code d) 0)))
                   (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
                   (assume h2 (not (= (str.len d) 1)))
                   (step t1 (cl (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            }
            "Term shared between the premises is not the same" {
                r#"(assume h1 (= (str.++ d "dcba" (str.++ a b)) "acda"))
                   (assume h2 (not (= (str.len c) 0)))
                   (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ d "dcba" (str.++ "a" "b")) "acda"))
                   (assume h2 (not (= (str.len "ab") 0)))
                   (step t1 (cl (= (str.++ a b) (str.++ (str.substr (str.++ a b) 0 (- (str.len (str.++ a b)) (str.len (str.substr "acda" (- (str.len "acda") 3) 3)))) (str.substr "acda" (- (str.len "acda") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            }
            "Conclusion term is not of the form (= t_2 (str.++ r t_3))" {
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= a (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (not (= d (str.++ (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3))))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.++ a (str.substr d 0 (- (str.len d) (str.len (str.substr "aabc" (- (str.len "aabc") 3) 3)))) (str.substr "aabc" (- (str.len "aabc") 3) 3)))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
                r#"(assume h1 (= (str.++ a "bc" d) (str.++ e "aabc")))
                   (assume h2 (not (= (str.len d) 0)))
                   (step t1 (cl (= d (str.substr "aabc" (- (str.len "aabc") 3) 3))) :rule concat_cprop_suffix :premises (h1 h2))"#: false,
            }
        }
    }

    #[test]
    fn string_decompose() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (>= (str.len "ab") 2))
                   (define-fun w_1 () String (str.substr "ab" 0 2))
                   (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
                   (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args (false))"#: true,
                r#"(assume h1 (>= (str.len (str.++ "d" "c")) 1))
                   (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
                   (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
                   (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_1 w_2)) (= (str.len w_1) 1))) :rule string_decompose :premises (h1) :args (false))"#: true,
                r#"(assume h1 (>= (str.len (str.++ a (str.++ "b" c))) 0))
                   (define-fun w_1 () String (str.substr (str.++ a (str.++ "b" c)) 0 0))
                   (define-fun w_2 () String (str.substr (str.++ a (str.++ "b" c)) 0 (- (str.len (str.++ a (str.++ "b" c))) 0)))
                   (step t1 (cl (and (= (str.++ a (str.++ "b" c)) (str.++ w_1 w_2)) (= (str.len w_1) 0))) :rule string_decompose :premises (h1) :args (false))"#: true,
            }
            "Reverse argument set to true" {
                r#"(assume h1 (>= (str.len "ab") 2))
                   (define-fun w_1 () String (str.substr "ab" 0 2))
                   (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
                   (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_2) 2))) :rule string_decompose :premises (h1) :args (true))"#: true,
                r#"(assume h1 (>= (str.len (str.++ "d" "c")) 1))
                   (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
                   (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
                   (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_1 w_2)) (= (str.len w_2) 1))) :rule string_decompose :premises (h1) :args (true))"#: true,
            }
            "Invalid argument type" {
                r#"(assume h1 (>= (str.len "ab") 2))
                   (define-fun w_1 () String (str.substr "ab" 0 2))
                   (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
                   (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args (1))"#: false,
                r#"(assume h1 (>= (str.len "ab") 2))
                   (define-fun w_1 () String (str.substr "ab" 0 2))
                   (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
                   (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args (1.5))"#: false,
                r#"(assume h1 (>= (str.len "ab") 2))
                   (define-fun w_1 () String (str.substr "ab" 0 2))
                   (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
                   (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args ((- 1)))"#: false,
                r#"(assume h1 (>= (str.len "ab") 2))
                   (define-fun w_1 () String (str.substr "ab" 0 2))
                   (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
                   (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args ("teste"))"#: false,
                r#"(assume h1 (>= (str.len "ab") 2))
                   (define-fun w_1 () String (str.substr "ab" 0 2))
                   (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
                   (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args (d))"#: false,
            }
            "Premise term \"t\" is not the same in the conclusion" {
                r#"(assume h1 (>= (str.len "ab") 2))
                   (define-fun w_1 () String (str.substr "ab" 0 2))
                   (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
                   (step t1 (cl (and (= "ba" (str.++ w_1 w_2)) (= (str.len w_2) 2))) :rule string_decompose :premises (h1) :args (true))"#: false,
                r#"(assume h1 (>= (str.len "ba") 2))
                   (define-fun w_1 () String (str.substr "ba" 0 2))
                   (define-fun w_2 () String (str.substr "ba" 2 (- (str.len "ba") 2)))
                   (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_2) 2))) :rule string_decompose :premises (h1) :args (true))"#: false,
                r#"(assume h1 (>= (str.len (str.++ "a" (str.++ b "c"))) 2))
                   (define-fun w_1 () String (str.substr (str.++ "a" (str.++ b "c")) 0 2))
                   (define-fun w_2 () String (str.substr (str.++ "a" (str.++ b "c")) 2 (- (str.len (str.++ "a" (str.++ b "c"))) 2)))
                   (step t1 (cl (and (= (str.++ a (str.++ b "c")) (str.++ w_1 w_2)) (= (str.len w_2) 2))) :rule string_decompose :premises (h1) :args (true))"#: false,
            }
            "Switched skolems in the conclusion" {
                r#"(assume h1 (>= (str.len (str.++ "d" "c")) 1))
                   (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
                   (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
                   (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_2 w_1)) (= (str.len w_1) 1))) :rule string_decompose :premises (h1) :args (false))"#: false,
            }
            "" {}
            "Premise is not of the form (>= (str.len t) n)" {
                r#"(assume h1 (< (str.len (str.++ "d" "c")) 1))
                   (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
                   (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
                   (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_1 w_2)) (= (str.len w_2) 1))) :rule string_decompose :premises (h1) :args (true))"#: false,
                r#"(assume h1 (>= (str.to_code (str.++ "d" "c")) 1))
                   (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
                   (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
                   (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_1 w_2)) (= (str.len w_2) 1))) :rule string_decompose :premises (h1) :args (true))"#: false,
            }
            "Conclusion term is not of the form (and (= t x) (= (str.len y) 0))" {
                r#"(assume h1 (>= (str.len (str.++ a (str.++ "b" c))) 0))
                   (define-fun w_1 () String (str.substr (str.++ a (str.++ "b" c)) 0 0))
                   (define-fun w_2 () String (str.substr (str.++ a (str.++ "b" c)) 0 (- (str.len (str.++ a (str.++ "b" c))) 0)))
                   (step t1 (cl (or (= (str.++ a (str.++ "b" c)) (str.++ w_1 w_2)) (= (str.len w_1) 0))) :rule string_decompose :premises (h1) :args (false))"#: false,
                r#"(assume h1 (>= (str.len (str.++ a (str.++ "b" c))) 0))
                   (define-fun w_1 () String (str.substr (str.++ a (str.++ "b" c)) 0 0))
                   (define-fun w_2 () String (str.substr (str.++ a (str.++ "b" c)) 0 (- (str.len (str.++ a (str.++ "b" c))) 0)))
                   (step t1 (cl (and (not (= (str.++ a (str.++ "b" c)) (str.++ w_1 w_2))) (= (str.len w_1) 0))) :rule string_decompose :premises (h1) :args (false))"#: false,
                r#"(assume h1 (>= (str.len (str.++ a (str.++ "b" c))) 0))
                   (define-fun w_1 () String (str.substr (str.++ a (str.++ "b" c)) 0 0))
                   (define-fun w_2 () String (str.substr (str.++ a (str.++ "b" c)) 0 (- (str.len (str.++ a (str.++ "b" c))) 0)))
                   (step t1 (cl (and (= (str.++ a (str.++ "b" c)) (str.++ w_1 w_2)) (not (= (str.len w_1) 0)))) :rule string_decompose :premises (h1) :args (false))"#: false,
                r#"(assume h1 (>= (str.len (str.++ a (str.++ "b" c))) 0))
                   (define-fun w_1 () String (str.substr (str.++ a (str.++ "b" c)) 0 0))
                   (define-fun w_2 () String (str.substr (str.++ a (str.++ "b" c)) 0 (- (str.len (str.++ a (str.++ "b" c))) 0)))
                   (step t1 (cl (and (= (str.++ a (str.++ "b" c)) (str.++ w_1 w_2)) (= (str.to_code w_1) 0))) :rule string_decompose :premises (h1) :args (false))"#: false,
            }
            "Inverted argument value" {
                r#"(assume h1 (>= (str.len "ab") 2))
                   (define-fun w_1 () String (str.substr "ab" 0 2))
                   (define-fun w_2 () String (str.substr "ab" 2 (- (str.len "ab") 2)))
                   (step t1 (cl (and (= "ab" (str.++ w_1 w_2)) (= (str.len w_1) 2))) :rule string_decompose :premises (h1) :args (true))"#: false,
                r#"(assume h1 (>= (str.len (str.++ "d" "c")) 1))
                   (define-fun w_1 () String (str.substr (str.++ "d" "c") 0 1))
                   (define-fun w_2 () String (str.substr (str.++ "d" "c") 1 (- (str.len (str.++ "d" "c")) 1)))
                   (step t1 (cl (and (= (str.++ "d" "c") (str.++ w_1 w_2)) (= (str.len w_2) 1))) :rule string_decompose :premises (h1) :args (false))"#: false,
            }
        }
    }

    #[test]
    fn string_length_pos() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
            ",
            "Simple working examples" {
                r#"(step t1 (cl (or (and (= (str.len "ab") 0) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: true,
                r#"(step t1 (cl (or (and (= (str.len (str.++ "a" (str.++ b "c"))) 0) (= (str.++ "a" (str.++ b "c")) "")) (> (str.len (str.++ "a" (str.++ b "c"))) 0))) :rule string_length_pos :args ((str.++ "a" (str.++ b "c"))))"#: true,
                r#"(step t1 (cl (or (and (= (str.len a) 0) (= a "")) (> (str.len a) 0))) :rule string_length_pos :args (a))"#: true,
                r#"(step t1 (cl (or (and (= (str.len (str.++ a "b")) 0) (= (str.++ a "b") "")) (> (str.len (str.++ a "b")) 0))) :rule string_length_pos :args ((str.++ a "b")))"#: true,
            }
            "Argument term \"t\" and the conclusion term \"t\" is not the same" {
                r#"(step t1 (cl (or (and (= (str.len (str.++ a "b")) 0) (= (str.++ a "b") "")) (> (str.len (str.++ a "b")) 0))) :rule string_length_pos :args ((str.++ "a" b)))"#: false,
                r#"(step t1 (cl (or (and (= (str.len (str.++ "a" b)) 0) (= (str.++ "a" b) "")) (> (str.len (str.++ "a" b)) 0))) :rule string_length_pos :args ((str.++ a "b")))"#: false,
                r#"(step t1 (cl (or (and (= (str.len (str.++ "b" a)) 0) (= (str.++ a "b") "")) (> (str.len (str.++ a "b")) 0))) :rule string_length_pos :args ((str.++ a "b")))"#: false,
                r#"(step t1 (cl (or (and (= (str.len (str.++ a "b")) 0) (= a "")) (> (str.len (str.++ a "b")) 0))) :rule string_length_pos :args ((str.++ a "b")))"#: false,
                r#"(step t1 (cl (or (and (= (str.len (str.++ a "b")) 0) (= (str.++ a "b") "")) (> (str.len (str.++ b d)) 0))) :rule string_length_pos :args ((str.++ a "b")))"#: false,
            }
            "Conclusion is not of the form (or (and (= (str.len t) 0) (= t \"\")) (> (str.len t) 0))" {
                r#"(step t1 (cl (and (and (= (str.len "ab") 0) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
                r#"(step t1 (cl (or (or (= (str.len "ab") 0) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
                r#"(step t1 (cl (or (and (not (= (str.len "ab") 0)) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
                r#"(step t1 (cl (or (and (= (str.to_code "ab") 0) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
                r#"(step t1 (cl (or (and (= (str.len "ab") 1) (= "ab" "")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
                r#"(step t1 (cl (or (and (= (str.len "ab") 0) (not (= "ab" ""))) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
                r#"(step t1 (cl (or (and (= (str.len "ab") 0) (= "ab" "a")) (> (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
                r#"(step t1 (cl (or (and (= (str.len "ab") 0) (= "ab" "")) (< (str.len "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
                r#"(step t1 (cl (or (and (= (str.len "ab") 0) (= "ab" "")) (> (str.to_code "ab") 0))) :rule string_length_pos :args ("ab"))"#: false,
                r#"(step t1 (cl (or (and (= (str.len "ab") 0) (= "ab" "")) (> (str.len "ab") 1))) :rule string_length_pos :args ("ab"))"#: false,
            }
        }
    }

    #[test]
    fn string_length_non_empty() {
        test_cases! {
            definitions = "
                (declare-fun a () String)
                (declare-fun b () String)
                (declare-fun c () String)
                (declare-fun d () String)
            ",
            "Simple working examples" {
                r#"(assume h1 (not (= "ab" "")))
                   (step t1 (cl (not (= (str.len "ab") 0))) :rule string_length_non_empty :premises (h1))"#: true,
                r#"(assume h1 (not (= (str.++ "a" (str.++ "b" "c")) "")))
                   (step t1 (cl (not (= (str.len (str.++ "a" (str.++ "b" "c"))) 0))) :rule string_length_non_empty :premises (h1))"#: true,
                r#"(assume h1 (not (= d "")))
                   (step t1 (cl (not (= (str.len d) 0))) :rule string_length_non_empty :premises (h1))"#: true,
                r#"(assume h1 (not (= (str.++ b c) "")))
                   (step t1 (cl (not (= (str.len (str.++ b c)) 0))) :rule string_length_non_empty :premises (h1))"#: true,
            }
            "Premise term is not an inequality of the form (not (= t \"\"))" {
                r#"(assume h1 (= (str.++ "a" (str.++ "b" "c")) ""))
                   (step t1 (cl (not (= (str.len (str.++ "a" (str.++ "b" "c"))) 0))) :rule string_length_non_empty :premises (h1))"#: false,
                r#"(assume h1 (not (= (str.++ "a" (str.++ "b" "c")) "ab")))
                   (step t1 (cl (not (= (str.len (str.++ "a" (str.++ "b" "c"))) 0))) :rule string_length_non_empty :premises (h1))"#: false,
                r#"(assume h1 (not (= (str.++ "a" (str.++ "b" "c")) a)))
                   (step t1 (cl (not (= (str.len (str.++ "a" (str.++ "b" "c"))) 0))) :rule string_length_non_empty :premises (h1))"#: false,
                r#"(assume h1 (not (= (str.++ "a" (str.++ "b" "c")) (str.++ a b))))
                   (step t1 (cl (not (= (str.len (str.++ "a" (str.++ "b" "c"))) 0))) :rule string_length_non_empty :premises (h1))"#: false,
            }
            "Shared term \"t\" between the premise and the conclusion is not the same" {
                r#"(assume h1 (not (= (str.++ b c) "")))
                   (step t1 (cl (not (= (str.len (str.++ c b)) 0))) :rule string_length_non_empty :premises (h1))"#: false,
                r#"(assume h1 (not (= (str.++ b c) "")))
                   (step t1 (cl (not (= (str.len (str.++ "b" "c")) 0))) :rule string_length_non_empty :premises (h1))"#: false,
                r#"(assume h1 (not (= (str.++ "b" c) "")))
                   (step t1 (cl (not (= (str.len (str.++ b c)) 0))) :rule string_length_non_empty :premises (h1))"#: false,
            }
            "Conclusion term is not an inequality of the form (not (= (str.len t) 0))" {
                r#"(assume h1 (not (= "ab" "")))
                   (step t1 (cl (= (str.len "ab") 0)) :rule string_length_non_empty :premises (h1))"#: false,
                r#"(assume h1 (not (= "ab" "")))
                   (step t1 (cl (not (= (str.to_code "ab") 0))) :rule string_length_non_empty :premises (h1))"#: false,
                r#"(assume h1 (not (= "ab" "")))
                   (step t1 (cl (not (> (str.len "ab") 0))) :rule string_length_non_empty :premises (h1))"#: false,
                r#"(assume h1 (not (= "ab" "")))
                   (step t1 (cl (not (= (str.len "ab") 1))) :rule string_length_non_empty :premises (h1))"#: false,
            }
        }
    }
}
