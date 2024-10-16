pub mod error;
mod parallel;
mod rules;

use crate::{
    ast::*,
    benchmarking::{CollectResults, OnlineBenchmarkResults},
    CarcaraResult, Error,
};
use error::{CheckerError, SubproofError};
use indexmap::IndexSet;
pub use parallel::{scheduler::Scheduler, ParallelProofChecker};
use rules::{Premise, Rule, RuleArgs, RuleResult};
use std::{
    collections::HashSet,
    fmt,
    time::{Duration, Instant},
};

#[derive(Clone)]
pub struct CheckerStatistics<'s, CR: CollectResults + Send + Default> {
    pub file_name: &'s str,
    pub polyeq_time: Duration,
    pub assume_time: Duration,

    // This is the time to compare the `assume` term with the `assert` that matches it. That is,
    // this excludes the time spent searching for the correct `assert` premise.
    pub assume_core_time: Duration,
    pub results: CR,
}

impl<CR: CollectResults + Send + Default> fmt::Debug for CheckerStatistics<'_, CR> {
    // Since `self.results` does not implement `Debug`, we can't just `#[derive(Debug)]` and instead
    // have to implement it manually, removing that field.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CheckerStatistics")
            .field("file_name", &self.file_name)
            .field("polyeq_time", &self.polyeq_time)
            .field("assume_time", &self.assume_time)
            .field("assume_core_time", &self.assume_core_time)
            .finish()
    }
}

#[derive(Debug, Default, Clone)]
pub struct Config {
    /// If `true`, the checker will assume that the proof is elaborated, and enforce extra
    /// restrictions when checking it.
    ///
    /// Currently, if enabled, the following rules are affected:
    /// - `assume` and `refl`: implicit reordering of equalities is not allowed
    /// - `resolution` and `th_resolution`: the pivots must be provided as arguments
    pub elaborated: bool,

    /// If `true`, the checker will skip any steps with rules that it does not recognize, and will
    /// consider them as holes. Normally, using an unknown rule is considered an error.
    pub ignore_unknown_rules: bool,

    /// A set of rule names that the checker will allow, considering them holes in the proof.
    pub allowed_rules: HashSet<String>,
}

impl Config {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn elaborated(mut self, value: bool) -> Self {
        self.elaborated = value;
        self
    }

    pub fn ignore_unknown_rules(mut self, value: bool) -> Self {
        self.ignore_unknown_rules = value;
        self
    }
}

pub struct ProofChecker<'c> {
    pool: &'c mut PrimitivePool,
    config: Config,
    context: ContextStack,
    reached_empty_clause: bool,
    is_holey: bool,
}

impl<'c> ProofChecker<'c> {
    pub fn new(pool: &'c mut PrimitivePool, config: Config) -> Self {
        ProofChecker {
            pool,
            config,
            context: ContextStack::new(),
            reached_empty_clause: false,
            is_holey: false,
        }
    }

    pub fn check(&mut self, problem: &Problem, proof: &Proof) -> CarcaraResult<bool> {
        self.check_impl(
            problem,
            proof,
            None::<&mut CheckerStatistics<OnlineBenchmarkResults>>,
        )
    }

    pub fn check_with_stats<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        stats: &mut CheckerStatistics<CR>,
    ) -> CarcaraResult<bool> {
        self.check_impl(problem, proof, Some(stats))
    }

    fn check_impl<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        mut stats: Option<&mut CheckerStatistics<CR>>,
    ) -> CarcaraResult<bool> {
        // Similarly to the parser, to avoid stack overflows in proofs with many nested subproofs,
        // we check the subproofs iteratively, instead of recursively
        let mut iter = proof.iter();
        while let Some(command) = iter.next() {
            match command {
                ProofCommand::Step(step) => {
                    let is_end_of_subproof = iter.is_end_step();

                    // If this step ends a subproof, it might need to implicitly reference the
                    // previous command in the subproof
                    let previous_command = if is_end_of_subproof {
                        let subproof = iter.current_subproof().unwrap();
                        let index = subproof.len() - 2;
                        subproof
                            .get(index)
                            .map(|command| Premise::new((iter.depth(), index), command))
                    } else {
                        None
                    };
                    self.check_step(step, previous_command, &iter, &mut stats)
                        .map_err(|e| Error::Checker {
                            inner: e,
                            rule: step.rule.clone(),
                            step: step.id.clone(),
                        })?;

                    // If this is the last command of a subproof, we have to pop the subproof
                    // commands off of the stack. The parser already ensures that the last command
                    // in a subproof is always a `step` command
                    if is_end_of_subproof {
                        self.context.pop();
                    }

                    if step.clause.is_empty() {
                        self.reached_empty_clause = true;
                    }
                }
                ProofCommand::Subproof(s) => {
                    let time = Instant::now();
                    let step_id = command.id();

                    self.context.push(&s.args);

                    if let Some(stats) = &mut stats {
                        let rule_name = match s.commands.last() {
                            Some(ProofCommand::Step(step)) => format!("anchor({})", &step.rule),
                            _ => "anchor".to_owned(),
                        };
                        stats.results.add_step_measurement(
                            stats.file_name,
                            step_id,
                            &rule_name,
                            time.elapsed(),
                        );
                    }
                }
                ProofCommand::Assume { id, term } => {
                    if !self.check_assume(id, term, &problem.premises, &iter, &mut stats) {
                        return Err(Error::Checker {
                            inner: CheckerError::Assume(term.clone()),
                            rule: "assume".into(),
                            step: id.clone(),
                        });
                    }
                }
            }
        }
        if self.reached_empty_clause {
            Ok(self.is_holey)
        } else {
            Err(Error::DoesNotReachEmptyClause)
        }
    }

    fn check_assume<'i, CR: CollectResults + Send + Default>(
        &mut self,
        id: &str,
        term: &Rc<Term>,
        premises: &IndexSet<Rc<Term>>,
        iter: &'i ProofIter<'i>,
        mut stats: &mut Option<&mut CheckerStatistics<CR>>,
    ) -> bool {
        let time = Instant::now();

        // Some subproofs contain `assume` commands inside them. These don't refer to the original
        // problem premises, but are instead local assumptions that are discharged by the subproof's
        // final step, so we ignore the `assume` command if it is inside a subproof.
        if iter.is_in_subproof() {
            return true;
        }

        if premises.contains(term) {
            if let Some(s) = stats {
                let time = time.elapsed();

                s.assume_time += time;
                s.results
                    .add_assume_measurement(s.file_name, id, true, time);
            }
            return true;
        }

        if self.config.elaborated {
            return false;
        }

        let mut found = false;
        let mut polyeq_time = Duration::ZERO;
        let mut core_time = Duration::ZERO;

        for p in premises {
            let mut this_polyeq_time = Duration::ZERO;

            let mut comp = Polyeq::new().mod_reordering(true).mod_nary(true);
            let result = comp.eq_with_time(term, p, &mut this_polyeq_time);
            let depth = comp.max_depth();

            polyeq_time += this_polyeq_time;

            if let Some(s) = &mut stats {
                s.results.add_polyeq_depth(depth);
            }
            if result {
                core_time = this_polyeq_time;
                found = true;
                break;
            }
        }
        if !found {
            return false;
        };

        if let Some(s) = &mut stats {
            let time = time.elapsed();

            s.assume_time += time;
            s.assume_core_time += core_time;
            s.polyeq_time += polyeq_time;
            s.results
                .add_assume_measurement(s.file_name, id, false, time);
        }

        true
    }

    fn check_step<'i, CR: CollectResults + Send + Default>(
        &mut self,
        step: &ProofStep,
        previous_command: Option<Premise>,
        iter: &'i ProofIter<'i>,
        stats: &mut Option<&mut CheckerStatistics<CR>>,
    ) -> RuleResult {
        let time = Instant::now();
        let mut polyeq_time = Duration::ZERO;

        if !step.discharge.is_empty() && step.rule != "subproof" {
            return Err(CheckerError::Subproof(SubproofError::DischargeInWrongRule));
        }

        let rule = match Self::get_rule(&step.rule, self.config.elaborated) {
            Some(r) => r,
            None if self.config.ignore_unknown_rules
                || self.config.allowed_rules.contains(&step.rule) =>
            {
                self.is_holey = true;
                return Ok(());
            }
            None => return Err(CheckerError::UnknownRule),
        };

        if step.rule == "hole" || step.rule == "lia_generic" {
            self.is_holey = true;
        }

        let premises: Vec<_> = step
            .premises
            .iter()
            .map(|&p| {
                let command = iter.get_premise(p);
                Premise::new(p, command)
            })
            .collect();
        let discharge: Vec<_> = step
            .discharge
            .iter()
            .map(|&i| iter.get_premise(i))
            .collect();

        let rule_args = RuleArgs {
            conclusion: &step.clause,
            premises: &premises,
            args: &step.args,
            pool: self.pool,
            context: &mut self.context,
            previous_command,
            discharge: &discharge,
            polyeq_time: &mut polyeq_time,
        };

        rule(rule_args)?;

        if iter.is_end_step() {
            let subproof = iter.current_subproof().unwrap();
            Self::check_discharge(subproof, iter.depth(), &step.discharge)?;
        }

        if let Some(s) = stats {
            let time = time.elapsed();

            s.results
                .add_step_measurement(s.file_name, &step.id, &step.rule, time);
            s.polyeq_time += polyeq_time;
        }
        Ok(())
    }

    fn check_discharge(
        subproof: &[ProofCommand],
        depth: usize,
        discharge: &[(usize, usize)],
    ) -> RuleResult {
        let discharge: IndexSet<_> = discharge.iter().collect();
        if let Some((_, not_discharged)) = subproof
            .iter()
            .enumerate()
            .find(|&(i, command)| command.is_assume() && !discharge.contains(&(depth, i)))
        {
            Err(CheckerError::Subproof(
                SubproofError::LocalAssumeNotDischarged(not_discharged.id().to_owned()),
            ))
        } else {
            Ok(())
        }
    }

    pub fn get_rule(rule_name: &str, elaborated: bool) -> Option<Rule> {
        use rules::*;

        Some(match rule_name {
            "true" => tautology::r#true,
            "false" => tautology::r#false,
            "not_not" => tautology::not_not,
            "and_pos" => tautology::and_pos,
            "and_neg" => tautology::and_neg,
            "or_pos" => tautology::or_pos,
            "or_neg" => tautology::or_neg,
            "xor_pos1" => tautology::xor_pos1,
            "xor_pos2" => tautology::xor_pos2,
            "xor_neg1" => tautology::xor_neg1,
            "xor_neg2" => tautology::xor_neg2,
            "implies_pos" => tautology::implies_pos,
            "implies_neg1" => tautology::implies_neg1,
            "implies_neg2" => tautology::implies_neg2,
            "equiv_pos1" => tautology::equiv_pos1,
            "equiv_pos2" => tautology::equiv_pos2,
            "equiv_neg1" => tautology::equiv_neg1,
            "equiv_neg2" => tautology::equiv_neg2,
            "ite_pos1" => tautology::ite_pos1,
            "ite_pos2" => tautology::ite_pos2,
            "ite_neg1" => tautology::ite_neg1,
            "ite_neg2" => tautology::ite_neg2,
            "eq_reflexive" => reflexivity::eq_reflexive,
            "eq_transitive" => transitivity::eq_transitive,
            "eq_congruent" => congruence::eq_congruent,
            "eq_congruent_pred" => congruence::eq_congruent_pred,
            "distinct_elim" => clausification::distinct_elim,
            "la_rw_eq" => linear_arithmetic::la_rw_eq,
            "la_generic" => linear_arithmetic::la_generic,
            "la_disequality" => linear_arithmetic::la_disequality,
            "la_totality" => linear_arithmetic::la_totality,
            "la_tautology" => linear_arithmetic::la_tautology,
            "forall_inst" => quantifier::forall_inst,
            "qnt_join" => quantifier::qnt_join,
            "qnt_rm_unused" => quantifier::qnt_rm_unused,
            "resolution" | "th_resolution" if elaborated => resolution::resolution_with_args,
            "resolution" | "th_resolution" => resolution::resolution,
            "refl" if elaborated => reflexivity::strict_refl,
            "refl" => reflexivity::refl,
            "trans" => transitivity::trans,
            "cong" => congruence::cong,
            "ho_cong" => congruence::ho_cong,
            "and" => clausification::and,
            "tautology" => resolution::tautology,
            "not_or" => clausification::not_or,
            "or" => clausification::or,
            "not_and" => clausification::not_and,
            "xor1" => clausification::xor1,
            "xor2" => clausification::xor2,
            "not_xor1" => clausification::not_xor1,
            "not_xor2" => clausification::not_xor2,
            "implies" => clausification::implies,
            "not_implies1" => clausification::not_implies1,
            "not_implies2" => clausification::not_implies2,
            "equiv1" => tautology::equiv1,
            "equiv2" => tautology::equiv2,
            "not_equiv1" => tautology::not_equiv1,
            "not_equiv2" => tautology::not_equiv2,
            "ite1" => tautology::ite1,
            "ite2" => tautology::ite2,
            "not_ite1" => tautology::not_ite1,
            "not_ite2" => tautology::not_ite2,
            "ite_intro" => tautology::ite_intro,
            "contraction" => resolution::contraction,
            "connective_def" => tautology::connective_def,
            "ite_simplify" => simplification::ite_simplify,
            "eq_simplify" => simplification::eq_simplify,
            "and_simplify" => simplification::and_simplify,
            "or_simplify" => simplification::or_simplify,
            "not_simplify" => simplification::not_simplify,
            "implies_simplify" => simplification::implies_simplify,
            "equiv_simplify" => simplification::equiv_simplify,
            "bool_simplify" => simplification::bool_simplify,
            "qnt_simplify" => simplification::qnt_simplify,
            "div_simplify" => simplification::div_simplify,
            "prod_simplify" => simplification::prod_simplify,
            // Despite being separate rules in the specification, proofs generated by veriT don't
            // differentiate between `unary_minus_simplify` and `minus_simplify`. To account for
            // that, `simplification::minus_simplify` implements both rules in the same function.
            "unary_minus_simplify" | "minus_simplify" => simplification::minus_simplify,
            "sum_simplify" => simplification::sum_simplify,
            "comp_simplify" => simplification::comp_simplify,
            "nary_elim" => clausification::nary_elim,
            "ac_simp" => simplification::ac_simp,
            "bfun_elim" => clausification::bfun_elim,
            "bind" => subproof::bind,
            "qnt_cnf" => quantifier::qnt_cnf,
            "subproof" => subproof::subproof,
            "let" => subproof::r#let,
            "onepoint" => subproof::onepoint,
            "sko_ex" => subproof::sko_ex,
            "sko_forall" => subproof::sko_forall,
            "reordering" => extras::reordering,
            "symm" => extras::symm,
            "not_symm" => extras::not_symm,
            "eq_symmetric" => extras::eq_symmetric,
            "weakening" => extras::weakening,
            "bind_let" => extras::bind_let,
            "la_mult_pos" => extras::la_mult_pos,
            "la_mult_neg" => extras::la_mult_neg,
            "mod_simplify" => extras::mod_simplify,
            "bitblast_extract" => bitvectors::extract,
            "bitblast_bvadd" => bitvectors::add,
            "bitblast_ult" => bitvectors::ult,

            "concat_eq" => strings::concat_eq,
            "concat_unify" => strings::concat_unify,
            "concat_conflict" => strings::concat_conflict,
            "concat_csplit_prefix" => strings::concat_csplit_prefix,
            "concat_csplit_suffix" => strings::concat_csplit_suffix,
            "concat_split_prefix" => strings::concat_split_prefix,
            "concat_split_suffix" => strings::concat_split_suffix,
            "concat_lprop_prefix" => strings::concat_lprop_prefix,
            "concat_lprop_suffix" => strings::concat_lprop_suffix,
            "concat_cprop_prefix" => strings::concat_cprop_prefix,
            "concat_cprop_suffix" => strings::concat_cprop_suffix,

            "string_decompose" => strings::string_decompose,
            "string_length_pos" => strings::string_length_pos,
            "string_length_non_empty" => strings::string_length_non_empty,

            "re_inter" => strings::re_inter,
            "re_unfold_neg" => strings::re_unfold_neg,
            "re_unfold_neg_concat_fixed_prefix" => strings::re_unfold_neg_concat_fixed_prefix,
            "re_unfold_neg_concat_fixed_suffix" => strings::re_unfold_neg_concat_fixed_suffix,

            // Special rules that always check as valid, and are used to indicate holes in the
            // proof.
            "hole" => |_| Ok(()),
            "lia_generic" => |_| {
                log::warn!("encountered \"lia_generic\" rule, ignoring");
                Ok(())
            },

            // The Alethe specification does not yet describe how this more strict version of the
            // resolution rule will be called. Until that is decided and added to the specification,
            // we define a new specialized rule that calls it
            "strict_resolution" => resolution::strict_resolution,

            _ => return None,
        })
    }
}
