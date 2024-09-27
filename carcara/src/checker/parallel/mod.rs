pub mod scheduler;

use super::{
    error::{CheckerError, SubproofError},
    rules::{Premise, RuleArgs, RuleResult},
    Config, ProofChecker,
};
use crate::benchmarking::{CollectResults, OnlineBenchmarkResults};
use crate::checker::CheckerStatistics;
use crate::{
    ast::{pool::advanced::*, *},
    CarcaraResult, Error,
};
use indexmap::IndexSet;
pub use scheduler::{Schedule, ScheduleIter, Scheduler};
use std::{
    ops::ControlFlow,
    sync::{atomic::AtomicBool, Arc},
    thread,
    time::{Duration, Instant},
};

pub struct ParallelProofChecker<'c> {
    pool: Arc<PrimitivePool>,
    config: Config,
    prelude: &'c ProblemPrelude,
    context: ContextStack,
    reached_empty_clause: bool,
    is_holey: bool,
    stack_size: usize,
}

impl<'c> ParallelProofChecker<'c> {
    pub fn new(
        pool: Arc<PrimitivePool>,
        config: Config,
        prelude: &'c ProblemPrelude,
        context_usage: &Vec<usize>,
        stack_size: usize,
    ) -> Self {
        ParallelProofChecker {
            pool,
            config,
            prelude,
            context: ContextStack::from_usage(context_usage),
            reached_empty_clause: false,
            is_holey: false,
            stack_size,
        }
    }

    /// Copies the proof checker and instantiate parallel fields to be shared between threads
    pub fn share(&self) -> Self {
        ParallelProofChecker {
            pool: self.pool.clone(),
            config: self.config.clone(),
            prelude: self.prelude,
            context: ContextStack::from_previous(&self.context),
            reached_empty_clause: false,
            is_holey: false,
            stack_size: self.stack_size,
        }
    }

    pub fn check(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        scheduler: &Scheduler,
    ) -> CarcaraResult<bool> {
        // Used to estimulate threads to abort prematurely (only happens when a
        // thread already found out an invalid step)
        let premature_abort = Arc::new(AtomicBool::new(false));
        let context_pool = ContextPool::from_global(&self.pool);
        //
        thread::scope(|s| {
            let threads: Vec<_> = scheduler
                .loads
                .iter()
                .enumerate()
                .map(|(i, schedule)| {
                    // Shares the self between threads
                    let mut local_self = self.share();
                    let local_pool = LocalPool::from_previous(&context_pool);
                    let should_abort = premature_abort.clone();

                    thread::Builder::new()
                        .name(format!("worker-{i}"))
                        .stack_size(self.stack_size)
                        .spawn_scoped(s, move || -> CarcaraResult<(bool, bool)> {
                            local_self.worker_thread_check(
                                problem,
                                proof,
                                schedule,
                                local_pool,
                                should_abort,
                                None::<&mut CheckerStatistics<OnlineBenchmarkResults>>,
                            )
                        })
                        .unwrap()
                })
                .collect();

            // Unify the results of all threads and generate the final result based on them
            let (mut reached, mut holey) = (false, false);
            let mut err: Result<_, Error> = Ok(());

            // Wait until the threads finish and merge the results and statistics
            threads
                .into_iter()
                .map(|t| t.join().unwrap())
                .try_for_each(|opt| {
                    match opt {
                        Ok((local_reached, local_holey)) => {
                            // Mask the result booleans
                            (reached, holey) = (reached | local_reached, holey | local_holey);
                            ControlFlow::Continue(())
                        }
                        Err(e) => {
                            err = Err(e);
                            ControlFlow::Break(())
                        }
                    }
                });

            // If an error happend
            err?;

            if reached {
                Ok(holey)
            } else {
                Err(Error::DoesNotReachEmptyClause)
            }
        })
    }

    pub fn check_with_stats<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        scheduler: &Scheduler,
        stats: &mut CheckerStatistics<CR>,
    ) -> CarcaraResult<bool> {
        // Used to estimulate threads to abort prematurely (only happens when a
        // thread already found out an invalid step)
        let premature_abort = Arc::new(AtomicBool::new(false));
        let context_pool = ContextPool::from_global(&self.pool);
        //
        thread::scope(|s| {
            let threads: Vec<_> = scheduler
                .loads
                .iter()
                .enumerate()
                .map(|(i, schedule)| {
                    let mut local_stats = CheckerStatistics {
                        file_name: "",
                        polyeq_time: Duration::ZERO,
                        assume_time: Duration::ZERO,
                        assume_core_time: Duration::ZERO,
                        results: CR::default(),
                    };
                    // Shares the proof checker between threads
                    let mut local_self = self.share();
                    let local_pool = LocalPool::from_previous(&context_pool);
                    let should_abort = premature_abort.clone();

                    thread::Builder::new()
                        .name(format!("worker-{i}"))
                        .stack_size(self.stack_size)
                        .spawn_scoped(
                            s,
                            move || -> CarcaraResult<(bool, bool, CheckerStatistics<CR>)> {
                                local_self
                                    .worker_thread_check(
                                        problem,
                                        proof,
                                        schedule,
                                        local_pool,
                                        should_abort,
                                        Some(&mut local_stats),
                                    )
                                    .map(|r| (r.0, r.1, local_stats))
                            },
                        )
                        .unwrap()
                })
                .collect();

            // Unify the results of all threads and generate the final result based on them
            let (mut reached, mut holey) = (false, false);
            let mut err: Result<_, Error> = Ok(());

            // Wait until the threads finish and merge the results and statistics
            threads
                .into_iter()
                .map(|t| t.join().unwrap())
                .for_each(|opt| {
                    match opt {
                        Ok((local_reached, local_holey, mut local_stats)) => {
                            // Combine the statistics
                            // Takes the external and local benchmark results to local variables and combine them
                            let main = std::mem::take(&mut stats.results);
                            let to_merge = std::mem::take(&mut local_stats.results);
                            stats.results = CR::combine(main, to_merge);

                            // Make sure other times are updated
                            stats.polyeq_time += local_stats.polyeq_time;
                            stats.assume_time += local_stats.assume_time;
                            stats.assume_core_time += local_stats.assume_core_time;

                            // Mask the result booleans
                            (reached, holey) = (reached | local_reached, holey | local_holey);
                        }
                        Err(e) => {
                            // Since we want the statistics of the whole run
                            // (even in a error case) we cannot abort at this
                            // point, since we can have more threads to be
                            // evaluated and their statistics colleted
                            err = Err(e);
                        }
                    }
                });

            // If an error happend
            err?;

            if reached {
                Ok(holey)
            } else {
                Err(Error::DoesNotReachEmptyClause)
            }
        })
    }

    fn worker_thread_check<CR: CollectResults + Send + Default>(
        &mut self,
        problem: &Problem,
        proof: &Proof,
        schedule: &Schedule,
        mut pool: LocalPool,
        should_abort: Arc<AtomicBool>,
        mut stats: Option<&mut CheckerStatistics<CR>>,
    ) -> CarcaraResult<(bool, bool)> {
        use std::sync::atomic::Ordering;

        let mut iter = schedule.iter(&proof.commands[..]);
        let mut last_depth = 0;

        while let Some(command) = iter.next() {
            // If there is any depth difference between the current and last step
            while (last_depth - iter.depth() as i64 > 0)
                || (last_depth - iter.depth() as i64 == 0
                    && matches!(command, ProofCommand::Subproof(_)))
            {
                // If this is the last command of a subproof, we have to pop off the subproof
                // commands of the stack. The parser already ensures that the last command
                // in a subproof is always a `step` command
                self.context.pop();
                last_depth -= 1;
            }
            last_depth = iter.depth() as i64;

            match command {
                ProofCommand::Step(step) => {
                    // If this step ends a subproof, it might need to implicitly reference the
                    // previous command in the subproof
                    let previous_command = if iter.is_end_step() {
                        let subproof = iter.current_subproof().unwrap();
                        let index = subproof.len() - 2;
                        subproof
                            .get(index)
                            .map(|command| Premise::new((iter.depth(), index), command))
                    } else {
                        None
                    };

                    self.check_step(step, previous_command, &iter, &mut pool, &mut stats)
                        .map_err(|e| {
                            // Signalize to other threads to stop the proof checking
                            should_abort.store(true, Ordering::Release);
                            Error::Checker {
                                inner: e,
                                rule: step.rule.clone(),
                                step: step.id.clone(),
                            }
                        })?;

                    if step.clause.is_empty() {
                        self.reached_empty_clause = true;
                    }
                }
                ProofCommand::Subproof(s) => {
                    let time = Instant::now();
                    let step_id = command.id();

                    self.context.push_with_id(&s.args, s.context_id);

                    if let Some(stats) = &mut stats {
                        // Collects statistics
                        let rule_name = match s.commands.last() {
                            Some(ProofCommand::Step(step)) => {
                                format!("anchor({})", &step.rule)
                            }
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
                        // Signalize to other threads to stop the proof checking
                        should_abort.store(true, Ordering::Release);
                        return Err(Error::Checker {
                            inner: CheckerError::Assume(term.clone()),
                            rule: "assume".into(),
                            step: id.clone(),
                        });
                    }
                }
            }
            // Verify if any of the other threads found an error and abort in case of positive
            if should_abort.load(Ordering::Acquire) {
                break;
            }
        }

        // Returns Ok(reached empty clause, isHoley)
        if self.reached_empty_clause {
            Ok((true, self.is_holey))
        } else {
            Ok((false, self.is_holey))
        }
    }

    fn check_assume<CR: CollectResults + Send + Default>(
        &mut self,
        id: &str,
        term: &Rc<Term>,
        premises: &IndexSet<Rc<Term>>,
        iter: &ScheduleIter,
        mut stats: &mut Option<&mut CheckerStatistics<CR>>,
    ) -> bool {
        let time = Instant::now();

        // Similarly to the single-threaded checker, we ignore `assume` commands that are inside
        // subproofs
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
        }

        if let Some(s) = stats {
            let time = time.elapsed();
            s.assume_time += time;
            s.assume_core_time += core_time;
            s.polyeq_time += polyeq_time;
            s.results
                .add_assume_measurement(s.file_name, id, false, time);
        }

        true
    }

    fn check_step<CR: CollectResults + Send + Default>(
        &mut self,
        step: &ProofStep,
        previous_command: Option<Premise>,
        iter: &ScheduleIter,
        pool: &mut LocalPool,
        stats: &mut Option<&mut CheckerStatistics<CR>>,
    ) -> RuleResult {
        let time = Instant::now();
        let mut polyeq_time = Duration::ZERO;

        if !step.discharge.is_empty() && step.rule != "subproof" {
            return Err(CheckerError::Subproof(SubproofError::DischargeInWrongRule));
        }

        let rule = match ProofChecker::get_rule(&step.rule, self.config.elaborated) {
            Some(r) => r,
            None if self.config.ignore_unknown_rules => {
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
            pool,
            context: &mut self.context,
            previous_command,
            discharge: &discharge,
            polyeq_time: &mut polyeq_time,
        };

        rule(rule_args)?;

        if iter.is_end_step() {
            let subproof = iter.current_subproof().unwrap();
            ProofChecker::check_discharge(subproof, iter.depth(), &step.discharge)?;
        }

        if let Some(s) = stats {
            let time = time.elapsed();
            s.results
                .add_step_measurement(s.file_name, &step.id, &step.rule, time);
            s.polyeq_time += polyeq_time;
        }
        Ok(())
    }
}
