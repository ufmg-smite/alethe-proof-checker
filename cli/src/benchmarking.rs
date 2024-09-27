use carcara::{
    ast,
    benchmarking::{CollectResults, CsvBenchmarkResults, RunMeasurement},
    checker, elaborator, parser,
};
use crossbeam_queue::ArrayQueue;
use std::{
    fs::File,
    io::{self, BufReader},
    path::{Path, PathBuf},
    thread,
    time::{Duration, Instant},
};

#[derive(Debug, Clone, Copy)]
struct JobDescriptor<'a> {
    problem_file: &'a Path,
    proof_file: &'a Path,
    run_index: usize,
}

fn run_job<T: CollectResults + Default + Send>(
    results: &mut T,
    job: JobDescriptor,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: Option<(elaborator::Config, Vec<elaborator::ElaborationStep>)>,
) -> Result<bool, carcara::Error> {
    let proof_file_name = job.proof_file.to_str().unwrap();
    let mut checker_stats = checker::CheckerStatistics {
        file_name: proof_file_name,
        polyeq_time: Duration::ZERO,
        assume_time: Duration::ZERO,
        assume_core_time: Duration::ZERO,
        results: std::mem::take(results),
    };

    let total = Instant::now();

    let parsing = Instant::now();
    let (problem, proof, mut pool) = parser::parse_instance(
        BufReader::new(File::open(job.problem_file)?),
        BufReader::new(File::open(job.proof_file)?),
        parser_config,
    )?;
    let parsing = parsing.elapsed();

    let mut checker = checker::ProofChecker::new(&mut pool, checker_config);

    let checking = Instant::now();

    let checking_result = checker.check_with_stats(&problem, &proof, &mut checker_stats);
    let checking = checking.elapsed();

    let (elaboration, pipeline_durations) = if let Some((config, pipeline)) = elaborator_config {
        let elaboration = Instant::now();
        let node = ast::ProofNode::from_commands(proof.commands);
        let (elaborated, pipeline_durations) =
            elaborator::Elaborator::new(&mut pool, &problem, config)
                .elaborate_with_stats(&node, pipeline);
        elaborated.into_commands();
        (elaboration.elapsed(), pipeline_durations)
    } else {
        (Duration::ZERO, Vec::new())
    };

    let total = total.elapsed();

    checker_stats.results.add_run_measurement(
        &(proof_file_name.to_string(), job.run_index),
        RunMeasurement {
            parsing,
            checking,
            elaboration,
            scheduling: Duration::ZERO,
            total,
            polyeq: checker_stats.polyeq_time,
            assume: checker_stats.assume_time,
            assume_core: checker_stats.assume_core_time,
            elaboration_pipeline: pipeline_durations,
        },
    );
    *results = checker_stats.results;
    checking_result
}

fn worker_thread<T: CollectResults + Default + Send>(
    jobs_queue: &ArrayQueue<JobDescriptor>,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: Option<(elaborator::Config, Vec<elaborator::ElaborationStep>)>,
) -> T {
    let mut results = T::default();

    while let Some(job) = jobs_queue.pop() {
        let result = run_job(
            &mut results,
            job,
            parser_config,
            checker_config.clone(),
            elaborator_config.clone(),
        );
        match result {
            Ok(true) => results.register_holey(),
            Err(e) => {
                log::error!("encountered error in file '{}'", job.proof_file.display());
                results.register_error(&e);
            }
            _ => (),
        }
    }

    results
}

pub fn run_benchmark<T: CollectResults + Default + Send>(
    instances: &[(PathBuf, PathBuf)],
    num_runs: usize,
    num_jobs: usize,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: Option<(elaborator::Config, Vec<elaborator::ElaborationStep>)>,
) -> T {
    const STACK_SIZE: usize = 128 * 1024 * 1024;

    let jobs_queue = ArrayQueue::new(instances.len() * num_runs);
    for run_index in 0..num_runs {
        for (problem, proof) in instances {
            let job = JobDescriptor {
                problem_file: problem,
                proof_file: proof,
                run_index,
            };
            jobs_queue.push(job).unwrap();
        }
    }

    thread::scope(|s| {
        let jobs_queue = &jobs_queue; // So we don't try to move the queue into the thread closure

        // We of course need to `collect` here to ensure we spawn all threads before starting to
        // `join` them
        #[allow(clippy::needless_collect)]
        let workers: Vec<_> = (0..num_jobs)
            .map(|_| {
                let checker_config = checker_config.clone();
                let elaborator_config = elaborator_config.clone();
                thread::Builder::new()
                    .stack_size(STACK_SIZE)
                    .spawn_scoped(s, move || {
                        worker_thread(jobs_queue, parser_config, checker_config, elaborator_config)
                    })
                    .unwrap()
            })
            .collect();

        workers
            .into_iter()
            .map(|w| w.join().unwrap())
            .reduce(T::combine)
            .unwrap()
    })
}

#[allow(clippy::too_many_arguments)] // TODO: refactor this
pub fn run_csv_benchmark(
    instances: &[(PathBuf, PathBuf)],
    num_runs: usize,
    num_jobs: usize,
    parser_config: parser::Config,
    checker_config: checker::Config,
    elaborator_config: Option<(elaborator::Config, Vec<elaborator::ElaborationStep>)>,
    runs_dest: &mut dyn io::Write,
    steps_dest: &mut dyn io::Write,
) -> io::Result<()> {
    let result: CsvBenchmarkResults = run_benchmark(
        instances,
        num_runs,
        num_jobs,
        parser_config,
        checker_config,
        elaborator_config,
    );
    println!(
        "{} errors encountered during benchmark",
        result.num_errors()
    );
    if result.num_errors() > 0 {
        println!("invalid");
    } else if result.is_holey() {
        println!("holey");
    } else {
        println!("valid");
    }
    result.write_csv(runs_dest, steps_dest)
}
