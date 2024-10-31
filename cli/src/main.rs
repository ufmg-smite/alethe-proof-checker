mod benchmarking;
mod error;
mod logger;
mod path_args;

use carcara::{
    ast, benchmarking::OnlineBenchmarkResults, check, check_and_elaborate, check_parallel, checker,
    elaborator, generate_lia_smt_instances, parser, translation::printer::PrintProof,
};
use clap::{AppSettings, ArgEnum, Args, Parser, Subcommand};
use const_format::{formatcp, str_index};
use error::{CliError, CliResult};
use git_version::git_version;
use path_args::{get_instances_from_paths, infer_problem_path};
use std::{
    fs::File,
    io::{self, BufRead, IsTerminal},
    path::Path,
    sync::atomic,
};

// `git describe --all` will try to find any ref (including tags) that describes the current commit.
// This will include tags like `carcara-0.1.0`, that we create for github releases. To account for
// that, we pass the arguments `--exclude 'carcara-*'`, ignoring these tags.
const GIT_BRANCH_NAME: &str = git_version!(
    args = ["--all", "--exclude", "carcara-*"],
    fallback = "heads/none",
);
const GIT_COMMIT_HASH: &str = git_version!(fallback = "unknown");
const APP_VERSION: &str = env!("CARGO_PKG_VERSION");

const VERSION_STRING: &str = formatcp!(
    "{} [git {} {}]",
    APP_VERSION,
    // By default, `git describe` returns something like "heads/main". We ignore the "heads/" part
    // to get only the branch name
    str_index!(GIT_BRANCH_NAME, 6..),
    GIT_COMMIT_HASH,
);

#[derive(Parser)]
#[clap(
    name = "carcara",
    version = VERSION_STRING,
    setting = AppSettings::DeriveDisplayOrder
)]
struct Cli {
    #[clap(subcommand)]
    command: Command,

    /// Sets the maximum logging level.
    #[clap(arg_enum, global = true, long = "log", default_value_t = LogLevel::Warn)]
    log_level: LogLevel,

    /// Disables output coloring.
    #[clap(global = true, long)]
    no_color: bool,

    /// Don't use sharing when printing terms.
    #[clap(global = true, short = 'v', long)]
    no_print_with_sharing: bool,
}

#[derive(Subcommand)]
enum Command {
    /// Parses a proof file and prints it back.
    Parse(ParseCommandOptions),

    /// Checks a proof file.
    Check(CheckCommandOptions),

    /// Checks and elaborates a proof file.
    Elaborate(ElaborateCommandOptions),

    /// Checks a series of proof files and records performance statistics.
    Bench(BenchCommandOptions),

    /// Given a step, takes a slice of a proof consisting of all its transitive premises.
    Slice(SliceCommandOptions),

    /// Generates the equivalent SMT instance for every `lia_generic` step in a proof.
    GenerateLiaProblems(ParseCommandOptions),

    /// Translates an Alethe proof into Eunoia.
    Translate(TranslateCommandOptions),
}

#[derive(Args)]
struct Input {
    /// The proof file to be checked
    proof_file: String,

    /// The original problem file. If this argument is not present, it will be inferred from the
    /// proof file.
    problem_file: Option<String>,
}

#[derive(Args)]
struct StatsOptions {
    /// Enables the gathering of performance statistics
    #[clap(long)]
    stats: bool,
}

#[derive(Args)]
struct StackOptions {
    /// Defines the thread stack size for each check worker (does not include the main thread stack size, which should be set manually).
    #[clap(long, default_value = "0")]
    stack_size: usize,
}

#[derive(Args, Clone, Copy)]
struct ParsingOptions {
    /// Expand function definitions introduced by `define-fun`s in the SMT problem. If this flag is
    /// not present, they are instead interpreted as a function declaration and an `assert` that
    /// defines the function name to be equal to its body. Function definitions in the proof itself
    /// are always expanded.
    #[clap(long)]
    apply_function_defs: bool,

    /// Eliminates `let` bindings from terms when parsing.
    #[clap(long)]
    expand_let_bindings: bool,

    /// Enables `Int`/`Real` subtyping in the parser. This allows terms of sort `Int` to be passed
    /// to arithmetic operators that are expecting a term of sort `Real`.
    #[clap(long)]
    allow_int_real_subtyping: bool,

    /// Enables strict parsing.
    ///
    /// When this flag is enabled: unary `and`, `or` and `xor` terms are not allowed;
    #[clap(short, long = "strict-parsing")]
    strict: bool,
}

impl From<ParsingOptions> for parser::Config {
    fn from(val: ParsingOptions) -> Self {
        Self {
            apply_function_defs: val.apply_function_defs,
            expand_lets: val.expand_let_bindings,
            allow_int_real_subtyping: val.allow_int_real_subtyping,
            strict: val.strict,
        }
    }
}

#[derive(ArgEnum, Clone, Copy, PartialEq, Eq)]
enum CheckGranularity {
    Normal,
    Elaborated,
}

#[derive(Args, Clone)]
struct CheckingOptions {
    /// Allow steps with rules that are not known by the checker, and consider them as holes.
    #[clap(short, long)]
    ignore_unknown_rules: bool,

    // Note: the `--skip-unknown-rules` flag has been deprecated in favor of `--ignore-unknown-rules`
    #[clap(long, conflicts_with("ignore-unknown-rules"), hide = true)]
    skip_unknown_rules: bool,

    /// A set of extra rules to be allowed by the checker, and considered as holes.
    #[clap(long, multiple = true, conflicts_with = "ignore-unknown-rules")]
    allowed_rules: Option<Vec<String>>,

    /// Enforce restrictions on the granularity of the proof.
    ///
    /// If this is "normal", the proof is checked normally, with no extra restrictions. If this
    /// is "elaborated", the checker will expect the proof to have previously been elaborated by
    /// Carcara, and will enforce extra restrictions. In particular:
    /// - the implicit reordering of equalities is not allowed
    /// - the pivots for `resolution` steps must be given as arguments
    #[clap(arg_enum, long, default_value = "normal", verbatim_doc_comment)]
    check_granularity: CheckGranularity,
}

impl From<CheckingOptions> for checker::Config {
    fn from(val: CheckingOptions) -> Self {
        Self {
            elaborated: val.check_granularity == CheckGranularity::Elaborated,
            ignore_unknown_rules: val.ignore_unknown_rules,
            allowed_rules: val.allowed_rules.unwrap_or_default().into_iter().collect(),
        }
    }
}

#[derive(ArgEnum, Clone)]
enum ElaborationStep {
    Polyeq,
    LiaGeneric,
    Local,
    Uncrowd,
    Reordering,
    Hole,
}

#[derive(Args, Clone)]
struct ElaborationOptions {
    /// Elaborate `lia_generic` steps using the provided solver.
    #[clap(long)]
    lia_solver: Option<String>,

    /// The arguments to pass to the `lia_generic` solver. This should be a single string where
    /// multiple arguments are separated by spaces.
    #[clap(
        long,
        requires = "lia-solver",
        allow_hyphen_values = true,
        default_value = "--tlimit=10000 --lang=smt2 --proof-format-mode=alethe --proof-granularity=theory-rewrite --proof-alethe-res-pivots"
    )]
    lia_solver_args: String,

    /// When uncrowding resolutions steps, also reorder premises to further minimize the number of
    /// `contraction` steps added.
    #[clap(long)]
    uncrowd_rotate: bool,

    /// Elaborate `hole` steps using the provided solver.
    #[clap(long)]
    hole_solver: Option<String>,

    /// The arguments to pass to the `lia_generic` solver. This should be a single string where
    /// multiple arguments are separated by spaces.
    #[clap(
        long,
        requires = "hole-solver",
        allow_hyphen_values = true,
        default_value = "--disable-banner --disable-print-success --proof-prune --proof-merge --proof="
    )]
    hole_solver_args: String,

    /// The pipeline of elaboration steps to use.
    #[clap(
        arg_enum,
        long,
        multiple = true,
        default_values = &["polyeq", "lia-generic", "local", "uncrowd", "reordering", "hole"]
    )]
    pipeline: Vec<ElaborationStep>,
}

impl From<ElaborationOptions> for (elaborator::Config, Vec<elaborator::ElaborationStep>) {
    fn from(val: ElaborationOptions) -> Self {
        let pipeline: Vec<_> = val
            .pipeline
            .into_iter()
            .map(|s| match s {
                ElaborationStep::Polyeq => elaborator::ElaborationStep::Polyeq,
                ElaborationStep::LiaGeneric => elaborator::ElaborationStep::LiaGeneric,
                ElaborationStep::Local => elaborator::ElaborationStep::Local,
                ElaborationStep::Uncrowd => elaborator::ElaborationStep::Uncrowd,
                ElaborationStep::Reordering => elaborator::ElaborationStep::Reordering,
                ElaborationStep::Hole => elaborator::ElaborationStep::Hole,
            })
            .collect();
        let lia_options = val.lia_solver.map(|solver| elaborator::LiaGenericOptions {
            solver: solver.into(),
            arguments: val
                .lia_solver_args
                .split_whitespace()
                .map(Into::into)
                .collect(),
        });

        let hole_options = val.hole_solver.map(|solver| elaborator::HoleOptions {
            solver: solver.into(),
            arguments: val
                .hole_solver_args
                .split_whitespace()
                .map(Into::into)
                .collect(),
        });

        let config = elaborator::Config {
            lia_options,
            uncrowd_rotation: val.uncrowd_rotate,
            hole_options,
        };
        (config, pipeline)
    }
}

#[derive(Args)]
struct ParseCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,
}

#[derive(Args)]
struct CheckCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    checking: CheckingOptions,

    /// Defines the number of cores for proof checking.
    #[clap(short = 'u', long, required = false, default_value = "1", validator = |s: &str| -> Result<(), String> {
        if let Ok(n) = s.to_string().parse() as Result<u32, _> {
            if n < 1 {
                Err(format!("The threads number can't be {n}."))
            } else {
                Ok(())
            }
        } else {
            Err(String::from("Not a number."))
        }
    })]
    num_threads: usize,

    #[clap(flatten)]
    stats: StatsOptions,

    #[clap(flatten)]
    stack: StackOptions,
}

#[derive(Args)]
struct ElaborateCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    checking: CheckingOptions,

    #[clap(flatten)]
    elaboration: ElaborationOptions,

    #[clap(flatten)]
    stats: StatsOptions,
}

#[derive(Args)]
struct BenchCommandOptions {
    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(flatten)]
    checking: CheckingOptions,

    /// Also elaborate each proof in addition to parsing and checking.
    #[clap(long)]
    elaborate: bool,

    #[clap(flatten)]
    elaboration: ElaborationOptions,

    /// Number of times to run the benchmark for each file.
    #[clap(short, long, default_value_t = 1)]
    num_runs: usize,

    /// Number of jobs to run simultaneously when running the benchmark.
    #[clap(short = 'j', long, default_value_t = 1)]
    num_jobs: usize,

    /// Show benchmark results sorted by total time taken, instead of by average time taken.
    #[clap(short = 't', long)]
    sort_by_total: bool,

    /// Dump results to csv files instead of printing to screen.
    #[clap(long = "dump-to-csv")]
    dump_to_csv: bool,

    /// The proof files on which the benchmark will be run. If a directory is passed, the checker
    /// will recursively find all proof files in the directory. The problem files will be
    /// inferred from the proof files.
    files: Vec<String>,
}

#[derive(Args)]
struct SliceCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,

    #[clap(long)]
    from: String,

    #[clap(long, short = 'd')]
    max_distance: Option<usize>,

    // To make slice more convenient to use, we accept (and ignore!) some options from the `check`
    // subcommand
    #[clap(short, long, hide = true)]
    ignore_unknown_rules: bool,
    #[clap(long, hide = true)]
    lia_solver: Option<String>,
    #[clap(long, allow_hyphen_values = true, hide = true)]
    lia_solver_args: Option<String>,
    #[clap(long, hide = true)]
    hole_solver: Option<String>,
    #[clap(long, allow_hyphen_values = true, hide = true)]
    hole_solver_args: Option<String>,
}

#[derive(Args)]
struct TranslateCommandOptions {
    #[clap(flatten)]
    input: Input,

    #[clap(flatten)]
    parsing: ParsingOptions,
}

#[derive(ArgEnum, Clone)]
enum LogLevel {
    Off,
    Error,
    Warn,
    Info,
}

impl From<LogLevel> for log::LevelFilter {
    fn from(l: LogLevel) -> Self {
        match l {
            LogLevel::Off => Self::Off,
            LogLevel::Error => Self::Error,
            LogLevel::Warn => Self::Warn,
            LogLevel::Info => Self::Info,
        }
    }
}

fn main() {
    let cli = Cli::parse();
    let colors_enabled = !cli.no_color && std::io::stderr().is_terminal();

    ast::USE_SHARING_IN_TERM_DISPLAY.store(!cli.no_print_with_sharing, atomic::Ordering::Relaxed);

    logger::init(cli.log_level.into(), colors_enabled);

    if let Command::Check(CheckCommandOptions { checking, .. })
    | Command::Elaborate(ElaborateCommandOptions { checking, .. })
    | Command::Bench(BenchCommandOptions { checking, .. }) = &cli.command
    {
        if checking.skip_unknown_rules {
            log::warn!(
                "the `--skip-unknown-rules` option is deprecated, please use \
                `--ignore-unknown-rules` instead"
            )
        }
    }

    let result = match cli.command {
        Command::Parse(options) => parse_command(options).and_then(|(prelude, proof, mut pool)| {
            ast::print_proof(&mut pool, &prelude, &proof, !cli.no_print_with_sharing)?;
            Ok(())
        }),
        Command::Check(options) => {
            match check_command(options) {
                Ok(false) => println!("valid"),
                Ok(true) => println!("holey"),
                Err(e) => {
                    log::error!("{}", e);
                    println!("invalid");
                    std::process::exit(1);
                }
            }
            return;
        }
        Command::Elaborate(options) => {
            elaborate_command(options).and_then(|(res, prelude, proof, mut pool)| {
                if res {
                    println!("holey");
                } else {
                    println!("valid");
                }
                ast::print_proof(&mut pool, &prelude, &proof, !cli.no_print_with_sharing)?;
                Ok(())
            })
        }
        Command::Bench(options) => bench_command(options),
        Command::Slice(options) => slice_command(options).and_then(|(prelude, proof, mut pool)| {
            ast::print_proof(&mut pool, &prelude, &proof, !cli.no_print_with_sharing)?;
            Ok(())
        }),
        Command::GenerateLiaProblems(options) => {
            generate_lia_problems_command(options, !cli.no_print_with_sharing)
        }
        Command::Translate(options) => translate_command(options),
    };
    if let Err(e) = result {
        log::error!("{}", e);
        std::process::exit(1);
    }
}

fn get_instance(options: &Input) -> CliResult<(Box<dyn BufRead>, Box<dyn BufRead>)> {
    fn reader_from_path<P: AsRef<Path>>(path: P) -> CliResult<Box<dyn BufRead>> {
        Ok(Box::new(io::BufReader::new(File::open(path)?)))
    }

    match (options.problem_file.as_deref(), options.proof_file.as_str()) {
        (Some("-"), "-") | (None, "-") => Err(CliError::BothFilesStdin),
        (Some(problem), "-") => Ok((reader_from_path(problem)?, Box::new(io::stdin().lock()))),
        (Some("-"), proof) => Ok((Box::new(io::stdin().lock()), reader_from_path(proof)?)),
        (Some(problem), proof) => Ok((reader_from_path(problem)?, reader_from_path(proof)?)),
        (None, proof) => Ok((
            reader_from_path(infer_problem_path(proof)?)?,
            reader_from_path(proof)?,
        )),
    }
}

fn parse_command(
    options: ParseCommandOptions,
) -> CliResult<(ast::ProblemPrelude, ast::Proof, ast::PrimitivePool)> {
    let (problem, proof) = get_instance(&options.input)?;
    let result = parser::parse_instance(problem, proof, options.parsing.into())
        .map_err(carcara::Error::from)?;
    Ok(result)
}

fn check_command(options: CheckCommandOptions) -> CliResult<bool> {
    let (problem, proof) = get_instance(&options.input)?;
    let parser_config = options.parsing.into();
    let checker_config = options.checking.into();
    let collect_stats = options.stats.stats;
    if options.num_threads == 1 {
        check(problem, proof, parser_config, checker_config, collect_stats)
    } else {
        check_parallel(
            problem,
            proof,
            parser_config,
            checker_config,
            collect_stats,
            options.num_threads,
            options.stack.stack_size,
        )
    }
    .map_err(Into::into)
}

fn elaborate_command(
    options: ElaborateCommandOptions,
) -> CliResult<(bool, ast::ProblemPrelude, ast::Proof, ast::PrimitivePool)> {
    let (problem, proof) = get_instance(&options.input)?;

    let (elab_config, pipeline) = options.elaboration.into();
    check_and_elaborate(
        problem,
        proof,
        options.parsing.into(),
        options.checking.into(),
        elab_config,
        pipeline,
        options.stats.stats,
    )
    .map_err(CliError::CarcaraError)
}

fn bench_command(options: BenchCommandOptions) -> CliResult<()> {
    let instances = get_instances_from_paths(options.files.iter().map(|s| s.as_str()))?;
    if instances.is_empty() {
        log::warn!("no files passed");
        return Ok(());
    }

    log::info!(
        "running benchmark on {} files, doing {} runs each",
        instances.len(),
        options.num_runs
    );

    if options.dump_to_csv {
        benchmarking::run_csv_benchmark(
            &instances,
            options.num_runs,
            options.num_jobs,
            options.parsing.into(),
            options.checking.into(),
            options.elaborate.then(|| options.elaboration.into()),
            &mut File::create("runs.csv")?,
            &mut File::create("steps.csv")?,
        )?;
        return Ok(());
    }

    let results: OnlineBenchmarkResults = benchmarking::run_benchmark(
        &instances,
        options.num_runs,
        options.num_jobs,
        options.parsing.into(),
        options.checking.into(),
        options.elaborate.then(|| options.elaboration.into()),
    );
    if results.is_empty() {
        println!("no benchmark data collected");
        return Ok(());
    }

    if results.had_error {
        println!("invalid");
    } else if results.is_holey {
        println!("holey");
    } else {
        println!("valid");
    }
    results.print(options.sort_by_total);
    Ok(())
}

fn slice_command(
    options: SliceCommandOptions,
) -> CliResult<(ast::ProblemPrelude, ast::Proof, ast::PrimitivePool)> {
    let (problem, proof) = get_instance(&options.input)?;
    let (prelude, proof, pool) = parser::parse_instance(problem, proof, options.parsing.into())
        .map_err(carcara::Error::from)?;

    let node = ast::ProofNode::from_commands_with_root_id(proof.commands, &options.from)
        .ok_or_else(|| CliError::InvalidSliceId(options.from))?;
    let sliced = ast::Proof {
        commands: node.into_commands(),
        ..proof
    };

    Ok((prelude, sliced, pool))
}

fn generate_lia_problems_command(options: ParseCommandOptions, use_sharing: bool) -> CliResult<()> {
    use std::io::Write;

    let root_file_name = options.input.proof_file.clone();
    let (problem, proof) = get_instance(&options.input)?;

    let instances =
        generate_lia_smt_instances(problem, proof, options.parsing.into(), use_sharing)?;
    for (id, content) in instances {
        let file_name = format!("{}.{}.lia_smt2", root_file_name, id);
        let mut f = File::create(file_name)?;
        write!(f, "{}", content)?;
    }

    Ok(())
}

fn translate_command(options: TranslateCommandOptions) -> CliResult<()> {
    let (mut problem, mut proof) = get_instance(&options.input)?;
    let mut str_problem = String::new();
    let _ = problem.read_to_string(&mut str_problem);
    let mut str_proof = String::new();
    let _ = proof.read_to_string(&mut str_proof);

    let (alethe_problem, alethe_proof, _) = parser::parse_instance(
        str_problem.as_bytes(),
        str_proof.as_bytes(),
        options.parsing.into(),
    )
    .map_err(carcara::Error::from)?;

    let node = ast::ProofNode::from_commands(alethe_proof.commands);
    let mut translator = carcara::translation::eunoia::EunoiaTranslator::new();
    let eunoia_prelude = translator.translate_problem_prelude(&alethe_problem);
    let eunoia_proof = translator.translate(&node);

    let mut buf_proof = Vec::new();
    let s_exp_formatter_proof = carcara::translation::printer::SExpFormatter::new(&mut buf_proof);
    let mut printer_proof =
        carcara::translation::printer::EunoiaPrinter::new(s_exp_formatter_proof);

    printer_proof.write_proof(eunoia_proof).unwrap();

    let mut buf_prelude = Vec::new();
    let s_exp_formatter_prelude =
        carcara::translation::printer::SExpFormatter::new(&mut buf_prelude);
    let mut printer_prelude =
        carcara::translation::printer::EunoiaPrinter::new(s_exp_formatter_prelude);

    printer_prelude.write_proof(&eunoia_prelude).unwrap();

    // TODO: do not hard-code this in here
    // TODO: fix where to include these depedencies
    // Include Alethe's mechanization in Eunoia
    println!("(include \"../alethe_signature/Alethe.eo\")");
    println!("(include \"../alethe_signature/theory.eo\")");
    println!("(include \"../alethe_signature/programs.eo\")");
    println!("{}", std::str::from_utf8(&buf_prelude).unwrap());
    println!("{}", std::str::from_utf8(&buf_proof).unwrap());

    Ok(())
}
