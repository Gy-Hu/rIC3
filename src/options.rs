use clap::{Args, Parser, ValueEnum};
use shadow_rs::shadow;
use std::path::PathBuf;

shadow!(build);
/// rIC3 model checker
#[derive(Parser, Debug, Clone)]
#[command(
    version,
    about,
    after_help = "Copyright (C) 2023 - Present, Yuheng Su <gipsyh.icu@gmail.com>. All rights reserved."
)]
#[clap(long_version = build::CLAP_LONG_VERSION)]
pub struct Options {
    /// model checking engine
    #[arg(short, long, value_enum, default_value_t = Engine::Portfolio)]
    pub engine: Engine,

    /// model file in aiger format or in btor2 format.
    /// for btor model, the file name should be suffixed with .btor or .btor2
    pub model: PathBuf,

    /// certificate path
    pub certificate: Option<PathBuf>,

    /// certify with certifaiger
    #[arg(long, default_value_t = false)]
    pub certify: bool,

    /// print witness when model is unsafe
    #[arg(long, default_value_t = false)]
    pub witness: bool,
    
    /// Path where to dump inductive invariants (if verification is successful)
    /// This option implicitly enables dumping without needing to specify --ic3-dump-inv
    #[arg(long = "ic3-dump-inv-file", default_value = "inv.cnf")]
    pub ic3_dump_inv_file: String,
    
    /// Path to file containing clauses to load into IC3 (load before verification starts)
    #[arg(long = "ic3-load-inv", default_value = "")]
    pub ic3_load_inv_file: String,

    #[command(flatten)]
    pub ic3: IC3Options,

    #[command(flatten)]
    pub bmc: BMCOptions,

    #[command(flatten)]
    pub kind: KindOptions,

    #[command(flatten)]
    pub preprocess: PreprocessOptions,

    /// step length
    #[arg(long, default_value_t = 1, value_parser = clap::value_parser!(u32).range(1..))]
    pub step: u32,

    /// random seed
    #[arg(long, default_value_t = 0)]
    pub rseed: u64,

    /// verbose level
    #[arg(short, default_value_t = 1)]
    pub verbose: usize,

    /// interrupt statistic
    #[arg(long, default_value_t = false)]
    pub interrupt_statistic: bool,
}

#[derive(Copy, Clone, ValueEnum, Debug, PartialEq, Eq)]
pub enum Engine {
    /// ic3
    IC3,
    /// k-induction
    Kind,
    /// bmc
    BMC,
    /// portfolio
    Portfolio,
}

#[derive(Args, Clone, Debug)]
pub struct IC3Options {
    /// dynamic generalization
    #[arg(long = "ic3-dynamic", default_value_t = false)]
    pub dynamic: bool,

    /// ic3 counterexample to generalization
    #[arg(long = "ic3-ctg", default_value_t = false)]
    pub ctg: bool,

    /// max number of ctg
    #[arg(long = "ic3-ctg-max", default_value_t = 3)]
    pub ctg_max: usize,

    /// ctg limit
    #[arg(long = "ic3-ctg-limit", default_value_t = 1)]
    pub ctg_limit: usize,

    /// ic3 counterexample to propagation
    #[arg(long = "ic3-ctp", default_value_t = false)]
    pub ctp: bool,

    /// ic3 with internal signals (FMCAD'21)
    #[arg(long = "ic3-inn", default_value_t = false)]
    pub inn: bool,

    /// ic3 with abstract constrains
    #[arg(long = "ic3-abs-cst", default_value_t = false)]
    pub abs_cst: bool,

    /// ic3 without predicate property
    #[arg(long = "ic3-no-pred-prop", default_value_t = false)]
    pub no_pred_prop: bool,
    
    /// dump inductive invariants to a file
    /// (note: this can also be enabled by specifying --ic3-dump-inv-file)
    #[arg(long = "ic3-dump-inv", default_value_t = false)]
    pub dump_inv: bool,
    
    /// maximum clause size for filtering when side loading
    #[arg(long = "ic3-max-clause-size", default_value_t = 10)]
    pub max_clause_size: usize,

    /// enable CTI sampling - P /\ T /\ !P' pattern discovery
    #[arg(long = "ic3-cti-sample", default_value_t = false)]
    pub cti_sample: bool,

    /// CTI sample count - number of samples to collect
    #[arg(long = "ic3-cti-sample-count", default_value_t = 100)]
    pub cti_sample_count: usize,

    /// CTI sample output file
    #[arg(long = "ic3-cti-sample-file", default_value = "cti_samples.txt")]
    pub cti_sample_file: String,

    /// Reduce CTI samples (ternary simulation-like reduction)
    #[arg(long = "ic3-cti-reduce", default_value_t = true)]
    pub cti_reduce: bool,
}

#[derive(Args, Clone, Debug)]
pub struct BMCOptions {
    /// bmc single step time limit
    #[arg(long = "bmc-time-limit")]
    pub time_limit: Option<u64>,
    /// use kissat solver, otherwise cadical
    #[arg(long = "bmc-kissat", default_value_t = false)]
    pub bmc_kissat: bool,
    /// Bound to check up until k when bmc (default 0 means no bound)
    #[arg(long = "bmc-max-k", short = 'k', default_value_t = usize::MAX)]
    pub bmc_max_k: usize,
}

#[derive(Args, Clone, Debug)]
pub struct KindOptions {
    /// no bmc check in kind
    #[arg(long = "kind-no-bmc", default_value_t = false)]
    pub no_bmc: bool,
    /// use kissat solver, otherwise cadical
    #[arg(long = "kind-kissat", default_value_t = false)]
    pub kind_kissat: bool,
    /// simple path constraint
    #[arg(long = "kind-simple-path", default_value_t = false)]
    pub simple_path: bool,
}

#[derive(Args, Clone, Debug)]
pub struct PreprocessOptions {
    /// sec preprocess
    #[arg(long = "sec", default_value_t = false)]
    pub sec: bool,

    /// disable abc preprocess
    #[arg(long = "no-abc", default_value_t = false)]
    pub no_abc: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options::parse_from([""])
    }
}
