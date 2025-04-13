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

#[derive(Copy, Clone, ValueEnum, Debug)]
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

    /// ic3 sort by topology instead of activity
    #[arg(long = "ic3-topo-sort", default_value_t = false)]
    pub topo_sort: bool,

    /// ic3 reverse sort order
    #[arg(long = "ic3-reverse-sort", default_value_t = false)]
    pub reverse_sort: bool,

    /// ic3 use hybrid sort strategy (combine topology and activity)
    #[arg(long = "ic3-hybrid-sort", default_value_t = false)]
    pub hybrid_sort: bool,
    
    /// initial topology weight for hybrid sort (0.0-1.0)
    #[arg(long = "ic3-hybrid-topo-weight", default_value_t = 0.7)]
    pub hybrid_topo_weight: f64,
    
    /// frame factor for hybrid sort that controls how quickly topo weight decreases with frame
    #[arg(long = "ic3-hybrid-frame-factor", default_value_t = 0.1)]
    pub hybrid_frame_factor: f64,

    /// use flip rate data for sorting
    #[arg(long = "ic3-flip-rate-sort", default_value_t = false)]
    pub flip_rate_sort: bool,

    /// path to the flip rate JSON file
    #[arg(long = "ic3-flip-rate-file")]
    pub flip_rate_file: Option<PathBuf>,

    /// prioritize high flip rate variables first
    #[arg(long = "ic3-high-flip-rate-first", default_value_t = false)]
    pub high_flip_rate_first: bool,

    /// Calculate flip rates directly using FFI (no need for external JSON file)
    #[arg(long = "ic3-calculate-flip-rates", default_value_t = false)]
    pub calculate_flip_rates: bool,

    /// Number of simulation vectors for flip rate calculation
    #[arg(long = "ic3-flip-rate-vectors", default_value_t = 1000)]
    pub flip_rate_vectors: u32,

    /// Number of random seeds for flip rate calculation
    #[arg(long = "ic3-flip-rate-seeds", default_value_t = 1)]
    pub flip_rate_seeds: u32,

    /// Only calculate and print flip rates, then exit (requires --ic3-calculate-flip-rates)
    #[arg(long = "ic3-only-flip-rates", default_value_t = false)]
    pub only_flip_rates: bool,

    /// Enable adaptive ordering with multi-armed bandit algorithm
    #[arg(long = "ic3-adaptive-ordering", default_value_t = false)]
    pub adaptive_ordering: bool,
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
