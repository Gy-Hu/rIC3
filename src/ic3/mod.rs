use crate::{
    Engine,
    gipsat::{Solver, SolverStatistic},
    options::Options,
    transys::{Transys, TransysCtx, TransysIf, unroll::TransysUnroll},
    witness_encode,
};
use activity::Activity;
use aig::{Aig, AigEdge};
use frame::{Frame, Frames};
use giputils::{grc::Grc, hash::GHashMap};
use logic_form::{Lemma, LitVec, Var};
use mic::{DropVarParameter, MicType};
use nalgebra::{DMatrix, DVector};
use proofoblig::{ProofObligation, ProofObligationQueue};
use rand::{SeedableRng, rngs::StdRng};
use satif::Satif;
use statistic::Statistic;
use std::time::Instant;

mod activity;
mod frame;
mod mic;
mod proofoblig;
mod solver;
mod statistic;
mod verify;

// --- Contextual MAB Definitions ---
#[derive(Clone, Copy, Debug)]
struct MicParamsConfig {
    limit: usize,
    max: usize,
    level: usize,
}

// Define the fixed configurations for arms 1..N
const FIXED_MIC_PARAM_CONFIGS: [MicParamsConfig; 5] = [
    MicParamsConfig { limit: 0, max: 0, level: 0 },    // Minimal MIC
    MicParamsConfig { limit: 1, max: 2, level: 1 },    // Basic CTG
    MicParamsConfig { limit: 1, max: 5, level: 1 },    // Medium CTG
    MicParamsConfig { limit: 5, max: 5, level: 1 },    // Strong CTG Limit
    MicParamsConfig { limit: 10, max: 5, level: 1 },   // V. Strong CTG Limit
];
const NUM_FIXED_MIC_CONFIG_ARMS: usize = FIXED_MIC_PARAM_CONFIGS.len();
const CTX_HEURISTIC_ARM_INDEX: usize = 0; // Arm 0 is always the dynamic heuristic
const CTX_TOTAL_MIC_ARMS: usize = 1 + NUM_FIXED_MIC_CONFIG_ARMS;

// Context dimension (features + bias)
const CONTEXT_DIM: usize = 5; // [frame, lemma_len, act, depth, bias]
type MatrixDD = DMatrix<f64>;
type VectorD = DVector<f64>;

pub struct IC3 {
    options: Options,
    ts: Grc<TransysCtx>,
    solvers: Vec<Solver>,
    lift: Solver,
    bad_ts: Grc<TransysCtx>,
    bad_solver: cadical::Solver,
    bad_lift: Solver,
    bad_input: GHashMap<Var, Var>,
    frame: Frames,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
    pre_lemmas: Vec<LitVec>,
    abs_cst: LitVec,
    bmc_solver: Option<(Box<dyn satif::Satif>, TransysUnroll<TransysCtx>)>,

    auxiliary_var: Vec<Var>,
    rng: StdRng,
    
    // Contextual MAB (LinUCB) State
    ctx_mab_A: Vec<MatrixDD>,         // One matrix per arm
    ctx_mab_A_inv: Vec<MatrixDD>,     // Store inverse for efficiency
    ctx_mab_b: Vec<VectorD>,          // One vector per arm
    ctx_mab_theta: Vec<VectorD>,      // Store theta per arm
    ctx_mab_arm_pulls: Vec<usize>,    // Count of pulls per arm for statistics
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
    }

    // Feature normalization helper
    fn normalize_feature(val: f64, min_val: f64, max_val: f64) -> f64 {
        if max_val <= min_val { return 0.5; } // Avoid division by zero
        ((val - min_val) / (max_val - min_val)).max(0.0).min(1.0) // Clamp to [0, 1]
    }

    // Extract context vector from proof obligation
    fn get_context_vector(&self, po: &ProofObligation) -> VectorD {
        // Define expected ranges (these need tuning based on observation!)
        const MAX_EXPECTED_FRAME: f64 = 100.0;
        const MAX_EXPECTED_LEN: f64 = 50.0;
        const MAX_EXPECTED_ACT: f64 = 100.0;
        const MAX_EXPECTED_DEPTH: f64 = 50.0;

        let frame_feat = Self::normalize_feature(po.frame as f64, 0.0, MAX_EXPECTED_FRAME);
        let len_feat = Self::normalize_feature(po.lemma.len() as f64, 1.0, MAX_EXPECTED_LEN);
        let act_feat = Self::normalize_feature(po.act, 0.0, MAX_EXPECTED_ACT);
        let depth_feat = Self::normalize_feature(po.depth as f64, 0.0, MAX_EXPECTED_DEPTH);
        let bias = 1.0;

        // Ensure this matches CONTEXT_DIM
        VectorD::from_column_slice(&[frame_feat, len_feat, act_feat, depth_feat, bias])
    }

    fn extend(&mut self) {
        if !self.options.ic3.no_pred_prop {
            self.bad_solver = cadical::Solver::new();
            self.bad_ts.load_trans(&mut self.bad_solver, true);
        }
        let mut solver = Solver::new(self.options.clone(), Some(self.frame.len()), &self.ts);
        for v in self.auxiliary_var.iter() {
            solver.add_domain(*v, true);
        }
        self.solvers.push(solver);
        self.frame.push(Frame::new());
        if self.level() == 0 {
            for init in self.ts.init.clone() {
                self.add_lemma(0, LitVec::from([!init]), true, None);
            }
            let mut init = LitVec::new();
            for l in self.ts.latchs.iter() {
                if self.ts.init_map[*l].is_none() {
                    if let Some(v) = self.solvers[0].sat_value(l.lit()) {
                        let l = l.lit().not_if(!v);
                        init.push(l);
                    }
                }
            }
            for i in init {
                self.ts.add_init(i.var(), Some(i.polarity()));
            }
        } else if self.level() == 1 {
            for cls in self.pre_lemmas.clone().iter() {
                self.add_lemma(1, !cls.clone(), true, None);
            }
        }
    }

    fn push_lemma(&mut self, frame: usize, mut cube: LitVec) -> (usize, LitVec) {
        let start = Instant::now();
        for i in frame + 1..=self.level() {
            if self.solvers[i - 1].inductive(&cube, true) {
                cube = self.solvers[i - 1].inductive_core();
            } else {
                return (i, cube);
            }
        }
        self.statistic.block_push_time += start.elapsed();
        (self.level() + 1, cube)
    }

    fn generalize(&mut self, mut po: ProofObligation) -> bool {
        if self.options.ic3.inn && self.ts.cube_subsume_init(&po.lemma) {
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.lemma.cube().clone(), false, Some(po));
        }
        
        let mic_core = self.solvers[po.frame - 1].inductive_core();
        let chosen_arm_idx: usize;
        let mic_type_to_use: MicType;

        if self.options.ic3.enable_ctx_mab {
            // --- Contextual MAB Integration ---
            let context_vec = self.get_context_vector(&po);
            chosen_arm_idx = self.choose_mic_arm_linucb(&context_vec);

            if chosen_arm_idx == CTX_HEURISTIC_ARM_INDEX {
                // MAB chose the heuristic arm - calculate parameters now
                let heuristic_params = self.calculate_heuristic_mic_params(&po);
                mic_type_to_use = MicType::DropVar(heuristic_params);
            } else {
                // MAB chose a fixed arm
                let fixed_arm_index = chosen_arm_idx - 1; // Adjust index for the FIXED_MIC_PARAM_CONFIGS array
                let fixed_config = FIXED_MIC_PARAM_CONFIGS[fixed_arm_index];
                mic_type_to_use = MicType::DropVar(DropVarParameter::new(
                    fixed_config.limit, fixed_config.max, fixed_config.level));
            }
        } else if self.options.ic3.dynamic {
            // --- Use Original Dynamic Logic ---
            mic_type_to_use = if let Some(mut n) = po.next.as_ref() {
                let mut act = n.act;
                for _ in 0..2 {
                    if let Some(nn) = n.next.as_ref() {
                        n = nn;
                        act = act.max(n.act);
                    } else {
                        break;
                    }
                }
                const CTG_THRESHOLD: f64 = 10.0;
                const EXCTG_THRESHOLD: f64 = 40.0;
                let (limit, max, level) = match act {
                    EXCTG_THRESHOLD.. => {
                        let limit = ((act - EXCTG_THRESHOLD).powf(0.3) * 2.0 + 5.0).round()
                            as usize;
                        (limit, 5, 1)
                    }
                    CTG_THRESHOLD..EXCTG_THRESHOLD => {
                        let max = (act - CTG_THRESHOLD) as usize / 10 + 2;
                        (1, max, 1)
                    }
                    ..CTG_THRESHOLD => (0, 0, 0),
                    _ => panic!(),
                };
                let p = DropVarParameter::new(limit, max, level);
                MicType::DropVar(p)
            } else {
                MicType::DropVar(Default::default())
            };
            chosen_arm_idx = CTX_HEURISTIC_ARM_INDEX; // For statistics/logging
        } else {
            // --- Use Static Baseline Logic ---
            mic_type_to_use = MicType::from_options(&self.options);
            chosen_arm_idx = CTX_HEURISTIC_ARM_INDEX; // For statistics/logging
        }
        
        // Apply MIC with the chosen strategy
        let mic = self.mic(po.frame, mic_core, &[], mic_type_to_use);
        
        // Push the lemma and track the result
        let (pushed_frame, final_mic) = self.push_lemma(po.frame, mic);
        
        if self.options.ic3.enable_ctx_mab {
            // --- MAB Reward Calculation & Update ---
            let context_vec = self.get_context_vector(&po);
            let reward = (pushed_frame as f64) - (po.frame as f64); // Pushing Power reward
            // Update LinUCB stats for the chosen arm
            self.update_linucb(chosen_arm_idx, &context_vec, reward);
        }
        
        self.statistic.avg_po_cube_len += po.lemma.len();
        po.push_to(pushed_frame);
        self.add_obligation(po.clone());
        
        if self.add_lemma(pushed_frame - 1, final_mic.clone(), false, Some(po)) {
            return true;
        }
        false
    }

    fn block(&mut self) -> Option<bool> {
        while let Some(mut po) = self.obligations.pop(self.level()) {
            if po.removed {
                continue;
            }
            if self.ts.cube_subsume_init(&po.lemma) {
                if self.options.ic3.abs_cst {
                    self.add_obligation(po.clone());
                    if let Some(c) = self.check_witness_by_bmc(po.clone()) {
                        for c in c {
                            assert!(!self.abs_cst.contains(&c));
                            self.abs_cst.push(c);
                        }
                        if self.options.verbose > 1 {
                            println!("abs cst len: {}", self.abs_cst.len(),);
                        }
                        self.obligations.clear();
                        for f in self.frame.iter_mut() {
                            for l in f.iter_mut() {
                                l.po = None;
                            }
                        }
                        continue;
                    } else {
                        return Some(false);
                    }
                } else if self.options.ic3.inn && po.frame > 0 {
                    assert!(!self.solvers[0].solve(&po.lemma, vec![]));
                } else {
                    self.add_obligation(po.clone());
                    assert!(po.frame == 0);
                    return Some(false);
                }
            }
            if let Some((bf, _)) = self.frame.trivial_contained(po.frame, &po.lemma) {
                po.push_to(bf + 1);
                self.add_obligation(po);
                continue;
            }
            if self.options.verbose > 2 {
                self.frame.statistic();
            }
            po.bump_act();
            let blocked_start = Instant::now();
            let blocked = self.blocked_with_ordered(po.frame, &po.lemma, false, false);
            self.statistic.block_blocked_time += blocked_start.elapsed();
            if blocked {
                if self.generalize(po) {
                    return None;
                }
            } else {
                let (model, inputs) = self.get_pred(po.frame, true);
                self.add_obligation(ProofObligation::new(
                    po.frame - 1,
                    Lemma::new(model),
                    vec![inputs],
                    po.depth + 1,
                    Some(po.clone()),
                ));
                self.add_obligation(po);
            }
        }
        Some(true)
    }

    #[allow(unused)]
    fn trivial_block_rec(
        &mut self,
        frame: usize,
        lemma: Lemma,
        constraint: &[LitVec],
        limit: &mut usize,
        parameter: DropVarParameter,
    ) -> bool {
        if frame == 0 {
            return false;
        }
        if self.ts.cube_subsume_init(&lemma) {
            return false;
        }
        if *limit == 0 {
            return false;
        }
        *limit -= 1;
        loop {
            if self.blocked_with_ordered_with_constrain(
                frame,
                &lemma,
                false,
                true,
                constraint.to_vec(),
            ) {
                let mut mic = self.solvers[frame - 1].inductive_core();
                mic = self.mic(frame, mic, constraint, MicType::DropVar(parameter));
                let (frame, mic) = self.push_lemma(frame, mic);
                self.add_lemma(frame - 1, mic, false, None);
                return true;
            } else {
                if *limit == 0 {
                    return false;
                }
                let model = Lemma::new(self.get_pred(frame, false).0);
                if !self.trivial_block_rec(frame - 1, model, constraint, limit, parameter) {
                    return false;
                }
            }
        }
    }

    fn trivial_block(
        &mut self,
        frame: usize,
        lemma: Lemma,
        constraint: &[LitVec],
        parameter: DropVarParameter,
    ) -> bool {
        let mut limit = parameter.limit;
        self.trivial_block_rec(frame, lemma, constraint, &mut limit, parameter)
    }

    fn propagate(&mut self, from: Option<usize>) -> bool {
        let from = from.unwrap_or(self.frame.early).max(1);
        for frame_idx in from..self.level() {
            self.frame[frame_idx].sort_by_key(|x| x.len());
            let frame = self.frame[frame_idx].clone();
            for mut lemma in frame {
                if self.frame[frame_idx].iter().all(|l| l.ne(&lemma)) {
                    continue;
                }
                for ctp in 0..3 {
                    if self.blocked_with_ordered(frame_idx + 1, &lemma, false, false) {
                        let core = if self.options.ic3.inn && self.ts.cube_subsume_init(&lemma) {
                            lemma.cube().clone()
                        } else {
                            self.solvers[frame_idx].inductive_core()
                        };
                        if let Some(po) = &mut lemma.po {
                            if po.frame < frame_idx + 2 && self.obligations.remove(po) {
                                po.push_to(frame_idx + 2);
                                self.obligations.add(po.clone());
                            }
                        }
                        self.add_lemma(frame_idx + 1, core, true, lemma.po);
                        self.statistic.ctp.statistic(ctp > 0);
                        break;
                    }
                    if !self.options.ic3.ctp {
                        break;
                    }
                    let (ctp, _) = self.get_pred(frame_idx + 1, false);
                    if !self.ts.cube_subsume_init(&ctp)
                        && self.solvers[frame_idx - 1].inductive(&ctp, true)
                    {
                        let core = self.solvers[frame_idx - 1].inductive_core();
                        let mic =
                            self.mic(frame_idx, core, &[], MicType::DropVar(Default::default()));
                        if self.add_lemma(frame_idx, mic, false, None) {
                            return true;
                        }
                    } else {
                        break;
                    }
                }
            }
            if self.frame[frame_idx].is_empty() {
                return true;
            }
        }
        self.frame.early = self.level();
        false
    }

    fn base(&mut self) -> bool {
        if !self.options.ic3.no_pred_prop {
            let mut base = cadical::Solver::new();
            self.ts.load_trans(&mut base, true);
            self.ts.load_init(&mut base);
            let bad = self.ts.bad;
            if base.solve(&bad.cube()) {
                let (bad, inputs) = self.lift.get_pred(&base, &bad.cube(), true);
                self.add_obligation(ProofObligation::new(
                    0,
                    Lemma::new(bad),
                    vec![inputs],
                    0,
                    None,
                ));
                return false;
            }
            self.ts.constraints.push(!bad);
            self.lift = Solver::new(self.options.clone(), None, &self.ts);
        }
        self.extend();
        true
    }

    // LinUCB arm selection function
    fn choose_mic_arm_linucb(&mut self, context: &VectorD) -> usize {
        let alpha = self.options.ic3.mic_ctx_mab_alpha;
        let mut best_arm = 0;
        let mut max_score = -f64::INFINITY;

        for arm_idx in 0..CTX_TOTAL_MIC_ARMS {
            let a_inv = &self.ctx_mab_A_inv[arm_idx];
            let theta = &self.ctx_mab_theta[arm_idx]; // Use stored theta
            
            // Calculate UCB score: theta^T * x + alpha * sqrt(x^T * A_inv * x)
            let p_a = theta.transpose() * context; // Predicted reward (scalar)
            let x_a_inv_x = context.transpose() * a_inv * context;
            let uncertainty = x_a_inv_x[(0, 0)]; // Extract scalar from 1x1 matrix
            let ucb_score = p_a[0] + alpha * uncertainty.max(0.0).sqrt(); // Ensure non-negative under sqrt
            
            if self.options.verbose > 5 {
                println!("Arm {}: p_a={:.3}, uncertainty={:.3}, score={:.3}", 
                    arm_idx, p_a[0], uncertainty.sqrt(), ucb_score);
            }

            if ucb_score > max_score {
                max_score = ucb_score;
                best_arm = arm_idx;
            }
        }
        
        // Count arm pulls for statistics
        self.ctx_mab_arm_pulls[best_arm] += 1;
        
        if self.options.verbose > 4 {
            if best_arm == CTX_HEURISTIC_ARM_INDEX {
                println!("LinUCB chose Heuristic Arm ({} pulls)", self.ctx_mab_arm_pulls[CTX_HEURISTIC_ARM_INDEX]);
            } else {
                let config_idx = best_arm - 1;
                println!("LinUCB chose Fixed Arm {} ({} pulls): limit={}, max={}, level={}", 
                    config_idx + 1, 
                    self.ctx_mab_arm_pulls[best_arm],
                    FIXED_MIC_PARAM_CONFIGS[config_idx].limit,
                    FIXED_MIC_PARAM_CONFIGS[config_idx].max,
                    FIXED_MIC_PARAM_CONFIGS[config_idx].level);
            }
        }
        
        best_arm
    }

    // LinUCB update function
    fn update_linucb(&mut self, arm_idx: usize, context: &VectorD, reward: f64) {
        // Update A and b for the chosen arm
        let outer_product = context * context.transpose();
        self.ctx_mab_A[arm_idx] = &self.ctx_mab_A[arm_idx] + &outer_product;
        
        // Update b: b = b + r * x
        self.ctx_mab_b[arm_idx] = &self.ctx_mab_b[arm_idx] + context * reward;
        
        // Recompute A_inv and theta for the updated arm
        if let Some(inv) = self.ctx_mab_A[arm_idx].clone().try_inverse() {
            self.ctx_mab_A_inv[arm_idx] = inv;
            self.ctx_mab_theta[arm_idx] = &self.ctx_mab_A_inv[arm_idx] * &self.ctx_mab_b[arm_idx];
        } else {
            // Handle error - matrix became non-invertible
            if self.options.verbose > 0 {
                eprintln!("Warning: Matrix A for arm {} became non-invertible.", arm_idx);
            }
            // Reset this arm to identity matrix
            self.ctx_mab_A[arm_idx] = MatrixDD::identity(CONTEXT_DIM, CONTEXT_DIM);
            self.ctx_mab_A_inv[arm_idx] = MatrixDD::identity(CONTEXT_DIM, CONTEXT_DIM);
            self.ctx_mab_b[arm_idx] = VectorD::zeros(CONTEXT_DIM);
            self.ctx_mab_theta[arm_idx] = VectorD::zeros(CONTEXT_DIM);
        }
        
        if self.options.verbose > 4 {
            println!("  Arm {} got reward {:.2}", arm_idx, reward);
        }
    }

    // Calculate heuristic MIC parameters based on PO activity
    fn calculate_heuristic_mic_params(&self, po: &ProofObligation) -> DropVarParameter {
        // Extract activity-based calculation from the original dynamic code
        if let Some(mut n) = po.next.as_ref() {
            let mut act = n.act;
            for _ in 0..2 {
                if let Some(nn) = n.next.as_ref() {
                    n = nn;
                    act = act.max(n.act);
                } else {
                    break;
                }
            }
            const CTG_THRESHOLD: f64 = 10.0;
            const EXCTG_THRESHOLD: f64 = 40.0;
            
            match act {
                EXCTG_THRESHOLD.. => {
                    let limit = ((act - EXCTG_THRESHOLD).powf(0.3) * 2.0 + 5.0).round() as usize;
                    DropVarParameter::new(limit, 5, 1)
                }
                CTG_THRESHOLD..EXCTG_THRESHOLD => {
                    let max = (act - CTG_THRESHOLD) as usize / 10 + 2;
                    DropVarParameter::new(1, max, 1)
                }
                ..CTG_THRESHOLD => DropVarParameter::new(0, 0, 0),
                _ => panic!(), // Should never happen
            }
        } else {
            DropVarParameter::default()
        }
    }
}

impl IC3 {
    pub fn new(mut options: Options, mut ts: Transys, pre_lemmas: Vec<LitVec>) -> Self {
        ts.unique_prime();
        ts.simplify();
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll();
        if options.ic3.inn {
            options.ic3.no_pred_prop = true;
            ts = uts.interal_signals();
        }
        let mut bad_input = GHashMap::new();
        for &l in ts.input.iter() {
            bad_input.insert(uts.var_next(l, 1), l);
        }
        let mut bad_ts = uts.compile();
        bad_ts.constraint.push(!ts.bad);
        let ts = Grc::new(ts.ctx());
        let bad_ts = Grc::new(bad_ts.ctx());
        let statistic = Statistic::new(options.model.to_str().unwrap());
        let activity = Activity::new(&ts);
        let frame = Frames::new(&ts);
        let lift = Solver::new(options.clone(), None, &ts);
        let bad_lift = Solver::new(options.clone(), None, &bad_ts);
        let abs_cst = if options.ic3.abs_cst {
            LitVec::new()
        } else {
            ts.constraints.clone()
        };
        let rng = StdRng::seed_from_u64(options.rseed);
        Self {
            options,
            ts,
            activity,
            solvers: Vec::new(),
            bad_ts,
            bad_solver: cadical::Solver::new(),
            bad_lift,
            bad_input,
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            frame,
            abs_cst,
            pre_lemmas,
            auxiliary_var: Vec::new(),
            bmc_solver: None,
            rng,
            ctx_mab_A: vec![MatrixDD::identity(CONTEXT_DIM, CONTEXT_DIM); CTX_TOTAL_MIC_ARMS],
            ctx_mab_A_inv: vec![MatrixDD::identity(CONTEXT_DIM, CONTEXT_DIM); CTX_TOTAL_MIC_ARMS],
            ctx_mab_b: vec![VectorD::zeros(CONTEXT_DIM); CTX_TOTAL_MIC_ARMS],
            ctx_mab_theta: vec![VectorD::zeros(CONTEXT_DIM); CTX_TOTAL_MIC_ARMS],
            ctx_mab_arm_pulls: vec![0; CTX_TOTAL_MIC_ARMS],
        }
    }
}

impl Engine for IC3 {
    fn check(&mut self) -> Option<bool> {
        if !self.base() {
            return Some(false);
        }
        loop {
            let start = Instant::now();
            loop {
                match self.block() {
                    Some(false) => {
                        self.statistic.overall_block_time += start.elapsed();
                        return Some(false);
                    }
                    None => {
                        self.statistic.overall_block_time += start.elapsed();
                        self.verify();
                        return Some(true);
                    }
                    _ => (),
                }
                if let Some((bad, inputs)) = self.get_bad() {
                    let bad = Lemma::new(bad);
                    self.add_obligation(ProofObligation::new(self.level(), bad, inputs, 0, None))
                } else {
                    break;
                }
            }
            let blocked_time = start.elapsed();
            if self.options.verbose > 1 {
                self.frame.statistic();
                println!(
                    "[{}:{}] frame: {}, time: {:?}",
                    file!(),
                    line!(),
                    self.level(),
                    blocked_time,
                );
            }
            self.statistic.overall_block_time += blocked_time;
            self.extend();
            let start = Instant::now();
            let propagate = self.propagate(None);
            self.statistic.overall_propagate_time += start.elapsed();
            if propagate {
                self.verify();
                return Some(true);
            }
        }
    }

    fn certifaiger(&mut self, aig: &Aig) -> Aig {
        let invariants = self.frame.invariant();
        let invariants = invariants
            .iter()
            .map(|l| LitVec::from_iter(l.iter().map(|l| self.ts.restore(*l))));
        let mut certifaiger = aig.clone();
        let mut certifaiger_dnf = vec![];
        for cube in invariants {
            certifaiger_dnf
                .push(certifaiger.new_ands_node(cube.into_iter().map(AigEdge::from_lit)));
        }
        let invariants = certifaiger.new_ors_node(certifaiger_dnf);
        let constrains: Vec<AigEdge> = certifaiger
            .constraints
            .iter()
            .map(|e| !*e)
            .chain(certifaiger.bads.iter().copied())
            .collect();
        let constrains = certifaiger.new_ors_node(constrains);
        let invariants = certifaiger.new_or_node(invariants, constrains);
        certifaiger.bads.clear();
        certifaiger.outputs.clear();
        certifaiger.outputs.push(invariants);
        certifaiger
    }

    fn witness(&mut self, aig: &Aig) -> String {
        let mut res: Vec<LitVec> = vec![LitVec::new()];
        if let Some((bmc_solver, uts)) = self.bmc_solver.as_mut() {
            let mut wit = vec![LitVec::new()];
            for l in uts.ts.latchs.iter() {
                let l = l.lit();
                if let Some(v) = bmc_solver.sat_value(l) {
                    wit[0].push(uts.ts.restore(l.not_if(!v)));
                }
            }
            for k in 0..=uts.num_unroll {
                let mut w = LitVec::new();
                for l in uts.ts.inputs.iter() {
                    let l = l.lit();
                    let kl = uts.lit_next(l, k);
                    if let Some(v) = bmc_solver.sat_value(kl) {
                        w.push(uts.ts.restore(l.not_if(!v)));
                    }
                }
                wit.push(w);
            }
            return witness_encode(aig, &wit);
        }
        let b = self.obligations.peak().unwrap();
        assert!(b.frame == 0);
        for &l in b.lemma.iter() {
            if let Some(v) = self.solvers[0].sat_value(l) {
                res[0].push(self.ts.restore(l.not_if(!v)));
            }
        }
        let mut b = Some(b);
        while let Some(bad) = b {
            for i in bad.input.iter() {
                res.push(i.iter().map(|l| self.ts.restore(*l)).collect());
            }
            b = bad.next.clone();
        }
        witness_encode(aig, &res)
    }

    fn statistic(&mut self) {
        self.statistic.num_auxiliary_var = self.auxiliary_var.len();
        self.obligations.statistic();
        for f in self.frame.iter() {
            print!("{} ", f.len());
        }
        println!();
        
        // Print contextual MAB statistics if enabled
        if self.options.ic3.enable_ctx_mab {
            println!("\n--- Contextual MAB Statistics ---");
            println!("Arm pulls:");
            
            // Print heuristic arm stats
            println!("  Arm 0 (Heuristic): {} pulls", self.ctx_mab_arm_pulls[CTX_HEURISTIC_ARM_INDEX]);
            
            // Print fixed arm stats
            for i in 0..NUM_FIXED_MIC_CONFIG_ARMS {
                let arm_idx = i + 1;
                let config = FIXED_MIC_PARAM_CONFIGS[i];
                println!("  Arm {} (limit={}, max={}, level={}): {} pulls", 
                    arm_idx, config.limit, config.max, config.level, 
                    self.ctx_mab_arm_pulls[arm_idx]);
            }
            
            println!("----------------------------");
        }
        
        let mut statistic = SolverStatistic::default();
        for s in self.solvers.iter() {
            statistic += s.statistic;
        }
        println!("{:#?}", statistic);
        println!("{:#?}", self.statistic);
    }
}
