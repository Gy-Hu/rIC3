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
use giputils::grc::Grc;
use logic_form::{Lemma, LitVec, Var};
use mic::{DropVarParameter, MicType};
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

pub struct IC3 {
    options: Options,
    ts: Grc<TransysCtx>,
    solvers: Vec<Solver>,
    lift: Solver,
    bad_ts: Grc<TransysCtx>,
    bad_solver: cadical::Solver,
    bad_lift: Solver,
    frame: Frames,
    obligations: ProofObligationQueue,
    activity: Activity,
    statistic: Statistic,
    pre_lemmas: Vec<LitVec>,
    abs_cst: LitVec,
    bmc_solver: Option<(Box<dyn satif::Satif>, TransysUnroll<TransysCtx>)>,

    auxiliary_var: Vec<Var>,
    rng: StdRng,
}

impl IC3 {
    #[inline]
    pub fn level(&self) -> usize {
        self.solvers.len() - 1
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

    fn generalize(&mut self, mut po: ProofObligation, mic_type: MicType) -> bool {
        if self.options.ic3.inn && self.ts.cube_subsume_init(&po.lemma) {
            po.frame += 1;
            self.add_obligation(po.clone());
            return self.add_lemma(po.frame - 1, po.lemma.cube().clone(), false, Some(po));
        }
        
        // 获取归纳核心
        let mut mic = self.solvers[po.frame - 1].inductive_core();
        
        // 记录是否找到了不变式
        let mut found_invariant = false;
        
        // 多子句生成
        let multi_clauses = self.options.ic3.multi_clauses;
        if multi_clauses > 1 {
            // 第一个子句使用默认排序
            mic = self.mic(po.frame, mic.clone(), &[], mic_type);
            let (frame, mic_first) = self.push_lemma(po.frame, mic);
            self.statistic.avg_po_cube_len += po.lemma.len();
            po.push_to(frame);
            self.add_obligation(po.clone());
            found_invariant |= self.add_lemma(frame - 1, mic_first.clone(), false, Some(po.clone()));
            
            // 生成额外的子句，使用不同的排序变体
            for i in 1..multi_clauses {
                // 重新获取归纳核心，避免被之前的处理修改
                let mut mic_next = self.solvers[po.frame - 1].inductive_core();
                
                // 使用带变体ID的mic函数，变体ID从1开始
                mic_next = self.mic_with_variant(po.frame, mic_next, &[], mic_type, i);
                
                // 推送子句
                let (frame_next, mic_next) = self.push_lemma(po.frame, mic_next);
                
                // 创建一个新的证明义务来记录此子句
                let po_new = po.clone();
                
                // 添加子句到相应的帧
                found_invariant |= self.add_lemma(frame_next - 1, mic_next.clone(), false, Some(po_new));
            }
            
            return found_invariant;
        } else {
            // 原始单子句处理
            mic = self.mic(po.frame, mic, &[], mic_type);
            let (frame, mic) = self.push_lemma(po.frame, mic);
            self.statistic.avg_po_cube_len += po.lemma.len();
            po.push_to(frame);
            self.add_obligation(po.clone());
            if self.add_lemma(frame - 1, mic.clone(), false, Some(po)) {
                return true;
            }
            return false;
        }
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
                let mic_type = if self.options.ic3.dynamic {
                    if let Some(mut n) = po.next.as_mut() {
                        let mut act = n.act;
                        for _ in 0..2 {
                            if let Some(nn) = n.next.as_mut() {
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
                    }
                } else {
                    MicType::from_options(&self.options)
                };
                if self.generalize(po, mic_type) {
                    return None;
                }
            } else {
                // Generate multiple predecessors if configured
                let num_samples = self.options.ic3.pred_samples;
                if num_samples > 1 {
                    let preds = self.get_multiple_preds(po.frame, true, num_samples);
                    if !preds.is_empty() {
                        // Add the original proof obligation back to the queue
                        self.add_obligation(po.clone());
                        
                        // Add all the sampled predecessors as new proof obligations
                        for (i, (model, inputs)) in preds.into_iter().enumerate() {
                            let next = if i == 0 { Some(po.clone()) } else { None };
                            self.add_obligation(ProofObligation::new(
                                po.frame - 1,
                                Lemma::new(model),
                                inputs,
                                po.depth + 1,
                                next,
                            ));
                        }
                    }
                } else {
                    // Original behavior for single predecessor
                    let (model, inputs) = self.get_pred(po.frame, true);
                    self.add_obligation(ProofObligation::new(
                        po.frame - 1,
                        Lemma::new(model),
                        inputs,
                        po.depth + 1,
                        Some(po.clone()),
                    ));
                    self.add_obligation(po);
                }
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
                
                // 如果启用了多子句生成，对于相同的归纳核心，尝试生成多个子句
                if self.options.ic3.multi_clauses > 1 {
                    // 获取第一个子句的帧和子句
                    let (frame_first, mic_first) = self.push_lemma(frame, mic.clone());
                    let mut found_invariant = self.add_lemma(frame_first - 1, mic_first, false, None);
                    
                    // 生成和添加额外的子句
                    for i in 1..self.options.ic3.multi_clauses {
                        // 重新获取归纳核心
                        let mut mic_next = self.solvers[frame - 1].inductive_core();
                        
                        // 使用不同的排序变体
                        mic_next = self.mic_with_variant(frame, mic_next, constraint, MicType::DropVar(parameter), i);
                        
                        // 推送子句
                        let (frame_next, mic_next) = self.push_lemma(frame, mic_next);
                        
                        // 添加子句
                        found_invariant |= self.add_lemma(frame_next - 1, mic_next, false, None);
                    }
                    
                    return found_invariant;
                } else {
                    // 原始单子句处理
                    let (frame, mic) = self.push_lemma(frame, mic);
                    self.add_lemma(frame - 1, mic, false, None);
                    return true;
                }
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
                        
                        // 如果启用了多子句生成
                        if self.options.ic3.multi_clauses > 1 {
                            // 生成第一个子句
                            let mic = self.mic(frame_idx, core.clone(), &[], MicType::DropVar(Default::default()));
                            let mut found_invariant = self.add_lemma(frame_idx, mic, false, None);
                            
                            // 生成额外的子句
                            for i in 1..self.options.ic3.multi_clauses {
                                // 重新获取归纳核心
                                let core_next = self.solvers[frame_idx - 1].inductive_core();
                                
                                // 使用不同的排序变体
                                let mic_next = self.mic_with_variant(
                                    frame_idx, 
                                    core_next, 
                                    &[], 
                                    MicType::DropVar(Default::default()),
                                    i
                                );
                                
                                // 添加子句
                                found_invariant |= self.add_lemma(frame_idx, mic_next, false, None);
                            }
                            
                            if found_invariant {
                                return true;
                            }
                        } else {
                            // 原始单子句处理
                            let mic = self.mic(frame_idx, core, &[], MicType::DropVar(Default::default()));
                            if self.add_lemma(frame_idx, mic, false, None) {
                                return true;
                            }
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
                self.add_obligation(ProofObligation::new(0, Lemma::new(bad), inputs, 0, None));
                return false;
            }
            self.ts.constraints.push(!bad);
            self.lift = Solver::new(self.options.clone(), None, &self.ts);
        }
        self.extend();
        true
    }
}

impl IC3 {
    pub fn new(mut options: Options, mut ts: Transys, pre_lemmas: Vec<LitVec>) -> Self {
        ts.simplify();
        let mut uts = TransysUnroll::new(&ts);
        uts.unroll();
        if options.ic3.inn {
            options.ic3.no_pred_prop = true;
            ts = uts.interal_signals();
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
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
            frame,
            abs_cst,
            pre_lemmas,
            auxiliary_var: Vec::new(),
            bmc_solver: None,
            rng,
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
        let invariants = certifaiger.new_ors_node(certifaiger_dnf.into_iter());
        let constrains: Vec<AigEdge> = certifaiger
            .constraints
            .iter()
            .map(|e| !*e)
            .chain(certifaiger.bads.iter().copied())
            .collect();
        let constrains = certifaiger.new_ors_node(constrains.into_iter());
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
        let mut assump = if let Some(next) = b.next.clone() {
            self.ts.lits_next(&next.lemma)
        } else {
            self.ts.bad.cube()
        };
        assump.extend_from_slice(&b.input);
        assert!(self.solvers[0].solve(&assump, vec![]));
        for l in self.ts.latchs.iter() {
            let l = l.lit();
            if let Some(v) = self.solvers[0].sat_value(l) {
                res[0].push(self.ts.restore(l.not_if(!v)));
            }
        }
        let mut b = Some(b);
        while let Some(bad) = b {
            res.push(bad.input.iter().map(|l| self.ts.restore(*l)).collect());
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
        let mut statistic = SolverStatistic::default();
        for s in self.solvers.iter() {
            statistic += s.statistic;
        }
        println!("{:#?}", statistic);
        
        // Add multi-predecessor sampling statistics
        if self.options.ic3.pred_samples > 1 {
            println!("Predecessor sampling statistics:");
            println!("  Total samples attempted: {}", self.statistic.total_pred_samples);
            println!("  Successful samples: {}", self.statistic.successful_pred_samples);
            if self.statistic.total_pred_samples > 0 {
                println!("  Success rate: {:.2}%", 
                    (self.statistic.successful_pred_samples as f64 / self.statistic.total_pred_samples as f64) * 100.0);
            }
        }
        
        println!("{:#?}", self.statistic);
    }
}
