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
use mic::{DropVarParameter, MicOrdering, MicType};
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

    fn generalize(&mut self, mut po: ProofObligation, mic_type: MicType) -> Option<Vec<LitVec>> {
        if self.options.ic3.inn && self.ts.cube_subsume_init(&po.lemma) {
            po.frame += 1;
            self.add_obligation(po.clone());
            let cube_clone = po.lemma.cube().clone();
            let added_lemma = self.add_lemma(po.frame - 1, cube_clone.clone(), false, Some(po.clone()));
            return Some(vec![cube_clone]); // Return the lemma we added
        }
        
        // Capture the initial CTI from the initial blocking check
        let initial_generalized_cti = self.solvers[po.frame - 1].inductive_core();
        
        // Critical Check 1: Validate Initial CTI
        let cti_hits_init = po.frame > 0 && !self.options.ic3.inn && self.ts.cube_subsume_init(&initial_generalized_cti);
        
        // Additional validation to avoid false positives
        let mut unreliable_cti = false;
        if cti_hits_init || initial_generalized_cti.is_empty() {
            // The CTI is suspicious - it's either empty or only involves init-state variables
            unreliable_cti = true;
            
            if self.options.verbose > 1 {
                eprintln!("[WARNING] Suspicious CTI for frame {} - hits_init: {}, len: {}", 
                         po.frame, cti_hits_init, initial_generalized_cti.len());
                
                // Log each literal in the CTI and how it relates to init_map
                if self.options.verbose > 3 {
                    eprintln!("[DEBUG] CTI literals vs init_map:");
                    for lit in &initial_generalized_cti {
                        let init_val = self.ts.init_map[lit.var()];
                        eprintln!("[DEBUG]   Lit: {:?}, Init: {:?}, Match: {}", 
                                 lit, init_val, 
                                 init_val.map(|v| v == lit.polarity()).unwrap_or(false));
                    }
                }
            }
        }
        
        if unreliable_cti {
            // The only reason this block failed must involve the initial state.
            // Generalization based on this CTI at this frame is invalid.
            // Signal failure to the caller (block function).
            if self.options.verbose > 1 {
                eprintln!("Warning: Initial CTI for frame {} is unreliable. Aborting generalization for this PO.", po.frame);
            }
            return None; // Indicate generalization failed for this PO at this step
        }
        
        // Proceed with MIC generation only if the base CTI is valid for this frame.
        let base_cti_for_mic = initial_generalized_cti; // Use the validated CTI
        
        // Prepare for Multi-MIC
        let mut generated_mics: Vec<LitVec> = Vec::new();
        let orderings_to_try = [
            MicOrdering::ActivityAscending,
            MicOrdering::ActivityDescending,
            MicOrdering::TopologicalAscending,
            MicOrdering::TopologicalDescending,
        ];
        
        // Loop through orderings
        for &ordering in orderings_to_try.iter() {
            // Call the new refinement function for each ordering
            let mic_for_this_ordering = self.refine_mic_with_ordering(
                po.frame,
                base_cti_for_mic.clone(), // Use the validated CTI
                ordering,
                &[], // Empty constraints during generalize
                mic_type, // Pass MIC parameters (ctg settings etc.)
            );
            
            // Temporarily add all non-empty results. Validation happens later.
            if !mic_for_this_ordering.is_empty() {
                generated_mics.push(mic_for_this_ordering);
            }
        }
        
        // Deduplicate potentially identical MICs generated by different orderings
        generated_mics.sort();
        generated_mics.dedup();
        
        // Filter out invalid MICs (those that subsume init state)
        let valid_mics: Vec<LitVec> = generated_mics
            .into_iter()
            .filter(|mic_cube| {
                // Skip MICs that subsume init state (unless allowed by inn)
                if po.frame > 0 && !self.options.ic3.inn && self.ts.cube_subsume_init(mic_cube) {
                    if self.options.verbose > 2 {
                        eprintln!("Warning: Skipping init-subsuming MIC generated for frame {}: {:?}", po.frame, mic_cube);
                    }
                    false
                } else {
                    true
                }
            })
            .collect();
        
        // Update statistics even if we're not adding lemmas immediately
        for mic_cube in &valid_mics {
            self.statistic.avg_po_cube_len += mic_cube.len();
        }
        
        // Return the valid MICs for the block function to process
        Some(valid_mics)
    }

    fn block(&mut self) -> Option<bool> {
        while let Some(mut po) = self.obligations.pop(self.level()) {
            if po.removed { continue; }

            // Log the current proof obligation for debugging
            if self.options.verbose > 3 {
                eprintln!("Examining PO: Frame={}, Lemma={:?}, Depth={}", 
                          po.frame, po.lemma, po.depth);
            }

            // =========================================================
            // === PRIORITY 1: Check for Frame 0 / Immediate CEX ===
            // =========================================================
            if po.frame == 0 {
                // *** DEBUG LOGGING ***
                eprintln!("[DEBUG] Checking Frame 0 PO Lemma: {:?}", po.lemma);
                let init_check = self.ts.cube_subsume_init(&po.lemma);
                eprintln!("[DEBUG] Result of cube_subsume_init: {}", init_check);
                // Log each latch's init value vs. lemma value
                if self.options.verbose > 4 {
                    eprintln!("[DEBUG] Detailed latch-by-latch consistency check:");
                    for lit in po.lemma.iter() {
                        let var = lit.var();
                        let polarity = lit.polarity();
                        let init_val = self.ts.init_map[var];
                        eprintln!("[DEBUG]   Latch {:?} - Lemma polarity: {}, Init value: {:?}", 
                                 var, polarity, init_val);
                    }
                }
                
                if init_check {
                    // Extra validation: check if this is likely a false positive
                    // Count how many literals match their initial values vs. how many don't
                    if self.options.verbose > 3 {
                        let mut init_matches = 0;
                        let mut init_mismatches = 0;
                        let mut non_init_lits = 0;
                        
                        for lit in po.lemma.iter() {
                            match self.ts.init_map[lit.var()] {
                                Some(init_val) if init_val == lit.polarity() => init_matches += 1,
                                Some(_) => init_mismatches += 1, // Shouldn't happen with init_check=true
                                None => non_init_lits += 1,
                            }
                        }
                        
                        eprintln!("[DEBUG] F0 PO validation - init matches: {}, mismatches: {}, non-init: {}", 
                                 init_matches, init_mismatches, non_init_lits);
                                 
                        // If suspiciously few init matches, this may be a false positive
                        if init_matches < 3 && po.lemma.len() > 10 {
                            eprintln!("[WARNING] Suspicious F0 PO with very few init literals compared to size");
                        }
                    }
                    
                    // If we got here, Frame 0 CEX detected. UNSAFE.
                    if self.options.verbose > 2 {
                        eprintln!("Path 1: Frame 0 PO hits init state. UNSAFE.");
                    }
                    self.add_obligation(po); // Re-add for witness trace
                    return Some(false);      // UNSAFE
                } else {
                    // Unexpected state: Frame 0 PO that doesn't hit init.
                    // This shouldn't normally happen via get_bad.
                    // Treat as an error or potential UNSAFE path.
                    eprintln!("Critical Error: Frame 0 PO {:?} does not hit init state!", po);
                    if self.options.verbose > 1 {
                        eprintln!("Path 2: Frame 0 PO does not hit init state. Failing conservatively.");
                    }
                    self.add_obligation(po); // Re-add
                    return Some(false);      // Report UNSAFE conservatively
                }
            }
            
            // =========================================================
            // === Frame > 0 Processing ==============================
            // =========================================================
            assert!(po.frame > 0); // Logic below assumes frame > 0
            
            // Pre-calculate blocked status based on transition relation
            // We might override this later if the init check dictates it
            let blocked_start = Instant::now();
            let mut blocked = self.blocked_with_ordered(po.frame, &po.lemma, false, false);
            self.statistic.block_blocked_time += blocked_start.elapsed();
            
            // *** DEBUG LOGGING ***
            if blocked {
                let core_debug = self.solvers[po.frame - 1].inductive_core();
                eprintln!("[DEBUG] Blocked PO at frame {}: {:?}", po.frame, po);
                eprintln!("[DEBUG] Inductive Core: {:?}", core_debug);
                // Check if the core is init-consistent
                let core_init_consistent = self.ts.cube_subsume_init(&core_debug);
                eprintln!("[DEBUG] Core is init-consistent: {} (length: {})", 
                          core_init_consistent, core_debug.len());
            }

            // Default assumption, might be overridden
            let mut requires_predecessor = !blocked;
            let mut invariant_found_during_generalization = false;

            // --- Handle Init State Consistency and Reachability Check ---
            let is_init_consistent = self.ts.cube_subsume_init(&po.lemma);
            if self.options.verbose > 3 {
                eprintln!("PO at frame {} is init-consistent: {}", po.frame, is_init_consistent);
            }

            if is_init_consistent {
                if self.options.ic3.abs_cst {
                    if self.options.verbose > 3 {
                        eprintln!("Path 3: Init-consistent PO with abs_cst option.");
                    }
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
                        if self.options.verbose > 2 {
                            eprintln!("Path 4: BMC witness check confirmed CEX. UNSAFE.");
                        }
                        return Some(false);
                    }
                } else if self.options.ic3.inn {
                    // Use the assertion to provide additional debugging info
                    let is_reachable = self.solvers[0].solve(&po.lemma, vec![]);
                    if is_reachable {
                        if self.options.verbose > 1 {
                            eprintln!("INN check failed: PO at frame {} hits init and is reachable from init(0)",
                                     po.frame);
                        }
                    }
                    assert!(!is_reachable,
                           "INN check failed: PO {:?} at frame {} hits init and is reachable from init(0)", po, po.frame);
                    
                    if self.options.verbose > 3 {
                        eprintln!("Path 5: Init-consistent PO with inn option, proceeding with normal blocking.");
                    }
                    // Do not return; let normal blocking/generalization proceed below
                } else {
                    // --- !inn Logic (Fixed) ---
                    // Check reachability from actual frame 0 initial states
                    if self.options.verbose > 4 {
                        eprintln!("Running crucial reachability check for init-consistent state at frame {}", po.frame);
                    }
                    
                    // Fix: Be explicit about using the Frame 0 solver to check reachability
                    let is_reachable_from_init = self.solvers[0].solve(&po.lemma, vec![]);
                    
                    if is_reachable_from_init {
                        // Reachable! Confirmed CEX.
                        if self.options.verbose > 1 {
                            eprintln!("Path 6: PO lemma at frame {} hits init and is reachable from frame 0. UNSAFE.", po.frame);
                        }
                        self.add_obligation(po); // Keep for witness
                        return Some(false); // UNSAFE
                    } else {
                        // Consistent with init def, but NOT reachable from frame 0. Treat as blocked.
                        if self.options.verbose > 2 {
                            eprintln!("Path 7: PO lemma at frame {} hits init definition but is unreachable from frame 0. Generalizing.", po.frame);
                        }
                        blocked = true;             // Override: Treat as blocked
                        requires_predecessor = false; // Override: Do not generate predecessor
                        // Fall through to generalization logic below
                    }
                    // --- End !inn Logic ---
                }
            }

            // Check 2: Trivial Containment (After init checks)
            if !blocked { // Only check trivial containment if not already known to be blocked
                if let Some((bf, _)) = self.frame.trivial_contained(po.frame, &po.lemma) {
                    // PO is subsumed by a lemma in a higher frame 'bf'.
                    // Push the obligation beyond that frame.
                    if self.options.verbose > 3 {
                        eprintln!("Path 8: PO trivially contained in frame {}. Pushing to frame {}.", bf, bf+1);
                    }
                    po.push_to(bf + 1);
                    self.add_obligation(po);
                    continue; // Process the next obligation
                }
            }

            // Prepare for generalization
            if self.options.verbose > 2 {
                self.frame.statistic();
            }
            po.bump_act();
            
            if blocked {
                // State `po` is blocked (either by transition or because it hit unreachable init).
                // Attempt Generalization.
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
                
                // Attempt generalization with the appropriate mic_type
                match self.generalize(po.clone(), mic_type) {
                    Some(valid_mics) => {
                        // Generalization ran and produced valid MICs (list might be empty)
                        if !valid_mics.is_empty() {
                            if self.options.verbose > 1 {
                                eprintln!("Note: Adding {} MIC(s) for PO at frame {}", valid_mics.len(), po.frame);
                            }
                            // Add the valid MICs
                            for mic_cube in valid_mics {
                                let (pushed_frame, pushed_mic) = self.push_lemma(po.frame, mic_cube);
                                
                                // Update PO frame for next lemma
                                let mut po_clone = po.clone();
                                po_clone.push_to(pushed_frame);
                                self.add_obligation(po_clone);
                                
                                if self.add_lemma(pushed_frame - 1, pushed_mic.clone(), false, Some(po.clone())) {
                                    // Found the invariant!
                                    invariant_found_during_generalization = true;
                                    // We can break the MIC adding loop, but must finish processing this PO.
                                    break;
                                }
                            }
                        } else {
                            // Generalize ran but produced no valid MICs.
                            if self.options.verbose > 1 {
                                eprintln!("Note: Generalization for PO at frame {} produced no valid MICs.", po.frame);
                            }
                        }
                        
                        // Decide if predecessor is still needed:
                        // If the state was init-unreachable, requires_predecessor is already false
                        // Otherwise check if invariant was found
                        if !requires_predecessor {
                            // Keep requires_predecessor as false (from init check)
                        } else {
                            requires_predecessor = !invariant_found_during_generalization;
                        }
                    }
                    None => {
                        // Generalize failed early (initial CTI invalid). Predecessor required.
                        if self.options.verbose > 1 {
                            eprintln!("Note: Generalization failed early for PO at frame {}, requires predecessor.", po.frame);
                        }
                        requires_predecessor = true;
                    }
                }
            }

            // If invariant was found above, continue to next PO
            if invariant_found_during_generalization {
                continue; // The main loop will check for termination later
            }

            // Action: Predecessor Generation OR Re-add original PO
            if requires_predecessor {
                if self.options.verbose > 1 && blocked { // Log only if fallback after block
                    eprintln!("Note: Falling back to predecessor for blocked PO at frame {}", po.frame);
                }
                // Generate predecessor CTI
                let (pred_cti_lemma, inputs) = self.get_pred(po.frame, true);
                let pred_po = ProofObligation::new(
                    po.frame - 1,        // Predecessor is at frame F-1
                    Lemma::new(pred_cti_lemma),
                    vec![inputs],        // Capture input assignments for witness
                    po.depth + 1,        // Increment CEX depth
                    Some(po.clone()),    // Link back to original PO
                );
                self.add_obligation(pred_po); // Add the new predecessor task

                // Re-add the original obligation `po`. It must wait until its predecessor
                // is processed and hopefully blocked/generalized.
                self.add_obligation(po);
            }
            // If requires_predecessor is false, we simply drop this PO instance
        } // End while loop

        // If loop finishes, obligation queue is empty.
        Some(true) // Report SAFE (pending propagation check for invariant)
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
        let mut statistic = SolverStatistic::default();
        for s in self.solvers.iter() {
            statistic += s.statistic;
        }
        println!("{:#?}", statistic);
        println!("{:#?}", self.statistic);
    }
}
