use super::IC3;
use giputils::hash::GHashSet;
use logic_form::{Lemma, LitVec, Var};
use rand::seq::SliceRandom;
use rand::{rngs::StdRng, SeedableRng};
use satif::Satif;
use std::time::Instant;

impl IC3 {
    pub fn get_bad(&mut self) -> Option<(LitVec, LitVec)> {
        self.statistic.num_get_bad += 1;
        let start = Instant::now();
        if !self.options.ic3.no_pred_prop {
            let res = self.bad_solver.solve(&self.bad_ts.bad.cube());
            self.statistic.block_get_bad_time += start.elapsed();
            res.then(|| {
                self.bad_lift
                    .get_pred(&self.bad_solver, &self.bad_ts.bad.cube(), true)
            })
        } else {
            let res = self
                .solvers
                .last_mut()
                .unwrap()
                .solve_without_bucket(&self.ts.bad.cube(), vec![]);
            self.statistic.block_get_bad_time += start.elapsed();
            res.then(|| self.get_pred(self.solvers.len(), true))
        }
    }
}

impl IC3 {
    #[inline]
    pub fn sat_contained(&mut self, frame: usize, lemma: &Lemma) -> bool {
        !self.solvers[frame].solve(lemma, vec![])
    }

    pub fn blocked_with_ordered(
        &mut self,
        frame: usize,
        cube: &LitVec,
        ascending: bool,
        strengthen: bool,
    ) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.solvers[frame - 1].inductive(&ordered_cube, strengthen)
    }

    pub fn blocked_with_ordered_with_constrain(
        &mut self,
        frame: usize,
        cube: &LitVec,
        ascending: bool,
        strengthen: bool,
        constraint: Vec<LitVec>,
    ) -> bool {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.solvers[frame - 1].inductive_with_constrain(&ordered_cube, strengthen, constraint)
    }

    pub fn get_pred(&mut self, frame: usize, strengthen: bool) -> (LitVec, LitVec) {
        let start = Instant::now();
        let solver = &mut self.solvers[frame - 1];
        let mut cls: LitVec = solver.get_last_assump().clone();
        cls.extend_from_slice(&self.abs_cst);
        if cls.is_empty() {
            return (LitVec::new(), LitVec::new());
        }
        let in_cls: GHashSet<Var> = GHashSet::from_iter(cls.iter().map(|l| l.var()));
        let cls = !cls;
        let mut inputs = LitVec::new();
        for input in self.ts.inputs.iter() {
            let lit = input.lit();
            if let Some(v) = solver.sat_value(lit) {
                inputs.push(lit.not_if(!v));
            }
        }
        self.lift.set_domain(cls.iter().cloned());
        let mut latchs = LitVec::new();
        for latch in self.ts.latchs.iter() {
            let lit = latch.lit();
            if self.lift.domain.has(lit.var()) {
                if let Some(v) = solver.sat_value(lit) {
                    if in_cls.contains(latch) || !solver.flip_to_none(*latch) {
                        latchs.push(lit.not_if(!v));
                    }
                }
            }
        }
        let inn: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
            cube.sort();
            cube.reverse();
        });
        let act: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
            self.activity.sort_by_activity(cube, false);
        });
        let rev: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
            cube.reverse();
        });
        let mut order = if self.options.ic3.inn || !self.auxiliary_var.is_empty() {
            vec![inn, act, rev]
        } else {
            vec![act, rev]
        };
        for i in 0.. {
            if latchs.is_empty() {
                break;
            }
            if let Some(f) = order.get_mut(i) {
                f(&mut latchs);
            } else {
                latchs.shuffle(&mut self.rng);
            }
            let olen = latchs.len();
            latchs = self.lift.minimal_pred(&inputs, &latchs, &cls).unwrap();
            if latchs.len() == olen || !strengthen {
                break;
            }
        }
        self.lift.unset_domain();
        self.statistic.block_get_predecessor_time += start.elapsed();
        (latchs, inputs)
    }

    pub fn new_var(&mut self) -> Var {
        let var = self.ts.new_var();
        for s in self.solvers.iter_mut() {
            assert!(var == s.new_var());
        }
        assert!(var == self.lift.new_var());
        var
    }

    pub fn get_multiple_preds(&mut self, frame: usize, strengthen: bool, num_samples: usize) -> Vec<(LitVec, LitVec)> {
        if num_samples <= 1 {
            let pred = self.get_pred(frame, strengthen);
            return vec![pred];
        }

        let mut results = Vec::with_capacity(num_samples);
        let mut blocking_clauses = Vec::new();

        // Track statistics for multiple predecessor sampling
        self.statistic.total_pred_samples += num_samples;

        // Get the first predecessor using the original method
        let first_pred = self.get_pred(frame, strengthen);
        if first_pred.0.is_empty() {
            return vec![];
        }
        results.push(first_pred.clone());
        self.statistic.successful_pred_samples += 1;

        // For subsequent predecessors, we'll block the previous ones and try different orderings
        for i in 1..num_samples {
            // Add blocking clause for the previous model
            let blocking_clause = !results.last().unwrap().0.clone();
            blocking_clauses.push(blocking_clause);

            // Try to get another predecessor with the blocking clauses
            let solver = &mut self.solvers[frame - 1];
            let mut cls: LitVec = solver.get_last_assump().clone();
            cls.extend_from_slice(&self.abs_cst);
            
            if cls.is_empty() {
                break;
            }

            // Check if SAT with blocking clauses
            let can_block = solver.solve(&cls, blocking_clauses.clone());
            if !can_block {
                break; // No more models available
            }

            // Get a new predecessor with different ordering or random choice
            let start = Instant::now();
            
            let in_cls: GHashSet<Var> = GHashSet::from_iter(cls.iter().map(|l| l.var()));
            let cls = !cls;
            let mut inputs = LitVec::new();
            for input in self.ts.inputs.iter() {
                let lit = input.lit();
                if let Some(v) = solver.sat_value(lit) {
                    inputs.push(lit.not_if(!v));
                }
            }
            
            self.lift.set_domain(cls.iter().cloned());
            let mut latchs = LitVec::new();
            for latch in self.ts.latchs.iter() {
                let lit = latch.lit();
                if self.lift.domain.has(lit.var()) {
                    if let Some(v) = solver.sat_value(lit) {
                        if in_cls.contains(latch) || !solver.flip_to_none(*latch) {
                            latchs.push(lit.not_if(!v));
                        }
                    }
                }
            }
            
            // Use different ordering strategies based on the sample index
            // to increase the diversity of the generated models
            let mut order: Vec<Box<dyn FnMut(&mut LitVec)>> = Vec::new();
            
            // Add standard orderings
            let inn: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
                cube.sort();
                cube.reverse();
            });
            let act: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
                self.activity.sort_by_activity(cube, false);
            });
            let rev: Box<dyn FnMut(&mut LitVec)> = Box::new(|cube: &mut LitVec| {
                cube.reverse();
            });
            
            // Create a separate RNG for the closure to avoid borrow issues
            let seed = self.options.rseed + i as u64;
            let mut closure_rng = StdRng::seed_from_u64(seed);
            
            // Use different orderings for different samples
            match i % 3 {
                0 => {
                    if self.options.ic3.inn || !self.auxiliary_var.is_empty() {
                        order = vec![inn, act, rev];
                    } else {
                        order = vec![act, rev];
                    }
                },
                1 => {
                    order = vec![rev, act];
                },
                _ => {
                    // For the third and subsequent samples, use random shuffling with a separate RNG
                    order = vec![Box::new(move |cube: &mut LitVec| {
                        cube.shuffle(&mut closure_rng);
                    })];
                }
            }
            
            for j in 0.. {
                if latchs.is_empty() {
                    break;
                }
                if let Some(f) = order.get_mut(j) {
                    f(&mut latchs);
                } else {
                    // Use the main RNG here since we're outside the closure
                    latchs.shuffle(&mut self.rng);
                }
                let olen = latchs.len();
                latchs = self.lift.minimal_pred(&inputs, &latchs, &cls).unwrap();
                if latchs.len() == olen || !strengthen {
                    break;
                }
            }
            
            self.lift.unset_domain();
            self.statistic.block_get_predecessor_time += start.elapsed();
            
            if !latchs.is_empty() {
                results.push((latchs, inputs));
                self.statistic.successful_pred_samples += 1;
            }
        }

        if self.options.verbose > 2 {
            println!(
                "Predecessor sampling: {}/{} successful samples", 
                self.statistic.successful_pred_samples, 
                self.statistic.total_pred_samples
            );
        }

        results
    }
}
