use super::IC3;
use crate::{options::Options, transys::TransysIf};
use giputils::hash::GHashSet;
use logic_form::{Lemma, Lit, LitVec};
use satif::Satif;
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MicOrdering {
    ActivityAscending,
    ActivityDescending,
    TopologicalAscending,  // Based on variable index or a fixed order
    TopologicalDescending,
    // Potentially add Random in the future
}

#[derive(Clone, Copy, Debug, Default)]
pub struct DropVarParameter {
    pub limit: usize,
    max: usize,
    level: usize,
}

impl DropVarParameter {
    #[inline]
    pub fn new(limit: usize, max: usize, level: usize) -> Self {
        Self { limit, max, level }
    }

    fn sub_level(self) -> Self {
        Self {
            limit: self.limit,
            max: self.max,
            level: self.level - 1,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum MicType {
    NoMic,
    DropVar(DropVarParameter),
}

impl MicType {
    pub fn from_options(options: &Options) -> Self {
        let p = if options.ic3.ctg {
            DropVarParameter {
                limit: options.ic3.ctg_limit,
                max: options.ic3.ctg_max,
                level: 1,
            }
        } else {
            DropVarParameter::default()
        };
        MicType::DropVar(p)
    }
}

impl IC3 {
    fn down(
        &mut self,
        frame: usize,
        cube: &LitVec,
        keep: &GHashSet<Lit>,
        full: &LitVec,
        constraint: &[LitVec],
        cex: &mut Vec<(Lemma, Lemma)>,
    ) -> Option<LitVec> {
        let mut cube = cube.clone();
        self.statistic.num_down += 1;
        loop {
            if self.ts.cube_subsume_init(&cube) {
                return None;
            }
            let lemma = Lemma::new(cube.clone());
            if cex
                .iter()
                .any(|(s, t)| !lemma.subsume(s) && lemma.subsume(t))
            {
                return None;
            }
            self.statistic.num_down_sat += 1;
            if self.blocked_with_ordered_with_constrain(
                frame,
                &cube,
                false,
                true,
                constraint.to_vec(),
            ) {
                return Some(self.solvers[frame - 1].inductive_core());
            }
            let mut ret = false;
            let mut cube_new = LitVec::new();
            for lit in cube {
                if keep.contains(&lit) {
                    if let Some(true) = self.solvers[frame - 1].sat_value(lit) {
                        cube_new.push(lit);
                    } else {
                        ret = true;
                        break;
                    }
                } else if let Some(true) = self.solvers[frame - 1].sat_value(lit) {
                    if !self.solvers[frame - 1].flip_to_none(lit.var()) {
                        cube_new.push(lit);
                    }
                }
            }
            cube = cube_new;
            let mut s = LitVec::new();
            let mut t = LitVec::new();
            for l in full.iter() {
                if let Some(v) = self.solvers[frame - 1].sat_value(*l) {
                    if !self.solvers[frame - 1].flip_to_none(l.var()) {
                        s.push(l.not_if(!v));
                    }
                }
                let lt = self.ts.next(*l);
                if let Some(v) = self.solvers[frame - 1].sat_value(lt) {
                    t.push(l.not_if(!v));
                }
            }
            cex.push((Lemma::new(s), Lemma::new(t)));
            if ret {
                return None;
            }
        }
    }

    fn ctg_down(
        &mut self,
        frame: usize,
        cube: &LitVec,
        keep: &GHashSet<Lit>,
        full: &LitVec,
        parameter: DropVarParameter,
    ) -> Option<LitVec> {
        let mut cube = cube.clone();
        self.statistic.num_down += 1;
        let mut ctg = 0;
        loop {
            if self.ts.cube_subsume_init(&cube) {
                return None;
            }
            self.statistic.num_down_sat += 1;
            if self.blocked_with_ordered(frame, &cube, false, true) {
                return Some(self.solvers[frame - 1].inductive_core());
            }
            for lit in cube.iter() {
                if keep.contains(lit) && !self.solvers[frame - 1].sat_value(*lit).is_some_and(|v| v)
                {
                    return None;
                }
            }
            let (model, _) = self.get_pred(frame, false);
            let cex_set: GHashSet<Lit> = GHashSet::from_iter(model.iter().cloned());
            for lit in cube.iter() {
                if keep.contains(lit) && !cex_set.contains(lit) {
                    return None;
                }
            }
            if ctg < parameter.max
                && frame > 1
                && !self.ts.cube_subsume_init(&model)
                && self.trivial_block(
                    frame - 1,
                    Lemma::new(model.clone()),
                    &[!full.clone()],
                    parameter.sub_level(),
                )
            {
                ctg += 1;
                continue;
            }
            ctg = 0;
            let mut cube_new = LitVec::new();
            for lit in cube {
                if cex_set.contains(&lit) {
                    cube_new.push(lit);
                } else if keep.contains(&lit) {
                    return None;
                }
            }
            cube = cube_new;
        }
    }

    fn handle_down_success(
        &mut self,
        _frame: usize,
        cube: LitVec,
        i: usize,
        mut new_cube: LitVec,
    ) -> (LitVec, usize) {
        new_cube = cube
            .iter()
            .filter(|l| new_cube.contains(l))
            .cloned()
            .collect();
        let new_i = new_cube
            .iter()
            .position(|l| !(cube[0..i]).contains(l))
            .unwrap_or(new_cube.len());
        if new_i < new_cube.len() {
            assert!(!(cube[0..=i]).contains(&new_cube[new_i]))
        }
        (new_cube, new_i)
    }

    pub fn refine_mic_with_ordering(
        &mut self,
        frame: usize,
        initial_cti: LitVec, // The CTI from the *initial* blocking check
        ordering: MicOrdering,
        constraint: &[LitVec], // Constraints relevant to this PO/frame
        mic_type: MicType, // For potential future use (e.g., CTG parameters)
    ) -> LitVec {
        // *** CRUCIAL STEP 1: Isolate Solver State ***
        // Reset assignments, temp clauses, VSIDS heap etc. before this refinement pass.
        // Keeps learned clauses and level-0 assignments from previous IC3 steps.
        self.solvers[frame - 1].reset();

        let start = Instant::now(); // For statistics
        self.statistic.num_mic += 1; // Or a new statistic counter

        let mut current_cube = initial_cti;
        self.statistic.avg_mic_cube_len += current_cube.len(); // Track initial length

        // Loop until no more literals can be removed
        let mut i = 0;
        let mut keep = GHashSet::new(); // Literals confirmed necessary for this pass

        'mic_loop: loop {
            // Sort the cube according to the *current target ordering* at the start
            // of each pass (or after successful removal).
            match ordering {
                MicOrdering::ActivityAscending => self.activity.sort_by_activity(&mut current_cube, true),
                MicOrdering::ActivityDescending => self.activity.sort_by_activity(&mut current_cube, false),
                MicOrdering::TopologicalAscending => current_cube.sort(), // Assumes Lit's Ord is topological
                MicOrdering::TopologicalDescending => { current_cube.sort(); current_cube.reverse(); }
            }

            i = 0; // Reset index after sorting
            while i < current_cube.len() {
                let lit_to_try_removing = current_cube[i];

                if keep.contains(&lit_to_try_removing) {
                    i += 1;
                    continue;
                }

                // Create cube with the literal removed
                let mut removed_cube = current_cube.clone();
                removed_cube.remove(i); // `i` remains valid index for the *original* `current_cube`

                if removed_cube.is_empty() || (self.options.ic3.inn && self.ts.cube_subsume_init(&removed_cube)) {
                   // Cannot remove if it results in empty/init-subsuming cube
                   keep.insert(lit_to_try_removing);
                   i += 1;
                   continue;
                }

                // *** CRUCIAL STEP 2: Relative Inductiveness Check ***
                // Use a consistent internal ordering (e.g., ActivityAscending) for the check itself.
                // The `solve` call inside `blocked_with_ordered_with_constrain` manages its own state reset.
                let is_still_blocked = self.blocked_with_ordered_with_constrain(
                    frame,
                    &removed_cube,
                    true, // Use a fixed ordering for the check (e.g., activity ascending)
                    true, // Strengthen needed to get core
                    constraint.to_vec(), // Pass constraints
                );

                if is_still_blocked {
                    // Removal Successful! The smaller cube is also relatively inductive.
                    // Get the core explaining *why* it's still blocked.
                    let new_core = self.solvers[frame - 1].inductive_core();

                    // Check if this refinement core hits initial state
                    if frame > 0 && self.ts.cube_subsume_init(&new_core) {
                        // If the core from the refinement check hits the initial state,
                        // it means removing `lit_to_try_removing` was invalid because
                        // the resulting `removed_cube` leads back to the initial state.
                        // We should *not* update `current_cube` with this core.
                        // Instead, we must keep `lit_to_try_removing`.
                        keep.insert(lit_to_try_removing);
                        self.statistic.mic_drop.fail(); // Or a specific counter
                        i += 1;
                        continue; // Continue to the next literal in the current_cube
                    }

                    // Update current_cube based on the intersection with the new core
                    // (This is a common MIC refinement step)
                    let original_len = current_cube.len();
                    current_cube.retain(|l| new_core.contains(l));

                    // IMPORTANT: If the cube changed, restart the process from the beginning
                    // with the smaller, re-sorted cube.
                    if current_cube.len() < original_len {
                         keep.clear(); // Reset keep set as the cube has changed
                         self.statistic.mic_drop.success();
                         continue 'mic_loop; // Restart outer loop to re-sort and re-check
                    } else {
                         // Core didn't shrink the cube further, keep the literal for now
                         keep.insert(lit_to_try_removing);
                         i += 1;
                    }

                } else {
                    // Removal Failed! The smaller cube is NOT relatively inductive (SAT found).
                    // This literal is necessary *for this ordering pass*.
                    keep.insert(lit_to_try_removing);
                    self.statistic.mic_drop.fail(); // Or use specific stats
                    i += 1;
                }
            }
            // If we finish the inner loop without restarting, MIC is complete for this ordering
            break 'mic_loop;
        } // End of 'mic_loop

        self.activity.bump_cube_activity(&current_cube); // Bump activity for the final MIC
        self.statistic.block_mic_time += start.elapsed(); // Accumulate time

        current_cube // Return the minimized cube for this specific ordering
    }

    pub fn mic_by_drop_var(
        &mut self,
        frame: usize,
        mut cube: LitVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
    ) -> LitVec {
        let start = Instant::now();
        if parameter.level == 0 {
            self.solvers[frame - 1].set_domain(
                self.ts
                    .lits_next(&cube)
                    .iter()
                    .copied()
                    .chain(cube.iter().copied()),
            );
        }
        self.statistic.avg_mic_cube_len += cube.len();
        self.statistic.num_mic += 1;
        let mut cex = Vec::new();
        self.activity.sort_by_activity(&mut cube, true);
        let mut keep = GHashSet::new();
        let mut i = 0;
        while i < cube.len() {
            if keep.contains(&cube[i]) {
                i += 1;
                continue;
            }
            let mut removed_cube = cube.clone();
            removed_cube.remove(i);
            let mic = if parameter.level == 0 {
                self.down(frame, &removed_cube, &keep, &cube, constraint, &mut cex)
            } else {
                self.ctg_down(frame, &removed_cube, &keep, &cube, parameter)
            };
            if let Some(new_cube) = mic {
                self.statistic.mic_drop.success();
                (cube, i) = self.handle_down_success(frame, cube, i, new_cube);
                if parameter.level == 0 {
                    self.solvers[frame - 1].unset_domain();
                    self.solvers[frame - 1].set_domain(
                        self.ts
                            .lits_next(&cube)
                            .iter()
                            .copied()
                            .chain(cube.iter().copied()),
                    );
                }
            } else {
                self.statistic.mic_drop.fail();
                keep.insert(cube[i]);
                i += 1;
            }
        }
        if parameter.level == 0 {
            self.solvers[frame - 1].unset_domain();
        }
        self.activity.bump_cube_activity(&cube);
        self.statistic.block_mic_time += start.elapsed();
        cube
    }

    pub fn mic(
        &mut self,
        frame: usize,
        cube: LitVec,
        constraint: &[LitVec],
        mic_type: MicType,
    ) -> LitVec {
        match mic_type {
            MicType::NoMic => cube,
            MicType::DropVar(parameter) => self.mic_by_drop_var(frame, cube, constraint, parameter),
        }
    }
}
