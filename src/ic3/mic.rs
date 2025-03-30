use super::IC3;
use crate::{options::Options, transys::TransysIf};
use giputils::hash::GHashSet;
use logic_form::{Lemma, Lit, LitVec};
use satif::Satif;
use std::time::Instant;
use rand::Rng;
use rand::RngCore;

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
    MultiClauses(DropVarParameter, usize),
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
        
        if options.ic3.multi_clauses > 1 {
            MicType::MultiClauses(p, options.ic3.multi_clauses)
        } else {
            MicType::DropVar(p)
        }
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

    pub fn mic_by_drop_var(
        &mut self,
        frame: usize,
        mut cube: LitVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
        manage_domain: bool,
    ) -> LitVec {
        let start = Instant::now();
        if parameter.level == 0 && manage_domain {
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
        if self.options.ic3.topo_sort {
            cube.sort();
            if self.options.ic3.reverse_sort {
                cube.reverse();
            }
        } else {
            let ascending = !self.options.ic3.reverse_sort;
            self.activity.sort_by_activity(&mut cube, ascending);
        }
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
                if parameter.level == 0 && manage_domain {
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
        if parameter.level == 0 && manage_domain {
            self.solvers[frame - 1].unset_domain();
        }
        self.activity.bump_cube_activity(&cube);
        self.statistic.block_mic_time += start.elapsed();
        cube
    }

    pub fn mic_by_multi_clauses(
        &mut self,
        frame: usize,
        cube: &LitVec,
        constraint: &[LitVec],
        parameter: DropVarParameter,
        num_clauses: usize,
    ) -> Vec<LitVec> {
        let start = Instant::now();
        
        let domain_needs_handling = parameter.level == 0;
        if domain_needs_handling {
            self.solvers[frame - 1].unset_domain();
        }
        
        self.statistic.avg_mic_cube_len += cube.len();
        self.statistic.num_mic += 1;
        
        let mut variants = Vec::new();
        
        variants.push((cube.clone(), self.options.ic3.topo_sort, self.options.ic3.reverse_sort));
        
        if num_clauses > 1 && !self.options.ic3.inn {
            variants.push((cube.clone(), self.options.ic3.topo_sort, !self.options.ic3.reverse_sort));
            
            variants.push((cube.clone(), !self.options.ic3.topo_sort, self.options.ic3.reverse_sort));
            
            variants.push((cube.clone(), !self.options.ic3.topo_sort, !self.options.ic3.reverse_sort));
            
            if num_clauses > 4 {
                for _ in 0..(num_clauses - 4).min(3) {
                    let mut randomized_cube = cube.clone();
                    let mut indices: Vec<usize> = (0..randomized_cube.len()).collect();
                    for i in 0..indices.len() {
                        let j = self.rng.next_u32() as usize % indices.len();
                        indices.swap(i, j);
                    }
                    
                    let mut reordered_cube = LitVec::new();
                    for &idx in &indices {
                        if idx < randomized_cube.len() {
                            reordered_cube.push(randomized_cube[idx]);
                        }
                    }
                    
                    let topo = self.rng.next_u32() % 2 == 0;
                    let reverse = self.rng.next_u32() % 2 == 0;
                    variants.push((reordered_cube, topo, reverse));
                }
            }
        }
        
        let mut clauses = Vec::new();
        
        for (variant_cube, topo_sort, reverse_sort) in variants {
            if clauses.len() >= num_clauses {
                break;
            }
            
            let original_topo_sort = self.options.ic3.topo_sort;
            let original_reverse_sort = self.options.ic3.reverse_sort;
            
            self.options.ic3.topo_sort = topo_sort;
            self.options.ic3.reverse_sort = reverse_sort;
            
            if domain_needs_handling {
                self.solvers[frame - 1].set_domain(
                    self.ts
                        .lits_next(&variant_cube)
                        .iter()
                        .copied()
                        .chain(variant_cube.iter().copied()),
                );
            }
            
            let result_cube = self.mic_by_drop_var(frame, variant_cube, constraint, parameter, false);
            
            self.options.ic3.topo_sort = original_topo_sort;
            self.options.ic3.reverse_sort = original_reverse_sort;
            
            self.statistic.total_multi_clauses += 1;
            
            if !clauses.contains(&result_cube) {
                clauses.push(result_cube);
                self.statistic.unique_multi_clauses += 1;
            }
            
            if domain_needs_handling {
                self.solvers[frame - 1].unset_domain();
            }
        }
        
        self.statistic.block_mic_time += start.elapsed();
        clauses
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
            MicType::DropVar(parameter) => {
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
                
                let result = self.mic_by_drop_var(frame, cube, constraint, parameter, false);
                
                if parameter.level == 0 {
                    self.solvers[frame - 1].unset_domain();
                }
                
                result
            },
            MicType::MultiClauses(parameter, num_clauses) => {
                let clauses = self.mic_by_multi_clauses(frame, &cube, constraint, parameter, num_clauses);
                if let Some(first_clause) = clauses.into_iter().next() {
                    first_clause
                } else {
                    cube
                }
            }
        }
    }

    pub fn mic_multi(
        &mut self,
        frame: usize,
        cube: LitVec,
        constraint: &[LitVec],
        mic_type: MicType,
    ) -> Vec<LitVec> {
        match mic_type {
            MicType::NoMic => vec![cube],
            MicType::DropVar(parameter) => {
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
                
                let result = vec![self.mic_by_drop_var(frame, cube, constraint, parameter, false)];
                
                if parameter.level == 0 {
                    self.solvers[frame - 1].unset_domain();
                }
                
                result
            },
            MicType::MultiClauses(parameter, num_clauses) => {
                self.mic_by_multi_clauses(frame, &cube, constraint, parameter, num_clauses)
            }
        }
    }
}
