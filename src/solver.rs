use super::Frames;
use crate::{model::Model, Ic3};
use logic_form::{Clause, Cube, Lit};
use satif::{SatResult, Satif, SatifSat, SatifUnsat};
use std::{mem::take, ops::Deref, time::Instant};

pub type SatSolver = minisat::Solver;
pub type Sat = minisat::Sat;
pub type Unsat = minisat::Unsat;

pub struct Ic3Solver {
    solver: Box<SatSolver>,
    num_act: usize,
    frame: usize,
    temporary: Vec<Cube>,
}

impl Ic3Solver {
    pub fn new(model: &Model, frame: usize) -> Self {
        let mut solver = Box::new(SatSolver::new());
        let false_lit: Lit = solver.new_var().into();
        solver.add_clause(&[!false_lit]);
        model.load_trans(&mut solver);
        Self {
            solver,
            frame,
            num_act: 0,
            temporary: Vec::new(),
        }
    }

    pub fn reset(&mut self, model: &Model, frames: &Frames) {
        let temporary = take(&mut self.temporary);
        *self = Self::new(model, self.frame);
        for t in temporary {
            self.solver.add_clause(&!&t);
            self.temporary.push(t);
        }
        let frames_slice = if self.frame == 0 {
            &frames[0..1]
        } else {
            &frames[self.frame..]
        };
        for dnf in frames_slice.iter() {
            for cube in dnf {
                self.add_clause(&!cube.deref());
            }
        }
    }

    pub fn add_clause(&mut self, clause: &Clause) {
        let mut cube = !clause;
        cube.sort_by_key(|x| x.var());
        let temporary = take(&mut self.temporary);
        for t in temporary {
            if !cube.ordered_subsume(&t) {
                self.temporary.push(t);
            }
        }
        self.solver.add_clause(clause);
    }

    #[allow(unused)]
    pub fn solve(&mut self, assumptions: &[Lit]) -> SatResult<Sat, Unsat> {
        self.solver.solve(assumptions)
    }
}

impl Ic3 {
    fn blocked_inner(&mut self, frame: usize, cube: &Cube, strengthen: bool) -> BlockResult {
        self.statistic.num_sat_inductive += 1;
        let solver_idx = frame - 1;
        let solver = &mut self.solvers[solver_idx].solver;
        let start = Instant::now();
        let mut assumption = self.model.cube_next(cube);
        let sat_start = Instant::now();
        let res = if strengthen {
            let act = solver.new_var().into();
            assumption.push(act);
            let mut tmp_cls = !cube;
            tmp_cls.push(!act);
            solver.add_clause(&tmp_cls);
            let act = !assumption.pop().unwrap();
            let res = match solver.solve(&assumption) {
                SatResult::Sat(_) => BlockResult::No(BlockResultNo {
                    solver: solver.as_mut(),
                    assumption,
                    act: Some(act),
                }),
                SatResult::Unsat(_) => BlockResult::Yes(BlockResultYes {
                    solver: solver.as_mut(),
                    cube: cube.clone(),
                    assumption,
                    act: Some(act),
                }),
            };
            res
        } else {
            match solver.solve(&assumption) {
                SatResult::Sat(_) => BlockResult::No(BlockResultNo {
                    solver: solver.as_mut(),
                    assumption,
                    act: None,
                }),
                SatResult::Unsat(_) => BlockResult::Yes(BlockResultYes {
                    solver: solver.as_mut(),
                    cube: cube.clone(),
                    assumption,
                    act: None,
                }),
            }
        };
        self.statistic.avg_sat_call_time += sat_start.elapsed();
        self.statistic.sat_inductive_time += start.elapsed();
        res
    }

    pub fn blocked(&mut self, frame: usize, cube: &Cube, strengthen: bool) -> BlockResult {
        assert!(!self.model.cube_subsume_init(cube));
        let solver = &mut self.solvers[frame - 1];
        solver.num_act += 1;
        if solver.num_act > 1000 {
            self.statistic.num_solver_restart += 1;
            solver.reset(&self.model, &self.frames);
        }
        self.blocked_inner(frame, cube, strengthen)
    }

    pub fn blocked_with_ordered(
        &mut self,
        frame: usize,
        cube: &Cube,
        ascending: bool,
        strengthen: bool,
    ) -> BlockResult {
        let mut ordered_cube = cube.clone();
        self.activity.sort_by_activity(&mut ordered_cube, ascending);
        self.blocked(frame, &ordered_cube, strengthen)
    }
}

pub enum BlockResult {
    Yes(BlockResultYes),
    No(BlockResultNo),
}

#[derive(Debug)]
pub struct BlockResultYes {
    solver: *mut SatSolver,
    cube: Cube,
    assumption: Cube,
    act: Option<Lit>,
}

impl Drop for BlockResultYes {
    fn drop(&mut self) {
        if let Some(act) = self.act {
            let solver = unsafe { &mut *self.solver };
            solver.add_clause(&[act]);
        }
    }
}

#[derive(Debug)]
pub struct BlockResultNo {
    solver: *mut SatSolver,
    assumption: Cube,
    act: Option<Lit>,
}

impl BlockResultNo {
    pub fn lit_value(&self, lit: Lit) -> Option<bool> {
        let solver = unsafe { &mut *self.solver };
        unsafe { solver.get_model() }.lit_value(lit)
    }
}

impl Drop for BlockResultNo {
    fn drop(&mut self) {
        if let Some(act) = self.act {
            let solver = unsafe { &mut *self.solver };
            solver.add_clause(&[act]);
        }
    }
}

impl Ic3 {
    pub fn blocked_conflict(&mut self, block: BlockResultYes) -> Cube {
        let solver = unsafe { &mut *block.solver };
        let conflict = unsafe { solver.get_conflict() };
        let mut ans = Cube::new();
        for i in 0..block.cube.len() {
            if conflict.has(block.assumption[i]) {
                ans.push(block.cube[i]);
            }
        }
        if self.model.cube_subsume_init(&ans) {
            ans = Cube::new();
            let new = *block
                .cube
                .iter()
                .find(|l| {
                    self.model
                        .init_map
                        .get(&l.var())
                        .is_some_and(|i| *i != l.polarity())
                })
                .unwrap();
            for i in 0..block.cube.len() {
                if conflict.has(block.assumption[i]) || block.cube[i] == new {
                    ans.push(block.cube[i]);
                }
            }
            assert!(!self.model.cube_subsume_init(&ans));
        }
        ans
    }

    pub fn unblocked_model(&mut self, unblock: BlockResultNo) -> Cube {
        let solver = unsafe { &mut *unblock.solver };
        let model = unsafe { solver.get_model() };
        self.minimal_predecessor(&unblock.assumption, model)
    }
}

pub struct Lift {
    solver: SatSolver,
    num_act: usize,
}

impl Lift {
    pub fn new(model: &Model) -> Self {
        let mut solver = SatSolver::new();
        let false_lit: Lit = solver.new_var().into();
        solver.add_clause(&[!false_lit]);
        model.load_trans(&mut solver);
        Self { solver, num_act: 0 }
    }
}

impl Ic3 {
    pub fn minimal_predecessor(&mut self, successor: &Cube, model: Sat) -> Cube {
        let start = Instant::now();
        self.lift.num_act += 1;
        if self.lift.num_act > 1000 {
            self.lift = Lift::new(&self.model)
        }
        let act: Lit = self.lift.solver.new_var().into();
        let mut assumption = Cube::from([act]);
        let mut cls = !successor;
        cls.push(!act);
        self.lift.solver.add_clause(&cls);
        for input in self.model.inputs.iter() {
            let lit = input.lit();
            match model.lit_value(lit) {
                Some(true) => assumption.push(lit),
                Some(false) => assumption.push(!lit),
                None => (),
            }
        }
        let mut latchs = Cube::new();
        for latch in self.model.latchs.iter() {
            let lit = latch.lit();
            match model.lit_value(lit) {
                Some(true) => latchs.push(lit),
                Some(false) => latchs.push(!lit),
                None => (),
            }
        }
        self.activity.sort_by_activity(&mut latchs, false);
        assumption.extend_from_slice(&latchs);
        let res: Cube = match self.lift.solver.solve(&assumption) {
            SatResult::Sat(_) => panic!(),
            SatResult::Unsat(conflict) => latchs.into_iter().filter(|l| conflict.has(*l)).collect(),
        };
        self.lift.solver.add_clause(&[!act]);
        self.statistic.minimal_predecessor_time += start.elapsed();
        res
    }
}
