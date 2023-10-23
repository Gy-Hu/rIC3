use super::{solver::BlockResult, Ic3};
use crate::basic::Ic3Error;
use logic_form::{Cube, Lit};
use std::{collections::HashSet, time::Instant};

impl Ic3 {
    fn down(&mut self, frame: usize, cube: &Cube) -> Result<Option<Cube>, Ic3Error> {
        if self.share.model.cube_subsume_init(cube) {
            return Ok(None);
        }
        self.share.statistic.lock().unwrap().num_down_blocked += 1;
        Ok(match self.blocked_with_ordered(frame, cube, false) {
            BlockResult::Yes(blocked) => Some(self.blocked_get_conflict(&blocked)),
            BlockResult::No(_) => None,
        })
    }

    fn ctg_down(
        &mut self,
        frame: usize,
        cube: &Cube,
        keep: &HashSet<Lit>,
    ) -> Result<Option<Cube>, Ic3Error> {
        let mut cube = cube.clone();
        self.share.statistic.lock().unwrap().num_ctg_down += 1;
        let mut ctgs = 0;
        loop {
            if self.share.model.cube_subsume_init(&cube) {
                return Ok(None);
            }
            match self.blocked(frame, &cube) {
                BlockResult::Yes(blocked) => return Ok(Some(self.blocked_get_conflict(&blocked))),
                BlockResult::No(unblocked) => {
                    let mut model = self.unblocked_get_model(&unblocked);
                    if ctgs < 3 && frame > 1 && !self.share.model.cube_subsume_init(&model) {
                        if self.share.args.cav23 {
                            self.cav23_activity.sort_by_activity(&mut model, false);
                        }
                        if let BlockResult::Yes(blocked) = self.blocked(frame - 1, &model) {
                            ctgs += 1;
                            let conflict = self.blocked_get_conflict(&blocked);
                            let mut i = frame;
                            while i <= self.depth() {
                                if let BlockResult::No(_) = self.blocked(i, &conflict) {
                                    break;
                                }
                                i += 1;
                            }
                            let conflict = self.mic(i - 1, conflict, true)?;
                            self.add_cube(i - 1, conflict);
                            continue;
                        }
                    }
                    ctgs = 0;
                    let cex_set: HashSet<Lit> = HashSet::from_iter(model);
                    let mut cube_new = Cube::new();
                    for lit in cube {
                        if cex_set.contains(&lit) {
                            cube_new.push(lit);
                        } else if keep.contains(&lit) {
                            return Ok(None);
                        }
                    }
                    cube = cube_new;
                }
            }
        }
    }

    fn add_temporary_cube(&mut self, mut frame: usize, cube: &Cube) {
        frame = frame.min(self.depth());
        for solver in self.solvers[1..=frame].iter_mut() {
            solver.add_temporary_clause(&!cube);
        }
    }

    fn handle_down_success(
        &mut self,
        frame: usize,
        cube: Cube,
        i: usize,
        mut new_cube: Cube,
    ) -> (Cube, usize) {
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
        self.add_temporary_cube(frame, &new_cube);
        (new_cube, new_i)
    }

    pub fn mic(&mut self, frame: usize, mut cube: Cube, simple: bool) -> Result<Cube, Ic3Error> {
        let start = Instant::now();
        self.share.statistic.lock().unwrap().average_mic_cube_len += cube.len();
        if !simple {
            self.add_temporary_cube(frame, &cube);
        }
        self.activity.sort_by_activity(&mut cube, true);
        let mut keep = HashSet::new();
        let cav23_parent = self.share.args.cav23.then(|| {
            self.cav23_activity.sort_by_activity(&mut cube, true);
            let mut similar = self.frames.similar(&cube, frame);
            similar.sort_by(|a, b| {
                self.cav23_activity
                    .cube_average_activity(b)
                    .partial_cmp(&self.cav23_activity.cube_average_activity(a))
                    .unwrap()
            });
            let similar = similar.into_iter().nth(0);
            if let Some(similar) = &similar {
                for l in similar.iter() {
                    keep.insert(*l);
                }
            }
            similar
        });
        let mut i = 0;
        while i < cube.len() {
            let mut removed_cube = cube.clone();
            removed_cube.remove(i);
            let res = if simple {
                self.down(frame, &removed_cube)?
            } else {
                self.ctg_down(frame, &removed_cube, &keep)?
            };
            match res {
                Some(new_cube) => {
                    self.share.statistic.lock().unwrap().num_mic_drop_success += 1;
                    (cube, i) = self.handle_down_success(frame, cube, i, new_cube);
                }
                None => {
                    self.share.statistic.lock().unwrap().num_mic_drop_fail += 1;
                    keep.insert(cube[i]);
                    i += 1;
                }
            }
        }
        if let Some(Some(cav23)) = cav23_parent {
            cube.sort_by_key(|x| *x.var());
            if cube.ordered_subsume(&cav23) {
                self.cav23_activity.pump_cube_activity(&cube);
            }
        }
        self.activity.pump_cube_activity(&cube);
        if simple {
            self.share.statistic.lock().unwrap().simple_mic_time += start.elapsed()
        } else {
            self.share.statistic.lock().unwrap().mic_time += start.elapsed()
        }
        Ok(cube)
    }
}
