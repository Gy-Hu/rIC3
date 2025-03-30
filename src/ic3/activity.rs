use crate::transys::TransysCtx;
use logic_form::{Lit, LitVec, Var, VarMap};
use std::ops::MulAssign;

pub struct Activity {
    activity: VarMap<f64>,
    max_act: f64,
    act_inc: f64,
}

impl Activity {
    pub fn new(ts: &TransysCtx) -> Self {
        let mut activity = VarMap::new();
        activity.reserve(ts.max_latch);
        Self {
            activity,
            max_act: 0.0,
            act_inc: 1.0,
        }
    }

    #[inline]
    #[allow(unused)]
    pub fn reserve(&mut self, var: Var) {
        self.activity.reserve(var);
    }

    #[inline]
    fn bump(&mut self, var: Var) {
        self.activity[var] += self.act_inc;
        self.max_act = self.max_act.max(self.activity[var]);
        if self.activity[var] > 1e100 {
            self.activity.iter_mut().for_each(|a| a.mul_assign(1e-100));
            self.act_inc *= 1e-100;
            self.max_act *= 1e-100;
        }
    }

    #[inline]
    #[allow(unused)]
    pub fn set_max_act(&mut self, var: Var) {
        self.activity[var] = self.max_act;
    }

    #[inline]
    pub fn decay(&mut self) {
        self.act_inc *= 1.0 / 0.9
    }

    pub fn bump_cube_activity(&mut self, cube: &LitVec) {
        self.decay();
        cube.iter().for_each(|l| self.bump(l.var()));
    }

    pub fn sort_by_activity(&self, cube: &mut LitVec, ascending: bool) {
        let ascending_func =
            |a: &Lit, b: &Lit| self.activity[*a].partial_cmp(&self.activity[*b]).unwrap();
        if ascending {
            cube.sort_by(ascending_func);
        } else {
            cube.sort_by(|a, b| ascending_func(b, a));
        }
    }

    /// Sort the cube using a hybrid approach that combines topological and activity-based ordering
    /// with a weight that decays based on the frame number
    pub fn sort_hybrid(&self, cube: &mut LitVec, frame: usize, reverse: bool) {
        // First perform a topological sort (just a regular sort on literals)
        cube.sort();
        if reverse {
            cube.reverse();
        }

        // Calculate the effective activity weight based on frame decay
        // As frame number increases, we rely more on activity and less on topology
        let base_weight = 0.3; // Base weight for activity
        let frame_decay = 0.1; // Frame decay factor
        let effective_act_weight = (base_weight + frame_decay * frame as f64).min(1.0);
        
        // If weight is very small, just use topological sort (already done above)
        if effective_act_weight <= 0.05 {
            return;
        }
        
        // If weight is very large, just use activity-based sort
        if effective_act_weight >= 0.95 {
            self.sort_by_activity(cube, !reverse);
            return;
        }

        // Create a vector of (lit, score) pairs where score is a weighted combination
        // of topological position and activity
        let mut scored_lits: Vec<(Lit, f64)> = Vec::with_capacity(cube.len());
        
        for (idx, &lit) in cube.iter().enumerate() {
            // Normalize the index to 0.0-1.0 range
            let topo_score = if cube.len() > 1 {
                idx as f64 / (cube.len() - 1) as f64
            } else {
                0.0
            };
            
            // Normalize activity to 0.0-1.0 range (approximately)
            let act_score = self.activity[lit] / self.max_act;
            
            // Combine scores with appropriate weights
            let topo_weight = 1.0 - effective_act_weight;
            let combined_score = topo_weight * topo_score + effective_act_weight * act_score;
            
            scored_lits.push((lit, combined_score));
        }
        
        // Sort by combined score
        scored_lits.sort_by(|(_, score_a), (_, score_b)| {
            if reverse {
                score_a.partial_cmp(score_b).unwrap()
            } else {
                score_b.partial_cmp(score_a).unwrap()
            }
        });
        
        // Update the cube with the new ordering
        *cube = scored_lits.into_iter().map(|(lit, _)| lit).collect();
    }

    #[allow(unused)]
    pub fn cube_average_activity(&self, cube: &LitVec) -> f64 {
        let sum: f64 = cube.iter().map(|l| self.activity[*l]).sum();
        sum / cube.len() as f64
    }
}
