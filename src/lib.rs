#![feature(assert_matches, is_sorted, get_mut_unchecked, format_args_nl)]

mod activity;
mod command;
mod mic;
mod proofoblig;
mod solver;
mod statistic;
mod verify;

use crate::proofoblig::{ProofObligation, ProofObligationQueue};
use crate::statistic::Statistic;
use activity::Activity;
use aig::Aig;
pub use command::Args;
use gipsat::{BlockResult, BlockResultYes, GipSAT};
use logic_form::{Cube, Lemma};
use solver::Lift;
use std::panic::{self, AssertUnwindSafe};
use std::process::exit;
use std::time::Instant;
use transys::Model;

pub struct Ic3 {
    args: Args,
    model: Model,
    gipsat: GipSAT,
    activity: Activity,
    obligations: ProofObligationQueue,
    lift: Lift,
    statistic: Statistic,
}

impl Ic3 {
    pub fn depth(&self) -> usize {
        self.gipsat.depth()
    }

    fn new_frame(&mut self) {
        self.gipsat.new_frame();
    }

    fn generalize(&mut self, frame: usize, cube: Cube) -> (usize, Cube) {
        // let level = if self.args.ctg { 1 } else { 0 };
        let mut cube = self.mic(frame, cube, 0);
        for i in frame + 1..=self.depth() {
            match self.gipsat.blocked(i, &cube, true, true) {
                BlockResult::Yes(block) => cube = self.gipsat.blocked_conflict(block),
                BlockResult::No(_) => return (i, cube),
            }
        }
        (self.depth() + 1, cube)
    }

    fn handle_blocked(&mut self, po: ProofObligation, blocked: BlockResultYes) {
        let conflict = self.gipsat.blocked_conflict(blocked);
        let (frame, core) = self.generalize(po.frame, conflict);
        self.statistic.avg_po_cube_len += po.lemma.len();
        self.add_obligation(ProofObligation::new(frame, po.lemma, po.depth));
        self.gipsat.add_lemma(frame - 1, core);
    }

    fn block(&mut self) -> bool {
        while let Some(po) = self.obligations.pop(self.depth()) {
            if po.frame == 0 {
                return false;
            }
            assert!(!self.model.cube_subsume_init(&po.lemma));
            if self.args.verbose_all {
                self.statistic();
            }
            if self.gipsat.trivial_contained(po.frame, &po.lemma) {
                self.add_obligation(ProofObligation::new(po.frame + 1, po.lemma, po.depth));
                continue;
            }
            match self.blocked_with_ordered(po.frame, &po.lemma, false, true, false) {
                BlockResult::Yes(blocked) => {
                    self.handle_blocked(po, blocked);
                }
                BlockResult::No(unblocked) => {
                    let model = self.unblocked_model(unblocked);
                    self.add_obligation(ProofObligation::new(
                        po.frame - 1,
                        Lemma::new(model),
                        po.depth + 1,
                    ));
                    self.add_obligation(po);
                }
            }
        }
        true
    }
}

impl Ic3 {
    pub fn new(args: Args) -> Self {
        let aig = Aig::from_file(args.model.as_ref().unwrap()).unwrap();
        let model = Model::from_aig(&aig);
        let lift = Lift::new(&model);
        let statistic = Statistic::new(args.model.as_ref().unwrap());
        let activity = Activity::new(&model.latchs);
        let gipsat = GipSAT::new(model.clone());
        let mut res = Self {
            args,
            model,
            activity,
            gipsat,
            lift,
            statistic,
            obligations: ProofObligationQueue::new(),
        };
        res.new_frame();
        for cube in res.model.inits() {
            res.gipsat.add_lemma(0, cube)
        }
        res
    }

    pub fn check(&mut self) -> bool {
        loop {
            let start = Instant::now();
            loop {
                if !self.block() {
                    self.statistic.overall_block_time += start.elapsed();
                    self.statistic();
                    return false;
                }
                if let Some(bad) = self.gipsat.get_bad() {
                    let bad = self.unblocked_model(bad);
                    self.add_obligation(ProofObligation::new(self.depth(), Lemma::new(bad), 0))
                } else {
                    break;
                }
            }
            let blocked_time = start.elapsed();
            if self.args.verbose {
                println!(
                    "[{}:{}] frame: {}, time: {:?}",
                    file!(),
                    line!(),
                    self.depth(),
                    blocked_time,
                );
            }
            self.statistic.overall_block_time += blocked_time;
            self.new_frame();
            let start = Instant::now();
            let propagate = self.gipsat.propagate();
            self.statistic.overall_propagate_time += start.elapsed();
            if propagate {
                self.statistic();
                if self.args.verify {
                    assert!(self.verify());
                }
                return true;
            }
        }
    }

    pub fn check_with_int_hanlder(&mut self) -> bool {
        let ic3 = self as *mut Ic3 as usize;
        ctrlc::set_handler(move || {
            let ic3 = unsafe { &mut *(ic3 as *mut Ic3) };
            ic3.statistic();
            exit(130);
        })
        .unwrap();
        panic::catch_unwind(AssertUnwindSafe(|| self.check())).unwrap_or_else(|_| {
            self.statistic();
            panic!();
        })
    }
}
