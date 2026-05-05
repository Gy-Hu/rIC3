use logic_form::{Lit, Var};
use satif::Satif;
use std::{
    ffi::{CString, c_char, c_int, c_void},
    sync::mpsc::channel,
    thread::spawn,
    time::Duration,
};

unsafe extern "C" {
    fn kissat_init() -> *mut c_void;
    fn kissat_release(s: *mut c_void);
    fn kissat_add(s: *mut c_void, lit: c_int);
    fn kissat_solve(s: *mut c_void) -> c_int;
    fn kissat_value(s: *mut c_void, lit: c_int) -> c_int;
    fn kissat_set_option(s: *mut c_void, op: *mut c_char, v: c_int) -> c_int;
    fn kissat_terminate(s: *mut c_void);
}

fn lit_to_kissat_lit(lit: &Lit) -> i32 {
    let mut res = Into::<usize>::into(lit.var()) as i32 + 1;
    if !lit.polarity() {
        res = -res;
    }
    res
}

#[allow(unused)]
fn kissat_lit_to_lit(lit: i32) -> Lit {
    let p = lit > 0;
    let v = Var::new(lit.unsigned_abs() as usize - 1);
    Lit::new(v, p)
}

pub struct Solver {
    solver: *mut c_void,
    num_var: usize,
}

impl Solver {
    pub fn new() -> Self {
        let solver = unsafe { kissat_init() };
        #[allow(dangling_pointers_from_temporaries)]
        unsafe {
            kissat_set_option(solver, CString::new("quiet").unwrap().as_ptr() as *mut _, 1)
        };
        Self { solver, num_var: 0 }
    }
}

impl Satif for Solver {
    #[inline]
    fn new_var(&mut self) -> Var {
        self.num_var += 1;
        Var::new(self.num_var - 1)
    }

    #[inline]
    fn num_var(&self) -> usize {
        self.num_var
    }

    #[inline]
    fn add_clause(&mut self, clause: &[Lit]) {
        for lit in clause.iter().map(lit_to_kissat_lit) {
            unsafe { kissat_add(self.solver, lit) };
        }
        unsafe { kissat_add(self.solver, 0) };
    }

    fn solve(&mut self, assumps: &[Lit]) -> bool {
        if !assumps.is_empty() {
            panic!("unsupport assumption");
        }
        match unsafe { kissat_solve(self.solver) } {
            10 => true,
            20 => false,
            _ => unreachable!(),
        }
    }

    fn solve_with_limit(&mut self, assumps: &[Lit], limit: Duration) -> Option<bool> {
        if !assumps.is_empty() {
            panic!("unsupport assumption");
        }
        let solver = self.solver as usize;
        let (tx, rx) = channel();
        let join = spawn(move || {
            tx.send(unsafe { kissat_solve(solver as *mut c_void) })
                .unwrap()
        });
        match rx.recv_timeout(limit) {
            Ok(10) => Some(true),
            Ok(20) => Some(false),
            Err(_) => {
                self.terminate();
                join.join().unwrap();
                None
            }
            _ => unreachable!(),
        }
    }

    fn sat_value(&self, lit: Lit) -> Option<bool> {
        let lit = lit_to_kissat_lit(&lit);
        let res = unsafe { kissat_value(self.solver, lit) };
        if res == lit {
            Some(true)
        } else if res == -lit {
            Some(false)
        } else {
            None
        }
    }
}

impl Solver {
    pub fn terminate(&mut self) {
        unsafe { kissat_terminate(self.solver) }
    }
}

impl Drop for Solver {
    fn drop(&mut self) {
        unsafe { kissat_release(self.solver) }
    }
}

impl Default for Solver {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Sync for Solver {}

unsafe impl Send for Solver {}

#[test]
fn test() {
    use logic_form::LitVec;
    let mut solver = Solver::new();
    let lit0: Lit = solver.new_var().into();
    let lit1: Lit = solver.new_var().into();
    let lit2: Lit = solver.new_var().into();
    solver.add_clause(&LitVec::from([lit0, !lit2]));
    solver.add_clause(&LitVec::from([lit1, !lit2]));
    solver.add_clause(&LitVec::from([!lit0, !lit1, lit2]));
    solver.add_clause(&LitVec::from([lit2]));
    if solver.solve(&[]) {
        assert!(solver.sat_value(lit0).unwrap());
        assert!(solver.sat_value(lit1).unwrap());
        assert!(solver.sat_value(lit2).unwrap());
    } else {
        panic!()
    }
}
