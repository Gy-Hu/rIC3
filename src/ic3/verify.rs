use super::{IC3, proofoblig::ProofObligation};
use crate::transys::{TransysCtx, TransysIf, unroll::TransysUnroll};
use cadical::Solver;
use logic_form::{Lemma, LitVec, Lit};
use satif::Satif;
use std::ops::Deref;
use std::fs::File;
use std::io::{Write, BufRead, BufReader};
use std::path::Path;
use giputils::hash::GHashMap;

pub fn verify_invariant(ts: &TransysCtx, invariants: &[Lemma]) -> bool {
    let mut solver = Solver::new();
    ts.load_trans(&mut solver, true);
    for lemma in invariants {
        let assump: LitVec = ts.init.iter().chain(lemma.iter()).copied().collect();
        if solver.solve(&assump) {
            return false;
        }
    }
    for lemma in invariants {
        solver.add_clause(&!lemma.deref());
    }
    if solver.solve(&ts.bad.cube()) {
        return false;
    }
    for lemma in invariants {
        if solver.solve(&ts.lits_next(lemma)) {
            return false;
        }
    }
    true
}

impl IC3 {
    pub fn verify(&mut self) {
        if !self.options.certify {
            return;
        }
        let invariants = self.frame.invariant();
        if !verify_invariant(&self.ts, &invariants) {
            panic!("invariant varify failed");
        }
        if self.options.verbose > 0 {
            println!(
                "inductive invariant verified with {} lemmas!",
                invariants.len()
            );
        }
    }
    
    // 单独处理导出逻辑，不依赖于certify选项
    pub fn dump_invariants_if_needed(&mut self) {
        // 如果设置了导出选项，导出归纳不变式
        if self.options.ic3.dump_inv || self.options.ic3_dump_inv_file != "inv.cnf" {
            let invariants = self.frame.invariant();
            self.dump_invariants(&invariants);
        }
    }

    // Feature 1: Export inductive invariants to file
    fn dump_invariants(&self, invariants: &[Lemma]) {
        let mut file = File::create(&self.options.ic3_dump_inv_file).expect(&format!("Unable to create {}", self.options.ic3_dump_inv_file));
        writeln!(&mut file, "{}", invariants.len()).expect("Failed to write to file");
        for clause in invariants.iter() {
            for lit in clause.cube().iter() {
                // 转换为AIGER变量编号 (通过restore映射)
                let aiger_lit = self.ts.restore(*lit);
                
                // 在AIGER格式中，变量编号是索引*2，负文字为奇数
                let aiger_var_id = (aiger_lit.var().0 * 2) as i32;
                let aiger_lit_id = if aiger_lit.polarity() { aiger_var_id } else { -aiger_var_id };
                
                write!(&mut file, "{} ", aiger_lit_id).expect("Failed to write to file");
            }
            writeln!(&mut file,"").expect("Failed to write to file");
        }
        
        if self.options.verbose > 0 {
            println!("Inductive invariants dumped to {} in AIGER variable numbering format", self.options.ic3_dump_inv_file);
        }
    }

    // Feature 2: Side-load clauses from file (with filtering)
    pub fn side_load_clauses(&mut self, filepath: &str) -> Result<usize, std::io::Error> {
        // 确保我们有至少2个帧 (0和1)
        if self.solvers.len() < 2 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput, 
                "Cannot load invariants - IC3 frames not initialized yet"
            ));
        }
        
        // 建立AIGER变量ID到内部变量的映射
        let mut aiger_to_internal = GHashMap::new();
        for latch in self.ts.latchs.iter() {
            if let Some(orig_var) = self.ts.restore.get(latch) {
                let aiger_var_id = (orig_var.0 * 2) as u32;
                aiger_to_internal.insert(aiger_var_id, *latch);
            }
        }
        for input in self.ts.inputs.iter() {
            if let Some(orig_var) = self.ts.restore.get(input) {
                let aiger_var_id = (orig_var.0 * 2) as u32;
                aiger_to_internal.insert(aiger_var_id, *input);
            }
        }
        
        let file = File::open(Path::new(filepath))?;
        let reader = BufReader::new(file);
        let mut lines = reader.lines();
        
        // Read the first line to get the number of clauses
        let num_clauses = lines
            .next()
            .ok_or(std::io::Error::new(std::io::ErrorKind::InvalidData, "Empty file"))?
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?
            .trim()
            .parse::<usize>()
            .map_err(|_| std::io::Error::new(std::io::ErrorKind::InvalidData, "Invalid clause count"))?;
        
        let mut loaded_count = 0;
        let mut skipped_count = 0;
        
        // Read each clause and add it to IC3
        for line in lines {
            let line = line.map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
            if line.trim().is_empty() {
                continue;
            }
            
            // Parse literals in the clause (AIGER format)
            let mut lits = LitVec::new();
            let mut valid_clause = true;
            
            for token in line.split_whitespace() {
                let aiger_lit_id: i32 = match token.parse() {
                    Ok(val) => val,
                    Err(_) => continue, // Skip invalid literals
                };
                
                // Extract AIGER变量ID和极性
                let aiger_var_id = (aiger_lit_id.abs() as u32); // 使用u32类型
                // 计算AIGER变量ID (确保是偶数)
                let aiger_var_id = aiger_var_id / 2 * 2;
                let polarity = aiger_lit_id > 0;
                
                // 转换为内部变量
                if let Some(internal_var) = aiger_to_internal.get(&aiger_var_id) {
                    let internal_lit = internal_var.lit().not_if(!polarity);
                    lits.push(internal_lit);
                } else {
                    // 如果找不到对应的内部变量，跳过这个子句
                    if self.options.verbose > 1 {
                        println!("Warning: AIGER variable {} not found in model, skipping clause", aiger_var_id);
                    }
                    valid_clause = false;
                    break;
                }
            }
            
            if !valid_clause {
                skipped_count += 1;
                continue;
            }
            
            // Filter logic: Check if the clause meets requirements
            if self.filter_clause(&lits) {
                // Add to IC3 framework (using frame level 1 and without containment check)
                self.add_lemma(1, lits, false, None);
                loaded_count += 1;
            } else {
                skipped_count += 1;
            }
        }
        
        if self.options.verbose > 0 {
            println!("Loaded {} clauses from {} (filtered/skipped {} from total {})", 
                     loaded_count, filepath, skipped_count, num_clauses);
            if loaded_count > 0 {
                println!("Added clauses will contribute to IC3 solving process");
            } else {
                println!("Warning: No clauses were loaded from {}. Possible reasons:", filepath);
                println!("  - All clauses were filtered out based on criteria");
                println!("  - The clauses referenced AIGER variables not found in model");
                println!("  - The file format is incorrect");
                println!("  - The file is empty");
                println!("IC3 will proceed with standard verification without external clauses.");
            }
        }
        
        Ok(loaded_count)
    }
    
    // Clause filtering function
    fn filter_clause(&self, lits: &LitVec) -> bool {
        // Filter logic example, can be adjusted according to actual requirements
        
        // 1. Clause length filtering
        if lits.is_empty() || lits.len() > self.options.ic3.max_clause_size {
            return false;
        }
        
        // 2. Filter out clauses that duplicate constraints already in abs_cst set
        for cst in self.abs_cst.iter() {
            if lits.iter().any(|lit| *lit == *cst) {
                return false;
            }
        }
        
        // 3. Check if the clause is compatible with the current state
        let mut solver = Solver::new();
        self.ts.load_trans(&mut solver, true);
        
        // Add known constraints
        for lemma in self.frame.invariant() {
            solver.add_clause(&lemma.deref());
        }
        
        // Check if the current clause conflicts with known constraints
        let negated_lits: LitVec = lits.iter().map(|l| !*l).collect();
        solver.add_clause(&negated_lits);
        if solver.solve(&[]) {
            return true; // Clause is compatible with current constraints
        } else {
            return false; // Clause conflicts with current constraints
        }
    }

    fn check_witness_with_constrain<S: Satif + ?Sized>(
        &mut self,
        solver: &mut S,
        uts: &TransysUnroll<TransysCtx>,
        constraint: &LitVec,
    ) -> bool {
        let mut assumps = LitVec::new();
        for k in 0..=uts.num_unroll {
            assumps.extend_from_slice(&uts.lits_next(constraint, k));
        }
        assumps.push(uts.lit_next(uts.ts.bad, uts.num_unroll));
        solver.solve(&assumps)
    }

    pub fn check_witness_by_bmc(&mut self, b: ProofObligation) -> Option<LitVec> {
        let mut uts = TransysUnroll::new(self.ts.deref());
        uts.unroll_to(b.depth);
        let mut solver: Box<dyn satif::Satif> = Box::new(cadical::Solver::new());
        for k in 0..=b.depth {
            uts.load_trans(solver.as_mut(), k, false);
        }
        uts.ts.load_init(solver.as_mut());
        let mut cst = uts.ts.constraints.clone();
        if self.check_witness_with_constrain(solver.as_mut(), &uts, &cst) {
            if self.options.verbose > 0 {
                println!("witness checking passed");
            }
            self.bmc_solver = Some((solver, uts));
            None
        } else {
            let mut i = 0;
            while i < cst.len() {
                if self.abs_cst.contains(&cst[i]) {
                    i += 1;
                    continue;
                }
                let mut drop = cst.clone();
                drop.remove(i);
                if self.check_witness_with_constrain(solver.as_mut(), &uts, &drop) {
                    i += 1;
                } else {
                    cst = drop;
                }
            }
            cst.retain(|l| !self.abs_cst.contains(l));
            assert!(!cst.is_empty());
            Some(cst)
        }
    }

    // 添加一个新函数用于显示AIGER和CNF变量之间的映射关系
    pub fn print_var_mapping(&self) {
        println!("\n=== AIGER to Internal Variable Mapping ===");
        
        // 打印状态变量映射
        println!("\nState Variables:");
        for latch in self.ts.latchs.iter() {
            if let Some(orig_var) = self.ts.restore.get(latch) {
                println!("Internal: {:<4} -> AIGER: {:>4} (AIGER ID: {})", 
                         latch, 
                         orig_var, 
                         orig_var.0 * 2);  // AIGER中的编号是变量索引*2
            }
        }
        
        // 打印输入变量映射
        println!("\nInput Variables:");
        for input in self.ts.inputs.iter() {
            if let Some(orig_var) = self.ts.restore.get(input) {
                println!("Internal: {:<4} -> AIGER: {:>4} (AIGER ID: {})", 
                         input, 
                         orig_var, 
                         orig_var.0 * 2);
            }
        }
        
        println!("\n=== Variable Format in Files ===");
        println!("- 使用AIGER变量ID (如26, 28, 30...)");
        println!("- 正文字直接使用变量ID (如26)");
        println!("- 负文字使用负数 (如-26)");
        println!("- inv.cnf文件现在使用AIGER变量ID而非内部变量ID");
        println!("=============================================\n");
    }
}
