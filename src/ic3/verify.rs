use super::{IC3, proofoblig::ProofObligation};
use crate::transys::{TransysCtx, TransysIf, unroll::TransysUnroll};
use cadical::Solver;
use logic_form::{Lemma, LitVec};
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
    
    // Handle export logic separately, not dependent on the certify option
    pub fn dump_invariants_if_needed(&mut self) {
        // Export inductive invariants if the export option is set
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
                // Convert to AIGER variable numbers (through restore mapping)
                let aiger_lit = self.ts.restore(*lit);
                
                // In AIGER format, variable numbers are index*2, negative literals are odd
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
        // Ensure we have at least 2 frames (0 and 1)
        if self.solvers.len() < 2 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput, 
                "Cannot load invariants - IC3 frames not initialized yet"
            ));
        }
        
        // Establish AIGER variable ID to internal variable mapping
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
                
                // Extract AIGER variable ID and polarity
                let aiger_var_id = aiger_lit_id.abs() as u32; // Use u32 type
                // Calculate AIGER variable ID (ensure it's even)
                let aiger_var_id = aiger_var_id / 2 * 2;
                let polarity = aiger_lit_id > 0;
                
                // Convert to internal variable
                if let Some(internal_var) = aiger_to_internal.get(&aiger_var_id) {
                    let internal_lit = internal_var.lit().not_if(!polarity);
                    lits.push(internal_lit);
                } else {
                    // Skip this clause if the corresponding internal variable cannot be found
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

    // Add a new function to display the mapping between AIGER and CNF variables
    pub fn print_var_mapping(&self) {
        println!("\n=== AIGER to Internal Variable Mapping ===");
        
        // Print state variable mappings
        println!("\nState Variables:");
        for latch in self.ts.latchs.iter() {
            if let Some(orig_var) = self.ts.restore.get(latch) {
                println!("Internal: {:<4} -> AIGER: {:>4} (AIGER ID: {})", 
                         latch, 
                         orig_var, 
                         orig_var.0 * 2);  // In AIGER, variable numbers are index*2
            }
        }
        
        // Print input variable mappings
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
        println!("- Using AIGER variable IDs (e.g., 26, 28, 30...)");
        println!("- Positive literals use the variable ID directly (e.g., 26)");
        println!("- Negative literals use negative numbers (e.g., -26)");
        println!("- inv.cnf file now uses AIGER variable IDs instead of internal variable IDs");
        println!("=============================================\n");
    }

    // Feature 3: CTI Sampling - Implement CTI (Counterexample To Induction) sampling functionality
    pub fn sample_cti(&mut self, sample_count: usize, reduce_samples: bool) -> Result<usize, std::io::Error> {
        use std::fs::File;
        use std::io::Write;
        use std::collections::HashSet;
        use std::time::Instant;

        // Make sure we have at least the first frame set up
        if self.solvers.len() < 1 {
            self.extend(); // Create initial frame if needed
        }

        // Create a solver for CTI sampling
        let mut solver = cadical::Solver::new();
        self.ts.load_trans(&mut solver, true);
        
        // Setup Not-Property constraint for next state
        // P /\ T /\ !P'
        // First, add P (property is false)
        solver.add_clause(&self.ts.bad.cube());
        
        // We need !P' (property is true in next state)
        // Get the primed version of the property
        let next_bad = self.ts.lits_next(&self.ts.bad.cube());
        let not_next_bad: LitVec = next_bad.iter().map(|l| !*l).collect();
        
        // Add the negated property in next state
        solver.add_clause(&not_next_bad);
        
        let start_time = Instant::now();
        let mut file = File::create(&self.options.ic3.cti_sample_file)?;
        let mut samples_collected = 0;
        let mut unique_samples = HashSet::new();
        let mut retry_count = 0;
        const MAX_RETRIES: usize = 1000; // To prevent infinite loops
        
        // Header information
        writeln!(&mut file, "# CTI Samples for model: {}", self.options.model.display())?;
        writeln!(&mut file, "# Format: Each line contains one state cube (conjunction of literals)")?;
        writeln!(&mut file, "# Each sample is a state s where s /\\ T /\\ !P' is satisfiable")?;
        writeln!(&mut file, "# Total samples requested: {}", sample_count)?;
        writeln!(&mut file, "# Reduction enabled: {}", reduce_samples)?;
        writeln!(&mut file, "# Literals inverted: {}", self.options.ic3.cti_invert)?;
        writeln!(&mut file, "# ===================================")?;
        
        let mut accumulated_lits = 0;
        while samples_collected < sample_count && retry_count < MAX_RETRIES {
            // Check if the formula is satisfiable
            if !solver.solve(&[]) {
                // If we can't find any more samples, break out
                if self.options.verbose > 0 {
                    println!("No more CTI samples can be found - formula became UNSAT after {} samples", samples_collected);
                }
                break;
            }
            
            // Extract state literals from model
            let mut state_lits = LitVec::new();
            for latch in self.ts.latchs.iter() {
                let lit = latch.lit();
                if let Some(v) = solver.sat_value(lit) {
                    state_lits.push(lit.not_if(!v));
                }
            }
            
            // If sample reduction is enabled, reduce the sample
            if reduce_samples {
                state_lits = self.reduce_cti_sample(&state_lits, &next_bad);
            }
            
            // Check if this sample is unique (to avoid duplicates)
            let sample_str = format!("{:?}", state_lits);
            if unique_samples.contains(&sample_str) {
                retry_count += 1;
                // Add blocking clause to prevent this exact model from being found again
                let block_clause: LitVec = state_lits.iter().map(|l| !*l).collect();
                solver.add_clause(&block_clause);
                continue;
            }
            
            // Record the unique sample
            unique_samples.insert(sample_str);
            samples_collected += 1;
            accumulated_lits += state_lits.len();
            retry_count = 0;
            
            // Write sample to file
            for lit in &state_lits {
                // Convert to AIGER-compatible variable numbering
                if let Some(orig_var) = self.ts.restore.get(&lit.var()) {
                    let aiger_var_id = (orig_var.0 * 2) as i32;
                    let mut aiger_lit_id = if lit.polarity() { aiger_var_id } else { -aiger_var_id };
                    
                    // If inversion option is enabled, invert the literal
                    if self.options.ic3.cti_invert {
                        aiger_lit_id = -aiger_lit_id;
                    }
                    
                    write!(&mut file, "{} ", aiger_lit_id)?;
                }
            }
            writeln!(&mut file)?;
            
            // Block this state to find the next unique CTI
            let block_clause: LitVec = state_lits.iter().map(|l| !*l).collect();
            solver.add_clause(&block_clause);
        }
        
        let elapsed = start_time.elapsed();
        let avg_lits_per_sample = if samples_collected > 0 { accumulated_lits as f64 / samples_collected as f64 } else { 0.0 };
        
        // Write summary footer
        writeln!(&mut file, "# ===================================")?;
        writeln!(&mut file, "# Sampling completed in {:.2?}", elapsed)?;
        writeln!(&mut file, "# Total samples collected: {}", samples_collected)?;
        writeln!(&mut file, "# Average literals per sample: {:.2}", avg_lits_per_sample)?;
        
        if self.options.verbose > 0 {
            println!("CTI sampling complete: Collected {} samples in {:.2?}", samples_collected, elapsed);
            println!("Average literals per sample: {:.2}", avg_lits_per_sample);
            println!("Samples saved to {}", self.options.ic3.cti_sample_file);
        }
        
        Ok(samples_collected)
    }
    
    // Helper method to reduce CTI samples by removing literals that aren't necessary
    // This is similar to ternary simulation in the example code's reduce_vars method
    fn reduce_cti_sample(&self, state_lits: &LitVec, next_prop: &LitVec) -> LitVec {
        use std::collections::HashSet;
        
        // If no literals to reduce, return as is
        if state_lits.is_empty() {
            return state_lits.clone();
        }
        
        // Create a new solver for reduction
        let mut red_solver = cadical::Solver::new();
        self.ts.load_trans(&mut red_solver, true);
        
        // Add requirement that next_prop must be satisfied
        for lit in next_prop {
            red_solver.add_clause(&[*lit]);
        }
        
        // Create a hash set for quick lookups
        let mut necessary_lits = HashSet::new();
        
        // Try removing each literal one by one
        for (i, lit) in state_lits.iter().enumerate() {
            // Create a candidate cube without the current literal
            let mut assumps = Vec::new();
            for (j, other_lit) in state_lits.iter().enumerate() {
                if i != j {
                    assumps.push(*other_lit);
                }
            }
            
            // Check if removing this literal still gives us a valid CTI
            if !red_solver.solve(&assumps) {
                // If unsatisfiable, this literal is necessary
                necessary_lits.insert(*lit);
            }
        }
        
        // Rebuild the reduced state as a Vec in the original order
        state_lits.iter()
            .filter(|lit| necessary_lits.contains(lit))
            .cloned()
            .collect()
    }
}
