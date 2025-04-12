use logic_form::Var;
use std::{collections::HashMap, fs::File, io::BufReader, path::Path};
use serde::{Deserialize, Serialize};
use aig::aigsim_ffi;

#[derive(Debug, Deserialize, Serialize)]
pub struct FlipRateData {
    pub flip_rates: HashMap<String, u32>,
    pub metadata: FlipRateMetadata,
}

#[derive(Debug, Deserialize, Serialize)]
pub struct FlipRateMetadata {
    pub total_cycles: u32,
    pub num_seeds: u32,
    pub num_latches: u32,
}

#[derive(Debug, Clone)]
pub struct FlipRateManager {
    // Maps variable ID to flip rate percentage (0-100)
    flip_rates: HashMap<Var, u32>,
    loaded: bool,
}

impl FlipRateManager {
    pub fn new() -> Self {
        Self {
            flip_rates: HashMap::new(),
            loaded: false,
        }
    }
    
    /// Calculate flip rates directly from an Aig model using FFI
    pub fn calculate_from_model(&mut self, aig_path: &Path, vectors: u32, seeds: u32) -> Result<(), String> {
        // Call FFI function to calculate flip rates
        let flip_rates = aigsim_ffi::calculate_flip_rates(
            aig_path, 
            vectors, 
            seeds
        )?;
        
        // Convert results to our format
        for (var_id, rate) in flip_rates {
            self.flip_rates.insert(Var::from(var_id / 2), rate);
        }
        
        self.loaded = true;
        Ok(())
    }

    /// Load flip rate data from a JSON file
    pub fn load_from_file<P: AsRef<Path>>(&mut self, path: P) -> Result<(), String> {
        let file = File::open(path).map_err(|e| format!("Failed to open flip rate file: {}", e))?;
        let reader = BufReader::new(file);
        
        let data: FlipRateData = serde_json::from_reader(reader)
            .map_err(|e| format!("Failed to parse flip rate JSON data: {}", e))?;
        
        // Convert string keys to Var
        for (key_str, rate) in data.flip_rates {
            if let Ok(var_id) = key_str.parse::<u32>() {
                self.flip_rates.insert(Var::from(var_id), rate);
            }
        }
        
        self.loaded = true;
        Ok(())
    }
    
    /// Get the flip rate for a variable, returns None if not found
    pub fn get_flip_rate(&self, var: Var) -> Option<u32> {
        self.flip_rates.get(&var).copied()
    }
    
    /// Check if flip rate data is loaded
    pub fn is_loaded(&self) -> bool {
        self.loaded
    }
    
    /// Sort the literals by flip rate in ascending or descending order
    pub fn sort_by_flip_rate(&self, cube: &mut logic_form::LitVec, high_to_low: bool) {
        if !self.loaded {
            return; // Don't sort if data isn't loaded
        }
        
        if high_to_low {
            // Sort from high flip rate to low flip rate
            cube.sort_by(|a, b| {
                let a_rate = self.get_flip_rate(a.var()).unwrap_or(0);
                let b_rate = self.get_flip_rate(b.var()).unwrap_or(0);
                b_rate.cmp(&a_rate)
            });
        } else {
            // Sort from low flip rate to high flip rate
            cube.sort_by(|a, b| {
                let a_rate = self.get_flip_rate(a.var()).unwrap_or(0);
                let b_rate = self.get_flip_rate(b.var()).unwrap_or(0);
                a_rate.cmp(&b_rate)
            });
        }
    }
}
