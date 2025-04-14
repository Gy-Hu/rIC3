use std::collections::HashMap;
use std::ffi::{c_char, c_int, CString};
use std::path::Path;
use std::ptr;

// Define FFI interface for C functions
#[link(name = "aiger", kind = "static")]
unsafe extern "C" {
    // These functions will be implemented in the modified aigsim.c
    fn aigsim_calculate_flip_rates(
        model_path: *const c_char,
        vectors: c_int,
        seeds: c_int,
        results: *mut *mut FlipRateResult,
        num_results: *mut c_int,
    ) -> c_int;

    fn aigsim_free_results(results: *mut FlipRateResult, num_results: c_int);
}

// C struct for receiving flip rate calculation results
#[repr(C)]
pub struct FlipRateResult {
    var_id: u32,
    flip_rate: u32,
}

/// Calculate flip rates for latches in an Aiger model
/// 
/// - `aiger_path`: Path to the Aiger model file
/// - `vectors`: Number of simulation vectors per seed
/// - `seeds`: Number of random seeds to use
///
/// Returns a HashMap mapping variable IDs to their flip rates (0-100 percentage)
pub fn calculate_flip_rates(
    aiger_path: impl AsRef<Path>,
    vectors: u32,
    seeds: u32,
) -> Result<HashMap<u32, u32>, String> {
    let path_str = aiger_path.as_ref().to_str()
        .ok_or_else(|| "Aiger path contains invalid UTF-8".to_string())?;

    unsafe {
        // Prepare FFI call parameters
        let path_c_str = CString::new(path_str).expect("Invalid path string");
        let mut results_ptr: *mut FlipRateResult = ptr::null_mut();
        let mut num_results: c_int = 0;

        // Call C function
        let status = aigsim_calculate_flip_rates(
            path_c_str.as_ptr(),
            vectors as c_int,
            seeds as c_int,
            &mut results_ptr,
            &mut num_results,
        );

        if status != 0 {
            return Err(format!("Failed to calculate flip rates, error code: {}", status));
        }

        // Convert C struct array to Rust HashMap
        let mut flip_rates = HashMap::new();
        let results_slice = std::slice::from_raw_parts(results_ptr, num_results as usize);

        for result in results_slice {
            flip_rates.insert(result.var_id, result.flip_rate);
        }

        // Free memory allocated by C
        aigsim_free_results(results_ptr, num_results);

        Ok(flip_rates)
    }
}
