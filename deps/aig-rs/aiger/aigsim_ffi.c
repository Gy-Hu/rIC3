/***************************************************************************
 * FFI extension for aigsim.c to be used from Rust via FFI
 ***************************************************************************/

#include "aiger.h"
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <assert.h>

// Struct definition for flip rate results
typedef struct FlipRateResult {
    unsigned int var_id;
    unsigned int flip_rate;
} FlipRateResult;

// Implementation of deref function
static unsigned char deref(unsigned lit, unsigned char* current) {
    unsigned res = current[lit >> 1];
    res ^= lit & 1;
    return res;
}
static void die(const char *fmt, ...);

// Calculate flip rates for latches in an Aiger model
int aigsim_calculate_flip_rates(
    const char* model_path,
    int vectors,
    int seeds,
    FlipRateResult** results,
    int* num_results
) {
    // Initialize aiger model
    aiger* model = aiger_init();
    const char* error = aiger_open_and_read_from_file(model, model_path);
    
    if (error) {
        aiger_reset(model);
        return 1; // Return error code
    }
    
    // Allocate latch flip rate counter
    unsigned int* latch_ones = calloc(model->num_latches, sizeof(unsigned int));
    if (!latch_ones) {
        aiger_reset(model);
        return 2; // Memory allocation failed
    }
    
    // Allocate current and next state vectors
    unsigned char* current = calloc(model->maxvar + 1, sizeof(unsigned char));
    unsigned char* next = calloc(model->num_latches, sizeof(unsigned char));
    
    if (!current || !next) {
        free(latch_ones);
        free(current);
        free(next);
        aiger_reset(model);
        return 2; // Memory allocation failed
    }
    
    // Set initial state
    for (unsigned j = 0; j < model->num_latches; j++) {
        aiger_symbol* symbol = model->latches + j;
        current[symbol->lit / 2] = (symbol->reset <= 1) ? symbol->reset : 0;
    }
    
    // Set random seed
    srand(0); // Use default seed, or pass as parameter
    
    unsigned int total_cycles = 0;
    unsigned int vectors_per_run = vectors;
    
    // Main simulation loop
    for (int seed_run = 0; seed_run < seeds; seed_run++) {
        if (seeds > 1) {
            srand(seed_run);
            
            // Reset latch states
            for (unsigned j = 0; j < model->num_latches; j++) {
                aiger_symbol* symbol = model->latches + j;
                current[symbol->lit / 2] = (symbol->reset <= 1) ? symbol->reset : 0;
            }
        }
        
        // Run specified number of simulation vectors
        for (int v = 0; v < vectors_per_run; v++) {
            // Set random inputs
            for (unsigned j = 1; j <= model->num_inputs; j++) {
                unsigned s = 17 * j + v;
                s %= 20;
                unsigned tmp = rand() >> s;
                tmp %= 2; // Binary simulation
                current[j] = tmp;
            }
            
            // Simulate AND gates
            for (unsigned j = 0; j < model->num_ands; j++) {
                aiger_and* and_gate = model->ands + j;
                unsigned l = deref(and_gate->rhs0, current);
                unsigned r = deref(and_gate->rhs1, current);
                current[and_gate->lhs / 2] = l & r;
            }
            
            // Calculate next state
            for (unsigned j = 0; j < model->num_latches; j++) {
                aiger_symbol* symbol = model->latches + j;
                next[j] = deref(symbol->next, current);
            }
            
            // Update state and count
            for (unsigned j = 0; j < model->num_latches; j++) {
                aiger_symbol* symbol = model->latches + j;
                current[symbol->lit / 2] = next[j];
                
                // Count instances of latch value 1
                if (next[j] == 1) {
                    latch_ones[j]++;
                }
            }
            
            total_cycles++;
        }
    }
    
    // Allocate result array
    *num_results = model->num_latches;
    *results = (FlipRateResult*)malloc(*num_results * sizeof(FlipRateResult));
    
    if (!*results) {
        free(latch_ones);
        free(current);
        free(next);
        aiger_reset(model);
        return 2; // Memory allocation failed
    }
    
    // Fill result array
    for (unsigned j = 0; j < model->num_latches; j++) {
        (*results)[j].var_id = model->latches[j].lit;
        // Calculate flip rate (percentage)
        (*results)[j].flip_rate = (total_cycles > 0) ? 
            (latch_ones[j] * 100 / total_cycles) : 0;
    }
    
    // Cleanup
    free(latch_ones);
    free(current);
    free(next);
    aiger_reset(model);
    
    return 0; // Success
}

// Free result array
void aigsim_free_results(FlipRateResult* results, int num_results) {
    if (results) {
        free(results);
    }
}
