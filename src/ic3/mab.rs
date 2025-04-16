use crate::ic3::statistic::Statistic;
use rand::prelude::*;
use rand::thread_rng;
use std::time::Duration;
use std::fmt::Debug;
use std::collections::HashMap;
use giputils::statistic::{SuccessRate, Average};

// Define the different ordering types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OrderingStrategy {
    DefaultActivity,     // Default act ordering
    TopoSort,            // ic3-topo-sort 
    ReverseSort,         // ic3-reverse-sort
    FlipRateSort,        // ic3-flip-rate-sort
    HighFlipRateFirst,   // ic3-high-flip-rate-first
}

impl OrderingStrategy {
    // Get all strategies as an array
    pub fn all() -> [OrderingStrategy; 5] {
        [
            OrderingStrategy::DefaultActivity,
            OrderingStrategy::TopoSort,
            OrderingStrategy::ReverseSort,
            OrderingStrategy::FlipRateSort,
            OrderingStrategy::HighFlipRateFirst,
        ]
    }

    // Convert a strategy to the corresponding option settings
    pub fn to_options(&self) -> (bool, bool, bool, bool) {
        match self {
            OrderingStrategy::DefaultActivity => (false, false, false, false),
            OrderingStrategy::TopoSort => (true, false, false, false),
            OrderingStrategy::ReverseSort => (true, true, false, false),
            OrderingStrategy::FlipRateSort => (false, false, true, false),
            OrderingStrategy::HighFlipRateFirst => (false, false, true, true),
        }
    }
}

// Contextual Multi-Armed Bandit implementation with adaptive strategy selection
pub struct ContextualMAB {
    strategies: Vec<OrderingStrategy>,
    // Map of [phase][strategy_index] -> vec of rewards (sliding window)
    context_rewards: HashMap<SolverPhase, Vec<Vec<f64>>>,
    window_size: usize,               // Size of sliding window
    pub exploration_rate: f64,        // Epsilon for exploration
    exploration_decay: f64,           // Decay rate for exploration
    min_exploration_rate: f64,        // Minimum exploration rate
    pub last_selected: Option<(SolverPhase, OrderingStrategy)>, // Last (context, strategy) pair
    rng: ThreadRng,                   // Random number generator
    // For contextual linear models (LinUCB): feature weights for each strategy
    weights: Vec<Vec<f64>>,           // [strategy_index][feature_index] -> weight
    alpha: f64,                       // Exploration parameter for LinUCB
}

impl ContextualMAB {
    pub fn new(window_size: usize, exploration_rate: f64, exploration_decay: f64, min_exploration_rate: f64) -> Self {
        let strategies = OrderingStrategy::all().to_vec();
        let num_strategies = strategies.len();
        
        // Initialize context reward storage for each phase
        let mut context_rewards = HashMap::new();
        for phase in [SolverPhase::Early, SolverPhase::Middle, SolverPhase::Late].iter() {
            context_rewards.insert(*phase, vec![Vec::with_capacity(window_size); num_strategies]);
        }
        
        // Number of features used in contextual model
        let num_features = 4; // [phase_early, phase_middle, phase_late, mic_success_rate]
        
        Self {
            strategies,
            context_rewards,
            window_size,
            exploration_rate,
            exploration_decay,
            min_exploration_rate,
            last_selected: None,
            rng: thread_rng(),
            weights: vec![vec![0.0; num_features]; num_strategies],
            alpha: 0.1, // Exploration parameter for LinUCB
        }
    }

    // Extract contextual features for the current state
    fn extract_features(&self, phase: SolverPhase, statistic: &Statistic) -> Vec<f64> {
        let mut features = vec![0.0; 4];
        
        // One-hot encoding of phase
        match phase {
            SolverPhase::Early => features[0] = 1.0,
            SolverPhase::Middle => features[1] = 1.0,
            SolverPhase::Late => features[2] = 1.0,
        }
        
        // Add normalized MIC success rate as a feature
        features[3] = Self::parse_success_rate(&statistic.mic_drop);
        
        features
    }
    
    // Select a strategy using contextual bandit algorithm
    pub fn select(&mut self, phase: SolverPhase, statistic: &Statistic) -> OrderingStrategy {
        // Extract features before any mutable borrowing
        let features = self.extract_features(phase, statistic);
        
        // Standard exploration with probability epsilon
        if self.rng.random::<f64>() < self.exploration_rate {
            let index = self.rng.random_range(0..self.strategies.len());
            self.last_selected = Some((phase, self.strategies[index]));
            return self.strategies[index];
        }
        
        // Create rewards vector if it doesn't exist yet
        if !self.context_rewards.contains_key(&phase) {
            self.context_rewards.insert(phase, vec![Vec::with_capacity(self.window_size); self.strategies.len()]);
        }
        
        // Clone the reward data to avoid borrow issues
        let rewards_data = self.context_rewards.get(&phase)
            .unwrap()
            .clone();
        
        // Check if we need to use simple averages due to insufficient data
        let use_simple_averages = rewards_data.iter().any(|r| r.is_empty());
        
        let best_index = if use_simple_averages {
            // Use simple average rewards if we don't have enough data
            let mut best_i = 0;
            let mut best_value = f64::NEG_INFINITY;

            for (i, strategy_rewards) in rewards_data.iter().enumerate() {
                if strategy_rewards.is_empty() {
                    // If no rewards yet for this strategy in this context, prioritize it
                    self.last_selected = Some((phase, self.strategies[i]));
                    return self.strategies[i];
                }

                let avg_reward = strategy_rewards.iter().sum::<f64>() / strategy_rewards.len() as f64;
                if avg_reward > best_value {
                    best_value = avg_reward;
                    best_i = i;
                }
            }
            best_i
        } else {
            // Use LinUCB algorithm with context features
            let mut best_i = 0;
            let mut best_ucb = f64::NEG_INFINITY;
            
            for (i, strategy_weights) in self.weights.iter().enumerate() {
                // Calculate expected reward using linear model
                let expected_reward = strategy_weights.iter().zip(features.iter())
                    .map(|(w, f)| w * f)
                    .sum::<f64>();
                
                // Add exploration bonus (simplified LinUCB formula)
                let exploration_bonus = self.alpha * (rewards_data[i].len() as f64 + 1.0).sqrt();
                let ucb = expected_reward + exploration_bonus;
                
                if ucb > best_ucb {
                    best_ucb = ucb;
                    best_i = i;
                }
            }
            best_i
        };
        
        self.last_selected = Some((phase, self.strategies[best_index]));
        self.strategies[best_index]
    }

    // Update the reward for the last selected strategy and context
    pub fn update(&mut self, reward: f64, statistic: &Statistic) {
        if let Some((phase, strategy)) = self.last_selected {
            let strategy_index = self.strategies.iter().position(|&s| s == strategy).unwrap();
            
            // Get context-specific rewards
            let phase_rewards = self.context_rewards.entry(phase)
                .or_insert_with(|| vec![Vec::with_capacity(self.window_size); self.strategies.len()]);
            
            // Add reward to the window
            if phase_rewards[strategy_index].len() >= self.window_size {
                phase_rewards[strategy_index].remove(0); // Remove oldest reward
            }
            phase_rewards[strategy_index].push(reward);
            
            // Update weights for the linear model
            if phase_rewards[strategy_index].len() >= 3 { // Only update after collecting some data
                let features = self.extract_features(phase, statistic);
                
                // Simple online gradient descent update
                let learning_rate = 0.1;
                let expected = self.weights[strategy_index].iter().zip(features.iter())
                    .map(|(w, f)| w * f)
                    .sum::<f64>();
                
                // Update weights based on prediction error
                let error = reward - expected;
                for (weight, &feature) in self.weights[strategy_index].iter_mut().zip(features.iter()) {
                    *weight += learning_rate * error * feature;
                }
            }

            // Decay exploration rate
            self.exploration_rate = (self.exploration_rate * self.exploration_decay)
                .max(self.min_exploration_rate);
        }
    }

    // Extract success rate from a SuccessRate's debug output
    fn parse_success_rate(sr: &SuccessRate) -> f64 {
        let debug_str = format!("{:?}", sr);
        // Parse success rate from format like "success: 123, fail: 456, success rate: 21.32%"
        if let Some(rate_part) = debug_str.split("success rate:").nth(1) {
            if let Some(percentage) = rate_part.trim().strip_suffix('%') {
                if let Ok(value) = percentage.trim().parse::<f64>() {
                    return value / 100.0;
                }
            }
        }
        0.0
    }
    
    // Extract average value from an Average's debug output
    fn parse_average(avg: &Average) -> f64 {
        let debug_str = format!("{:?}", avg);
        // Debug format is just the average value as a floating point
        if let Ok(value) = debug_str.parse::<f64>() {
            return value;
        }
        0.0
    }

    // Calculate reward from solver statistics based on context
    pub fn calculate_reward(&self, statistic: &Statistic, phase: SolverPhase) -> f64 {
        match phase {
            SolverPhase::Early => {
                // In early phase, prioritize MIC drop success rate and cube minimization
                let mic_success_rate = Self::parse_success_rate(&statistic.mic_drop);
                
                let avg_mic_cube_len = if statistic.num_mic > 0 { 
                    Self::parse_average(&statistic.avg_mic_cube_len)
                } else { 
                    0.0 
                };
                
                // Normalize cube length (shorter is better)
                let norm_cube_len = if avg_mic_cube_len > 0.0 {
                    1.0 / avg_mic_cube_len
                } else {
                    0.0
                };
                
                // Combined reward (70% success rate, 30% cube length)
                0.7 * mic_success_rate + 0.3 * norm_cube_len
            },
            SolverPhase::Middle => {
                // In middle phase, balance between success rate and solving speed
                let mic_success_rate = Self::parse_success_rate(&statistic.mic_drop);
                
                let block_time_ratio = if statistic.overall_block_time.as_secs_f64() > 0.0 {
                    statistic.block_mic_time.as_secs_f64() / statistic.overall_block_time.as_secs_f64()
                } else {
                    0.0
                };
                
                // Reward efficiency (lower block_time_ratio is better)
                let efficiency = if block_time_ratio > 0.0 {
                    1.0 / block_time_ratio
                } else {
                    0.0
                };
                
                // Combined reward
                0.5 * mic_success_rate + 0.5 * (efficiency / 10.0) // Normalize efficiency
            },
            SolverPhase::Late => {
                // In late phase, prioritize solving efficiency and propagation
                let ctp_success_rate = Self::parse_success_rate(&statistic.ctp);
                
                let propagate_time_ratio = if statistic.overall_propagate_time.as_secs_f64() > 0.0 {
                    1.0 / statistic.overall_propagate_time.as_secs_f64()
                } else {
                    0.0
                };
                
                // Combined reward
                0.4 * ctp_success_rate + 0.6 * (propagate_time_ratio * 10.0) // Normalize time ratio
            }
        }
    }
    
    // Print contextual strategy information
    pub fn print_contextual_stats(&self) {
        println!("\n=== Contextual MAB Strategy Statistics ===");
        for phase in [SolverPhase::Early, SolverPhase::Middle, SolverPhase::Late].iter() {
            println!("Phase: {:?}", phase);
            
            if let Some(rewards) = self.context_rewards.get(phase) {
                for (i, strategy_rewards) in rewards.iter().enumerate() {
                    if !strategy_rewards.is_empty() {
                        let avg_reward = strategy_rewards.iter().sum::<f64>() / strategy_rewards.len() as f64;
                        println!("  {:?}: avg reward = {:.4} (samples: {})", 
                                 self.strategies[i], avg_reward, strategy_rewards.len());
                    } else {
                        println!("  {:?}: no data", self.strategies[i]);
                    }
                }
            }
            println!("");
        }
        println!("========================================\n");
    }
}

// Define solver phases to adapt MAB rewards
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SolverPhase {
    Early,   // Beginning of solving, focus on finding good MICs
    Middle,  // Middle phase, balance between MIC and propagation
    Late,    // Late phase, focus on efficient propagation
}

// Helper function to determine solver phase based on statistics
// This provides the context for the contextual MAB
pub fn determine_phase(statistic: &Statistic, frames_count: usize) -> SolverPhase {
    // Use heuristics based on solving progress
    let debug_str = format!("{:?}", statistic.mic_drop);
    let total_tries = if let Some(succ_part) = debug_str.split("success:").nth(1) {
        if let Some(num_str) = succ_part.split(',').next() {
            if let Ok(success) = num_str.trim().parse::<usize>() {
                if let Some(fail_part) = debug_str.split("fail:").nth(1) {
                    if let Some(num_str) = fail_part.split(',').next() {
                        if let Ok(fail) = num_str.trim().parse::<usize>() {
                            success + fail
                        } else { 0 }
                    } else { 0 }
                } else { 0 }
            } else { 0 }
        } else { 0 }
    } else { 0 };
    
    if statistic.num_mic < 1000 || frames_count < 3 {
        SolverPhase::Early
    } else if total_tries < 100000 || frames_count < 10 {
        SolverPhase::Middle
    } else {
        SolverPhase::Late
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_contextual_mab_strategy_selection() {
        let mut mab = ContextualMAB::new(10, 0.1, 0.99, 0.01);
        let mut stats = Statistic::new("test");
        
        // Test early phase selection
        let phase = SolverPhase::Early;
        let strategy = mab.select(phase, &stats);
        assert!(OrderingStrategy::all().contains(&strategy));
        
        // Add some rewards to strategies for different phases
        for i in 0..5 {
            // Add rewards for early phase
            mab.last_selected = Some((SolverPhase::Early, OrderingStrategy::all()[i]));
            mab.update(0.5 + i as f64 * 0.1, &stats); // Increasing rewards
            
            // Add rewards for middle phase
            mab.last_selected = Some((SolverPhase::Middle, OrderingStrategy::all()[i]));
            mab.update(0.8 - i as f64 * 0.1, &stats); // Decreasing rewards
        }
        
        // With low exploration rate, should favor highest reward for each context
        mab.exploration_rate = 0.0;
        
        // Early phase should prefer HighFlipRateFirst
        let early_strategy = mab.select(SolverPhase::Early, &stats);
        assert_eq!(early_strategy, OrderingStrategy::HighFlipRateFirst);
        
        // Middle phase should prefer DefaultActivity
        let middle_strategy = mab.select(SolverPhase::Middle, &stats);
        assert_eq!(middle_strategy, OrderingStrategy::DefaultActivity);
    }
    
    #[test]
    fn test_phase_determination() {
        let mut stats = Statistic::new("test");
        
        // Early phase with few MICs
        stats.num_mic = 100;
        assert_eq!(determine_phase(&stats, 2), SolverPhase::Early);
        
        // Middle phase
        stats.num_mic = 5000;
        for _ in 0..20000 {
            stats.mic_drop.success();
        }
        assert_eq!(determine_phase(&stats, 5), SolverPhase::Middle);
        
        // Late phase
        for _ in 0..80000 {
            stats.mic_drop.fail();
        }
        assert_eq!(determine_phase(&stats, 15), SolverPhase::Late);
    }
    
    #[test]
    fn test_reward_calculation() {
        let mab = ContextualMAB::new(10, 0.1, 0.99, 0.01);
        let mut stats = Statistic::new("test");
        
        // Set up statistics
        stats.num_mic = 5000;
        
        // Add success/failures
        for _ in 0..20000 {
            stats.mic_drop.success();
        }
        for _ in 0..30000 {
            stats.mic_drop.fail();
        }
        for _ in 0..1000 {
            stats.ctp.success();
        }
        for _ in 0..9000 {
            stats.ctp.fail();
        }
        
        stats.overall_block_time = Duration::from_secs(10);
        stats.block_mic_time = Duration::from_secs(4);
        stats.overall_propagate_time = Duration::from_secs(5);
        
        // Test early phase reward
        let early_reward = mab.calculate_reward(&stats, SolverPhase::Early);
        assert!(early_reward > 0.0);
        
        // Test middle phase reward
        let middle_reward = mab.calculate_reward(&stats, SolverPhase::Middle);
        assert!(middle_reward > 0.0);
        
        // Test late phase reward
        let late_reward = mab.calculate_reward(&stats, SolverPhase::Late);
        assert!(late_reward > 0.0);
    }
} 