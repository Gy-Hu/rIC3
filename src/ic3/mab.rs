use crate::ic3::statistic::Statistic;
use rand::prelude::*;
use rand::thread_rng;
use std::time::Duration;
use std::fmt::Debug;
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

// Non-stationary MAB implementation with sliding window
pub struct NonStationaryMAB {
    strategies: Vec<OrderingStrategy>,
    rewards: Vec<Vec<f64>>,           // Sliding window of rewards for each arm
    window_size: usize,               // Size of sliding window
    pub exploration_rate: f64,        // Epsilon for exploration
    exploration_decay: f64,           // Decay rate for exploration
    min_exploration_rate: f64,        // Minimum exploration rate
    pub last_selected: Option<OrderingStrategy>, // Last selected strategy
    rng: ThreadRng,                   // Random number generator
}

impl NonStationaryMAB {
    pub fn new(window_size: usize, exploration_rate: f64, exploration_decay: f64, min_exploration_rate: f64) -> Self {
        let strategies = OrderingStrategy::all().to_vec();
        let rewards = vec![Vec::with_capacity(window_size); strategies.len()];

        Self {
            strategies,
            rewards,
            window_size,
            exploration_rate,
            exploration_decay,
            min_exploration_rate,
            last_selected: None,
            rng: thread_rng(),
        }
    }

    // Select a strategy using epsilon-greedy policy
    pub fn select(&mut self) -> OrderingStrategy {
        // Explore with probability epsilon
        if self.rng.random::<f64>() < self.exploration_rate {
            let index = self.rng.random_range(0..self.strategies.len());
            self.last_selected = Some(self.strategies[index]);
            return self.strategies[index];
        }

        // Otherwise exploit the best strategy
        let mut best_index = 0;
        let mut best_value = f64::NEG_INFINITY;

        for (i, rewards) in self.rewards.iter().enumerate() {
            if rewards.is_empty() {
                // If no rewards yet, prioritize exploration
                self.last_selected = Some(self.strategies[i]);
                return self.strategies[i];
            }

            let avg_reward = rewards.iter().sum::<f64>() / rewards.len() as f64;
            if avg_reward > best_value {
                best_value = avg_reward;
                best_index = i;
            }
        }

        self.last_selected = Some(self.strategies[best_index]);
        self.strategies[best_index]
    }

    // Update the reward for the last selected strategy
    pub fn update(&mut self, reward: f64) {
        if let Some(strategy) = self.last_selected {
            let index = self.strategies.iter().position(|&s| s == strategy).unwrap();
            
            // Add reward to the window
            if self.rewards[index].len() >= self.window_size {
                self.rewards[index].remove(0); // Remove oldest reward
            }
            self.rewards[index].push(reward);

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

    // Calculate reward from solver statistics
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
}

// Define solver phases to adapt MAB rewards
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverPhase {
    Early,   // Beginning of solving, focus on finding good MICs
    Middle,  // Middle phase, balance between MIC and propagation
    Late,    // Late phase, focus on efficient propagation
}

// Helper function to determine solver phase based on statistics
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
    fn test_mab_strategy_selection() {
        let mut mab = NonStationaryMAB::new(10, 0.1, 0.99, 0.01);
        
        // First selection should be exploration or first strategy (if no data)
        let strategy = mab.select();
        assert!(OrderingStrategy::all().contains(&strategy));
        
        // Add some rewards to strategies
        for i in 0..5 {
            mab.last_selected = Some(OrderingStrategy::all()[i]);
            mab.update(0.5 + i as f64 * 0.1); // Increasing rewards
        }
        
        // With low exploration rate, should favor highest reward
        mab.exploration_rate = 0.0;
        let strategy = mab.select();
        assert_eq!(strategy, OrderingStrategy::HighFlipRateFirst);
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
        let mab = NonStationaryMAB::new(10, 0.1, 0.99, 0.01);
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