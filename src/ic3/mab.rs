use crate::ic3::statistic::Statistic;
use rand::prelude::*;
use rand::Rng;
use std::fmt::Debug;
use giputils::statistic::{SuccessRate, Average};
use std::collections::HashMap;

// Define the different ordering types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

// Contextual MAB implementation with sliding window per context
pub struct ContextualMAB {
    strategies: Vec<OrderingStrategy>,
    rewards_per_context: HashMap<SolverPhase, Vec<Vec<f64>>>,
    window_size: usize,               // Size of sliding window
    pub exploration_rate: f64,        // Epsilon for exploration
    exploration_decay: f64,           // Decay rate for exploration
    min_exploration_rate: f64,        // Minimum exploration rate
    pub last_selected: Option<OrderingStrategy>, // Last selected strategy
    rng: ThreadRng,                   // Random number generator
}

impl ContextualMAB {
    pub fn new(window_size: usize, exploration_rate: f64, exploration_decay: f64, min_exploration_rate: f64) -> Self {
        let strategies = OrderingStrategy::all().to_vec();
        let mut rewards_per_context = HashMap::new();
        rewards_per_context.insert(SolverPhase::Early, vec![Vec::with_capacity(window_size); strategies.len()]);
        rewards_per_context.insert(SolverPhase::Middle, vec![Vec::with_capacity(window_size); strategies.len()]);
        rewards_per_context.insert(SolverPhase::Late, vec![Vec::with_capacity(window_size); strategies.len()]);

        Self {
            strategies,
            rewards_per_context,
            window_size,
            exploration_rate,
            exploration_decay,
            min_exploration_rate,
            last_selected: None,
            rng: rand::thread_rng(),
        }
    }

    // Select a strategy using epsilon-greedy policy within a given context
    pub fn select(&mut self, context: SolverPhase) -> OrderingStrategy {
        if self.rng.random::<f64>() < self.exploration_rate {
            let index = self.rng.random_range(0..self.strategies.len());
            self.last_selected = Some(self.strategies[index]);
            return self.strategies[index];
        }

        let mut best_index = 0;
        let mut best_value = f64::NEG_INFINITY;

        let context_rewards = self.rewards_per_context.get(&context).expect("Context should exist");

        for (i, rewards) in context_rewards.iter().enumerate() {
            if rewards.is_empty() {
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

    // Update the reward for the last selected strategy within a given context
    pub fn update(&mut self, reward: f64, context: SolverPhase) {
        if let Some(strategy) = self.last_selected {
            if let Some(index) = self.strategies.iter().position(|&s| s == strategy) {
                if let Some(context_rewards) = self.rewards_per_context.get_mut(&context) {
                    let strategy_rewards = &mut context_rewards[index];

                    if strategy_rewards.len() >= self.window_size {
                        strategy_rewards.remove(0);
                    }
                    strategy_rewards.push(reward);

                    self.exploration_rate = (self.exploration_rate * self.exploration_decay)
                        .max(self.min_exploration_rate);
                } else {
                    eprintln!("Warning: Context {:?} not found during MAB update.", context);
                }
            } else {
                eprintln!("Warning: Last selected strategy {:?} not found during MAB update.", strategy);
            }
        }
    }

    // Extract success rate from a SuccessRate's debug output
    fn parse_success_rate(sr: &SuccessRate) -> f64 {
        let debug_str = format!("{:?}", sr);
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
        if let Ok(value) = debug_str.parse::<f64>() {
            return value;
        }
        0.0
    }

    // Calculate reward from solver statistics
    pub fn calculate_reward(&self, statistic: &Statistic, phase: SolverPhase) -> f64 {
        match phase {
            SolverPhase::Early => {
                let mic_success_rate = Self::parse_success_rate(&statistic.mic_drop);
                
                let avg_mic_cube_len = if statistic.num_mic > 0 { 
                    Self::parse_average(&statistic.avg_mic_cube_len)
                } else { 
                    0.0 
                };
                
                let norm_cube_len = if avg_mic_cube_len > 0.0 {
                    1.0 / avg_mic_cube_len
                } else {
                    0.0
                };
                
                0.7 * mic_success_rate + 0.3 * norm_cube_len
            },
            SolverPhase::Middle => {
                let mic_success_rate = Self::parse_success_rate(&statistic.mic_drop);
                
                let block_time_ratio = if statistic.overall_block_time.as_secs_f64() > 0.0 {
                    statistic.block_mic_time.as_secs_f64() / statistic.overall_block_time.as_secs_f64()
                } else {
                    0.0
                };
                
                let efficiency = if block_time_ratio > 0.0 {
                    1.0 / block_time_ratio
                } else {
                    0.0
                };
                
                0.5 * mic_success_rate + 0.5 * (efficiency / 10.0)
            },
            SolverPhase::Late => {
                let ctp_success_rate = Self::parse_success_rate(&statistic.ctp);
                
                let propagate_time_ratio = if statistic.overall_propagate_time.as_secs_f64() > 0.0 {
                    1.0 / statistic.overall_propagate_time.as_secs_f64()
                } else {
                    0.0
                };
                
                0.4 * ctp_success_rate + 0.6 * (propagate_time_ratio * 10.0)
            }
        }
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
pub fn determine_phase(statistic: &Statistic, frames_count: usize) -> SolverPhase {
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
        let mut mab = ContextualMAB::new(10, 0.1, 0.99, 0.01);

        println!("Testing Early Phase Selection");
        let strategy_early = mab.select(SolverPhase::Early);
        assert!(OrderingStrategy::all().contains(&strategy_early));

        for i in 0..5 {
            mab.last_selected = Some(OrderingStrategy::all()[i]);
            let reward = if OrderingStrategy::all()[i] == OrderingStrategy::DefaultActivity { 0.9 } else { 0.5 }; 
            mab.update(reward, SolverPhase::Early);
        }

        mab.exploration_rate = 0.0;
        let strategy_early_exploit = mab.select(SolverPhase::Early);
        println!("Early Phase Best Strategy: {:?}", strategy_early_exploit);
        assert_eq!(strategy_early_exploit, OrderingStrategy::DefaultActivity);

        println!("\nTesting Late Phase Selection");
        mab.exploration_rate = 0.1; 
        let strategy_late = mab.select(SolverPhase::Late);
        assert!(OrderingStrategy::all().contains(&strategy_late));

        for i in 0..5 {
            mab.last_selected = Some(OrderingStrategy::all()[i]);
            let reward = if OrderingStrategy::all()[i] == OrderingStrategy::HighFlipRateFirst { 0.8 } else { 0.4 }; 
            mab.update(reward, SolverPhase::Late);
        }

        mab.exploration_rate = 0.0;
        let strategy_late_exploit = mab.select(SolverPhase::Late);
        println!("Late Phase Best Strategy: {:?}", strategy_late_exploit);
        assert_eq!(strategy_late_exploit, OrderingStrategy::HighFlipRateFirst);

        println!("\nRe-Testing Early Phase Selection");
        let strategy_early_recheck = mab.select(SolverPhase::Early);
        println!("Early Phase Best Strategy (Recheck): {:?}", strategy_early_recheck);
        assert_eq!(strategy_early_recheck, OrderingStrategy::DefaultActivity, "Early phase selection should not be affected by Late phase updates");
    }

    #[test]
    fn test_phase_determination() {
        let mut stats = Statistic::new("test");
        
        stats.num_mic = 100;
        assert_eq!(determine_phase(&stats, 2), SolverPhase::Early);
        
        stats.num_mic = 5000;
        for _ in 0..20000 {
            stats.mic_drop.success();
        }
        assert_eq!(determine_phase(&stats, 5), SolverPhase::Middle);
        
        for _ in 0..80000 {
            stats.mic_drop.fail();
        }
        assert_eq!(determine_phase(&stats, 15), SolverPhase::Late);
    }
    
    #[test]
    fn test_reward_calculation() {
        let mab = ContextualMAB::new(10, 0.1, 0.99, 0.01);
        let mut stats = Statistic::new("test");
        
        stats.num_mic = 5000;
        
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

        let early_reward = mab.calculate_reward(&stats, SolverPhase::Early);
        println!("Calculated Early Reward: {}", early_reward);
        assert!(early_reward > 0.0);

        let middle_reward = mab.calculate_reward(&stats, SolverPhase::Middle);
        println!("Calculated Middle Reward: {}", middle_reward);
        assert!(middle_reward > 0.0);

        let late_reward = mab.calculate_reward(&stats, SolverPhase::Late);
        println!("Calculated Late Reward: {}", late_reward);
        assert!(late_reward > 0.0);
    }
} 