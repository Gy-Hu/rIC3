#!/usr/bin/env python3
"""
rIC3 Latin Hypercube Sampler

This script generates diverse configurations for the rIC3 model checker 
using Latin Hypercube Sampling (LHS).
"""

import numpy as np
import pandas as pd
from pyDOE2 import lhs
import os
import argparse
import json
from datetime import datetime

def parse_arguments():
    parser = argparse.ArgumentParser(description='Generate configurations for rIC3 using LHS')
    parser.add_argument('--num_samples', type=int, default=20,
                        help='Number of configurations to generate (default: 20)')
    parser.add_argument('--output_dir', type=str, default='ric3_configs',
                        help='Directory to save the configuration files (default: ric3_configs)')
    parser.add_argument('--seed', type=int, default=42,
                        help='Random seed for reproducibility (default: 42)')
    return parser.parse_args()

def generate_configs(num_samples, seed):
    np.random.seed(seed)
    
    # Define boolean parameters
    bool_params = [
        "ic3_dynamic",
        "ic3_ctg",
        "ic3_ctp",
        "ic3_inn",
        "ic3_abs_cst",
        "ic3_no_pred_prop"
    ]
    
    # Define integer parameters with their ranges
    int_params = {
        "ic3_ctg_max": (1, 10),
        "ic3_ctg_limit": (1, 5)
    }
    
    # Fixed parameters
    fixed_params = {
        "engine": "IC3",
        "no_abc": False,
        "rseed": 42,
        "verbose": 1,
    }
    
    # Total number of parameters for LHS
    n_params = len(bool_params) + len(int_params)
    
    # Generate LHS samples
    samples = lhs(n_params, samples=num_samples)
    
    # Convert to configurations
    configs = []
    for i in range(num_samples):
        config = {}
        
        # Boolean parameters
        for j, param in enumerate(bool_params):
            config[param] = bool(round(samples[i, j]))
        
        # Integer parameters
        j = len(bool_params)
        for param, (low, high) in int_params.items():
            scaled_value = low + samples[i, j] * (high - low)
            config[param] = int(round(scaled_value))
            j += 1
        
        # Add fixed parameters
        config.update(fixed_params)
        
        # Apply post-processing rules
        if config["ic3_inn"]:
            config["no_abc"] = True
        
        if not config["ic3_ctg"]:
            config["ic3_ctg_max"] = None
            config["ic3_ctg_limit"] = None
        
        configs.append(config)
    
    return configs

def config_to_cmd(config, model_path):
    """Convert a configuration to a command line string"""
    cmd = f"./ric3 -e ic3"
    
    for param, value in config.items():
        if param.startswith("ic3_"):
            flag = f"--{param.replace('_', '-')}"
            if isinstance(value, bool):
                if value:
                    cmd += f" {flag}"
            elif value is not None:
                cmd += f" {flag} {value}"
        elif param == "no_abc" and value:
            cmd += f" --no-abc"
        elif param == "rseed":
            cmd += f" --rseed {value}"
    
    cmd += f" {model_path}"
    return cmd

def save_configs(configs, output_dir, model_path="model.aig"):
    """Save configurations to files"""
    os.makedirs(output_dir, exist_ok=True)
    
    # Save as DataFrame
    df = pd.DataFrame(configs)
    parquet_path = os.path.join(output_dir, "ric3_configs.parquet")
    csv_path = os.path.join(output_dir, "ric3_configs.csv")
    df.to_parquet(parquet_path)
    df.to_csv(csv_path, index=False)
    
    # Save as JSON
    json_path = os.path.join(output_dir, "ric3_configs.json")
    with open(json_path, 'w') as f:
        json.dump(configs, f, indent=2)
    
    # Save as shell script with commands
    sh_path = os.path.join(output_dir, "run_configs.sh")
    with open(sh_path, 'w') as f:
        f.write("#!/bin/bash\n\n")
        f.write(f"# Generated on {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
        
        for i, config in enumerate(configs):
            f.write(f"# Configuration {i+1}\n")
            f.write(f"{config_to_cmd(config, model_path)}\n\n")
    
    # Make the shell script executable
    os.chmod(sh_path, 0o755)
    
    return {
        "parquet": parquet_path,
        "csv": csv_path,
        "json": json_path,
        "shell": sh_path
    }

def main():
    args = parse_arguments()
    
    print(f"Generating {args.num_samples} configurations for rIC3...")
    configs = generate_configs(args.num_samples, args.seed)
    
    print(f"Saving configurations to {args.output_dir}/...")
    paths = save_configs(configs, args.output_dir)
    
    print("\nGenerated files:")
    for file_type, path in paths.items():
        print(f"- {file_type.capitalize()} configuration: {path}")
    
    print("\nConfiguration summary:")
    df = pd.DataFrame(configs)
    
    # Count boolean parameters
    for param in df.columns:
        if df[param].dtype == bool:
            true_count = df[param].sum()
            print(f"- {param}: {true_count} True, {len(df) - true_count} False")
    
    print("\nTo run all configurations:")
    print(f"  bash {paths['shell']}")
    
    print("\nTo run a specific configuration, for example #1:")
    print(f"  $(sed -n '4p' {paths['shell']})")

if __name__ == "__main__":
    main()