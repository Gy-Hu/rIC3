#![feature(exit_status_error)]

use giputils::build::copy_build;
use std::env;
use std::process::Command;
extern crate giputils;

fn main() -> Result<(), String> {
    giputils::build::git_submodule_update()?;
    println!("cargo:rerun-if-changed=./kissat");
    let cb_path = copy_build("kissat", |src| {
        Command::new("sh")
            .arg("configure")
            .current_dir(src)
            .status()
            .map_err(|e| e.to_string())?
            .exit_ok()
            .map_err(|e| e.to_string())?;
        let num_jobs = env::var("NUM_JOBS").unwrap();
        Command::new("make")
            .arg(format!("-j{}", num_jobs))
            .current_dir(src)
            .status()
            .map_err(|e| e.to_string())?
            .exit_ok()
            .map_err(|e| e.to_string())
    })?;
    println!(
        "cargo:rustc-link-search=native={}",
        cb_path.join("build").display()
    );
    println!("cargo:rustc-link-lib=static=kissat");
    Ok(())
}
