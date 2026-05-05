fn main() -> Result<(), String> {
    giputils::build::git_submodule_update()?;
    println!("cargo:rerun-if-changed=./abc");
    let mut cfg = cmake::Config::new("abc");
    cfg.build_target("libabc");
    let dst = cfg.build();
    println!(
        "cargo:rustc-link-search=native={}",
        dst.join("build").display()
    );
    println!("cargo:rustc-link-lib=static=abc");
    #[cfg(target_os = "linux")]
    println!("cargo:rustc-link-lib=dylib=stdc++");
    #[cfg(target_os = "macos")]
    println!("cargo:rustc-link-lib=dylib=c++");
    Ok(())
}
