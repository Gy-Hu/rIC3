extern crate cc;

fn main() -> Result<(), String> {
    giputils::build::git_submodule_update()?;
    println!("cargo:rerun-if-changed=./aiger");
    cc::Build::new()
        .include("aiger")
        .file("aiger/aiger.c")
        .file("aiger/aigsim.c")  // Add aigsim.c to compilation
        .file("aiger/aigsim_ffi.c")  // Add FFI implementation
        .opt_level(3)
        .warnings(false)
        .compile("aiger");

    Ok(())
}
