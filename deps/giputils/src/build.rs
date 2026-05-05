use git2::{FetchOptions, ProxyOptions};
use std::{
    env,
    fs::remove_dir_all,
    path::{Path, PathBuf},
    process::Command,
};

pub fn copy_build(
    src: &str,
    f: impl FnOnce(&Path) -> Result<(), String>,
) -> Result<PathBuf, String> {
    let src_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join(src);
    let cp_dir = PathBuf::from(env::var("OUT_DIR").unwrap()).join(src);
    if cp_dir.exists() {
        remove_dir_all(&cp_dir).unwrap();
    }
    Command::new("cp")
        .arg("-r")
        .arg(src_dir.as_path())
        .arg(&cp_dir)
        .status()
        .map_err(|e| e.to_string())?;
    f(&cp_dir)?;
    Ok(cp_dir)
}

pub fn git_submodule_update() -> Result<(), String> {
    let Ok(repo) = git2::Repository::open(".") else {
        return Ok(());
    };
    for mut sm in repo.submodules().unwrap() {
        let status = repo
            .submodule_status(sm.name().unwrap(), git2::SubmoduleIgnore::None)
            .unwrap();
        if !status.is_in_wd() || status.is_wd_uninitialized() || status.is_wd_deleted() {
            let mut proxy_options = ProxyOptions::new();
            proxy_options.auto();
            let mut fetch_opts = FetchOptions::new();
            fetch_opts.proxy_options(proxy_options);
            let mut opts = git2::SubmoduleUpdateOptions::new();
            opts.fetch(fetch_opts);
            sm.update(true, Some(&mut opts))
                .map_err(|e| e.to_string())?;
        }
    }
    Ok(())
}
