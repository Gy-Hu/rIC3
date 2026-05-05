use std::{path::Path, process::Command};
use tempfile::TempDir;

pub struct MountOverlay {
    _work: TempDir,
    merge: TempDir,
}

impl MountOverlay {
    pub fn new(lower: impl AsRef<Path>, upper: impl AsRef<Path>) -> Self {
        let work = tempfile::tempdir().unwrap();
        let merge = tempfile::tempdir().unwrap();
        Command::new("mount")
            .arg("-t")
            .arg("overlay")
            .arg("overlay")
            .arg("-o")
            .arg(format!(
                "lowerdir={},upperdir={},workdir={}",
                lower.as_ref().display(),
                upper.as_ref().display(),
                work.path().display()
            ))
            .arg(merge.path())
            .status()
            .unwrap()
            .exit_ok()
            .unwrap();
        Self { _work: work, merge }
    }

    pub fn path(&self) -> &Path {
        self.merge.path()
    }
}

impl Drop for MountOverlay {
    fn drop(&mut self) {
        Command::new("umount")
            .arg(self.merge.path())
            .status()
            .unwrap()
            .exit_ok()
            .unwrap();
    }
}
