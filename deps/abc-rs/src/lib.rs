use aig::Aig;
use std::{
    env,
    ffi::{CString, c_char, c_void},
};

unsafe extern "C" {
    fn Abc_FrameGetGlobalFrame() -> *mut c_void;
    fn Abc_Stop();
    fn Cmd_CommandExecute(pAbc: *mut c_void, sCommand: *const c_char) -> i32;
}

pub struct Abc {
    ptr: *mut c_void,
}

impl Drop for Abc {
    fn drop(&mut self) {
        unsafe { Abc_Stop() };
    }
}

impl Abc {
    pub fn new() -> Self {
        let ptr = unsafe { Abc_FrameGetGlobalFrame() };
        assert!(!ptr.is_null(), "init abc failed");
        Self { ptr }
    }

    pub fn execute_command(&mut self, command: &str) {
        let c = CString::new(command).unwrap();
        let res = unsafe { Cmd_CommandExecute(self.ptr, c.as_ptr()) };
        assert!(res == 0, "abc execute {command} failed");
    }

    pub fn read_aig(&mut self, aig: &Aig) {
        let dir = match env::var("RIC3_TMP_DIR") {
            Ok(d) => d,
            Err(_) => "/tmp/rIC3".to_string(),
        };
        let tmpfile = tempfile::NamedTempFile::new_in(dir).unwrap();
        let path = tmpfile.path().as_os_str().to_str().unwrap();
        aig.to_file(path, false);
        let command = format!("read_aiger {};", path);
        let command = CString::new(command).unwrap();
        let res = unsafe { Cmd_CommandExecute(self.ptr, command.as_ptr()) };
        assert!(res == 0, "abc read aig failed");
    }

    pub fn write_aig(&mut self) -> Aig {
        let dir = match env::var("RIC3_TMP_DIR") {
            Ok(d) => d,
            Err(_) => "/tmp/rIC3".to_string(),
        };
        let tmpfile = tempfile::NamedTempFile::new_in(dir).unwrap();
        let path = tmpfile.path().as_os_str().to_str().unwrap();
        let command = format!("write_aiger {};", path);
        let command = CString::new(command).unwrap();
        let res = unsafe { Cmd_CommandExecute(self.ptr, command.as_ptr()) };
        assert!(res == 0, "abc write aig failed");
        Aig::from_file(path)
    }
}

impl Default for Abc {
    fn default() -> Self {
        Self::new()
    }
}
