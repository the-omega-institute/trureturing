
## Process safety (binding)
Your own carrier is the sshx runner `run-codex-worker.sh --flight-id __FLIGHT__` and the `codex exec` processes it started; those are **you**. Never kill, signal or stop any `codex`, `node … codex`, `run-codex-worker.sh` or `dispatch` process, on this worktree or any other, even if it looks idle: an idle-looking runner is usually your own parent waiting for you. If you believe another seat is working in your worktree, stop and report `open` with the evidence (`ps` lines and file mtimes); do not take it over.

## Host-resource retries
If a build, report, emit, gate or door command fails only because the host ran out of a shared resource, wait two minutes and rerun the same command (for a one-command door, the whole door), up to three times in total. Shared-resource failures are `fork: Resource temporarily unavailable`, "too many open files in system", "file table overflow", error code 23, or a dotnet crash with exit 139. Report each attempt's exit code and diagnostic line. Any other failure follows the brief's own stop rules.

## Lean process limit (binding)
Run at most one Lean process at a time in this seat: one `lake env lean`, `lake build` or `make lean …` invocation, never several in parallel (no `&`, no parallel scratch compiles). Every seat on a host shares the kernel vnode table. A "Too many open files in system" or error-23 failure follows the host-resource retry rule above.
