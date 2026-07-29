# Report Supervisor Hang Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make setsid-descendant supervision correct and make failures return a bounded, typed test result instead of `Hangup`.

**Architecture:** Record supervised PID/start-identity pairs during normal sampling and revalidate them during termination. Strengthen the integration topology so the detached child has no live parent, original process-group membership, or inherited marker FD, and wrap the raw supervisor process in a timer watchdog that drains output and cleans up every path.

**Tech Stack:** Bash 3.2-compatible shell, .NET 10, xUnit 2, `System.Diagnostics.Process`.

---

### Task 1: Create the RED integration contract

**Files:**
- Modify: `Meta/StrataLint/StrataLint.Tests/Commands/ReportSupervisorFixture.cs`
- Modify: `Meta/StrataLint/StrataLint.Tests/Commands/ReportSupervisorScriptTests.cs`

- [ ] **Step 1: Build a deterministic detached topology**

Write worker, helper-parent, and detached-child PID files. The child calls
`setsid`, closes stdout/stderr/fd 9, waits for a release file, then execs
`sleep 60`. Add fixture-local `ps` and `pgrep` commands and prepend the fixture
root to `PATH` for supervisor runs.

- [ ] **Step 2: Require a candidate record before orphaning**

Add `HasRecordedProcessCandidate(pid)`. Wait for the record, release the helper
parent, prove the child remains alive, terminate the supervisor, and prove the
child is gone.

- [ ] **Step 3: Verify RED with the exact test body**

Run:

```bash
gtimeout --kill-after=10s 60s dotnet .scratch-report-supervisor-repro/bin/Release/net10.0/ReportSupervisorRepro.dll
```

Expected: an explicit assertion failure because the old supervisor has no
`process-candidates` file; the command returns before 60 seconds.

### Task 2: Add deterministic test cleanup

**Files:**
- Create: `Meta/StrataLint/StrataLint.Tests/Commands/ReportSupervisor/ReportSupervisorTestWatchdog.cs`
- Create: `Meta/StrataLint/StrataLint.Tests/Commands/ReportSupervisor/ReportSupervisorTestWatchdogTests.cs`
- Modify: `Meta/StrataLint/StrataLint.Tests/Commands/ReportSupervisorFixture.cs`
- Modify: `Meta/StrataLint/StrataLint.Tests/Commands/ReportSupervisorScriptTests.cs`

- [ ] **Step 1: Write a watchdog RED test**

Track `/bin/bash -c "printf watchdog-err >&2; sleep 60"` with a 100 ms timer.
Assert exit within five seconds and an xUnit timeout containing `watchdog-err`.

- [ ] **Step 2: Implement the independent watchdog**

Track `Process` instances, asynchronously drain stdout/stderr, retain 8192-char
tails, and use `Timer` to mark timeout and call
`Kill(entireProcessTree: true)`. Disposal kills active tracked processes and
throws only when the timer fired. Do not use xUnit `Timeout`.

- [ ] **Step 3: Put target cleanup in `finally`**

Track the supervisor immediately after start. In `finally`, terminate it if
active and send `KILL` to a parsed detached PID if it survived.

### Task 3: Record and reap session-changing descendants

**Files:**
- Modify: `Meta/StrataLint/scripts/report/report-supervisor.sh`

- [ ] **Step 1: Add the private candidate ledger**

Create `$TMP_ROOT/process-candidates`. For every sampled PID, append
`PID|process_start_identity` only once.

- [ ] **Step 2: Signal only identity-matching records**

Before existing marker/group TERM and KILL passes, read candidates in reverse
PID order, re-read each start identity, and signal only exact matches. Ignore
malformed, dead, or reused PIDs.

- [ ] **Step 3: Verify GREEN**

Rebuild the local harness and run the strengthened target test. Expected:
`PASS`, exit 0, and completion within 60 seconds.

### Task 4: Verify and commit

**Files:** All files above.

- [ ] **Step 1: Run focused stress**

Run target and watchdog tests at least ten times under an external 60-second
bound. Every run must return 0 without a surviving detached process.

- [ ] **Step 2: Run related gates**

Run the report-supervisor bucket, warning-as-error solution build, and
`make preflight`. Record exact sandbox capability failures separately; retain
direct in-process evidence when VSTest loopback is denied.

- [ ] **Step 3: Review and commit**

Remove scratch/debug files, inspect the diff, and commit to
`harness/report-supervisor-fix` with the root cause in the message.
