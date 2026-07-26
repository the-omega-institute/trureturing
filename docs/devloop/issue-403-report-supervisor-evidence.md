# Issue 403 report supervisor evidence

This file preserves the safety contract and RED evidence for the Lean-slot
controller after the #452 scope reduction. It is review evidence, not
executable policy.

## Dead-owner reclaim contract

Each lock records `owner=PID|process-start|epoch`. The epoch identifies the
claim event; it is not an expiry time and is never renewed. A live owner is
never displaced because of elapsed wall-clock time.

A slot whose owner process is gone, or whose PID has a different start
identity, has two conservative-extension branches. If a crash occurred after
the owner claim but before both `group` and `marker` metadata were published,
the slot is reclaimed directly with the same dead-owner meaning as `dev`. If
both metadata records exist, reclaim requires both recorded producer views to
be confirmed empty:

- the platform process view has no non-zombie member of the exact recorded
  process group; and
- the inherited marker has no process holding its dedicated descriptor.

Unreadable or malformed owner state fails closed. Once both producer metadata
records exist, unreadable or malformed process-group, process-table, or marker
state also fails closed. Any live group or marker member keeps the slot. Stale
reclaim never sends SIGTERM or SIGKILL.

This is a conservative extension of `dev` at every dead-owner state: missing
producer metadata retains `dev`'s direct reclaim, so the crash window cannot
introduce new starvation; complete metadata adds the stronger group-plus-marker
silence proof. A descendant that escapes both recorded views with `setsid`
remains an exposure already present in `dev`, not a regression introduced by
this change.

The independent #450 worker wall-clock budget is unchanged. A supervisor still
terminates its own worker group when that configured build budget is exceeded
(7200 seconds by default), records `124`, and releases its slot through the
normal `finish()` path.

## Cross-platform process semantics

Linux reads `/proc/<pid>/stat` directly. Following `proc_pid_stat(5)`, the
parser takes state from field 3, parent PID from field 4, process group from
field 5, and starttime (clock ticks after boot) from field 22. It locates fields
after the final `)` so spaces and parentheses in `comm` do not shift them.
Linux owner and group-leader identities use that same field-22 coordinate;
they never compare it with the wall-clock string emitted by `ps lstart`.
Hosts without procfs retain the common BSD/GNU
`ps -axo pid=,pgid=,stat=` fallback. The fallback does not assume exit zero
means usable output: every nonempty row must have numeric PID and PGID plus a
state field. Empty or malformed successful output fails closed.

State is classified by its first character on the fallback and as the exact
field-3 character on Linux. `Z` and Linux `X` are dead and do not count as live
group members. A missing proc entry is dead; an extant but unreadable or
malformed proc entry is unknown and therefore blocks reclaim immediately.
The only polled metadata gap is the bounded, expected interval between
creating a reclaim guard directory and atomically publishing its owner record.

Non-interactive Bash job control places the launched producer in a group whose
PGID is the producer leader PID. Tests wait until the supervisor has atomically
published that exact `group` record and its `marker` record before killing the
supervisor; a worker-created PID file alone is not proof that publication has
finished. A descendant may escape the PGID with `setsid`, so PGID membership is
not the only fence: the inherited marker is scanned independently.

Linux first derives a bounded PID candidate set from the recorded process
group and leader starttime: live members of that exact group plus live
PID-1-reparented processes whose field-22 starttime is not older than the
leader. Only those candidates have their descriptor directories scanned, and
all of each candidate's descriptors are checked. The supervisor therefore
does not traverse every same-UID process descriptor table. An unreadable
descriptor table or link for an extant candidate is unknown and blocks
reclaim. Hosts without procfs use `lsof`. Contract tests source the production
process-control library with a synthetic procfs root; the supervisor's
production root remains fixed at `/proc` so callers cannot redirect the fence
to an empty view.

`kill -0` proves that a PID is allocated and signalable, not that it is
runnable: Linux keeps returning success for an unreaped zombie. Generic PID
liveness therefore qualifies `kill -0` with the same proc stat snapshot on
Linux and `ps stat` on hosts without procfs. The test helper uses the same proc
stat rule on Linux and `Process.HasExited` on macOS. This permits reclaim on
runners whose PID 1 delays orphan reaping without weakening the requirement
that every non-zombie group or marker member keeps the slot.

## Stall observation contract

The supervisor samples aggregate process-group CPU plus `.olean`, producer-log,
relayed stdout, and relayed stderr progress. Consecutive windows with no change
emit a `stall observed` diagnostic. Sampling failure disables only the
observation and emits a diagnostic. Neither outcome changes the worker exit
code or signals the worker tree.

## RED transcript

Before the scope reduction, the focused command selected these three cases:

```text
SigkillOrphanKeepsSlotUntilTheWholeProcessGroupIsDead
LiveClosedFdDescendantPreventsReclaimWithoutBeingKilled
StalledProducerIsObservedWithoutBeingKilled
```

The old implementation produced `3 total, 0 passed, 3 failed`. Both dead-owner
cases expected the contender to time out with `2`, but stale reclaim killed the
remaining live process and returned `0`. The stall case expected the worker to
complete with `0`, but the destructive watchdog killed it and returned `2`.

The final tests use bounded condition polling for process, complete slot
metadata, concurrent supervisor readiness, and slot state. Concurrent workers
use an explicit release file after both run directories exist. The closed-FD
descendant is likewise released explicitly and polled until it is no longer
non-zombie. Tests do not use fixed sleeps to guess publication, overlap, or
orphan cleanup timing.
