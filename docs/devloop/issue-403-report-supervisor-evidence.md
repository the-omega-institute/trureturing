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

- `ps -axo pid=,pgid=,stat=` has no non-zombie member of the exact recorded
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

The process-group view uses the common BSD/GNU `ps -axo pid=,pgid=,stat=`
shape, but does not assume that exit zero means the output is usable. Every
nonempty row must contain exactly numeric PID and PGID fields plus a state
field. Empty or malformed successful output fails closed. State is classified
by its first character, so both BSD `Z` and GNU/Linux forms such as `Z+` are
zombies and do not count as live group members.

Non-interactive Bash job control places the launched producer in a group whose
PGID is the producer leader PID. Tests wait until the supervisor has atomically
published that exact `group` record and its `marker` record before killing the
supervisor; a worker-created PID file alone is not proof that publication has
finished. A descendant may escape the PGID with `setsid`, so PGID membership is
not the only fence: the inherited marker is scanned independently.

Linux scans procfs, including every descriptor rather than only the original
1, 2, and 9 descriptor numbers. Foreign-UID processes such as PID 1 are outside
the unprivileged supervisor's inheritance domain and are excluded by their
readable `status` UID. Missing or malformed UID state, or unreadable descriptor
state for a same-UID process that still exists, fails closed. Hosts without
procfs use `lsof`. Contract tests source the production process-control library
with a synthetic procfs root; the supervisor's production root remains fixed at
`/proc` so callers cannot redirect the fence to an empty view.

`kill -0` proves that a PID is allocated and signalable, not that it is
runnable: Linux keeps returning success for an unreaped zombie. Generic PID
liveness therefore qualifies `kill -0` with `/proc/<pid>/stat` on Linux and
`ps stat` on hosts without procfs; both `Z*` and the Linux dead state `X` are
dead. The test helper uses the same proc stat rule on Linux and
`Process.HasExited` on macOS. This permits reclaim on runners whose PID 1 delays
orphan reaping without weakening the requirement that every non-zombie group
or marker member keeps the slot.

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

The final tests use condition polling for process, complete slot metadata, and
slot state. The closed-FD descendant is held by an explicit release file, then
released by the test and polled until it is no longer non-zombie. They do not
use fixed sleeps to guess when publication or orphan cleanup has completed.
