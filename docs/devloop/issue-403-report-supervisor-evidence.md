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

The final tests use condition polling for process and slot state. They do not
use fixed sleeps to guess when orphan cleanup has completed.
