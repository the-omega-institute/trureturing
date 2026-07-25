# Issue 403 report supervisor evidence

This file preserves the safety argument and the RED evidence used to change the
Lean-slot lease and watchdog. It is review evidence, not executable policy.

## Process-group reclaim contract

Each canonical slot records `PGID|leader-pid|leader-start`. Before a stale slot
is detached, the reclaimer reads the process table with
`ps -axo pid=,pgid=,stat=` and selects every non-zombie member of that exact
PGID. A live leader must still have the recorded start identity; a mismatch or
an unreadable table fails closed so a reused group is not signalled.

If the recorded group is nonempty, reclaim sends SIGTERM to the group, waits a
grace period, enumerates the group again, sends SIGKILL when members remain,
and performs a final enumeration. Reclaim proceeds only when that final PID
table is empty. Inherited marker and pipe FDs are retained as an auxiliary way
to find escaped sessions, but an empty marker scan is never evidence that the
recorded process group is empty.

## Watchdog sampling contract

The portable CPU source is `ps -o time=`, which can expose cumulative CPU only
in whole seconds. A stall window is therefore at least 60 seconds. A low-duty
build that accumulates at least one CPU second per minute must cross one whole
second display quantum inside such a window. The watchdog requires at least
three consecutive windows to reduce boundary races.

A window counts as stalled only when both conditions hold throughout it:

- aggregate supervised-process CPU has no observed change; and
- all `.olean`, producer-log, relayed stdout, and relayed stderr snapshots have
  no observed change.

Any CPU change, including a decrease caused by process membership churn, is
treated conservatively as activity. Any other signal change resets the
consecutive-stall count. Unavailable sampling disables destructive watchdog
action rather than guessing.

## Durable RED transcript summary

The old implementation was exact commit
`e791c71d082eb610bc628103a6043a71906267ba`. Its archived tree was overlaid
only with the focused regression source later committed with blob
`5284fb559ef105b78118509ba04453abf38979e7`, then the following 12-test filter
was run. The observed result was `12 total, 4 passed, 8 failed` in 37.4875
seconds.

Failed cases and decisive output:

```text
OneFailedRenewalWriteIsRetriedInsideTheRemainingLeaseWindow
  Expected: 0; Actual: 2
ExpiredCanonicalLeaseWithoutProducerFenceIsNotReclaimed
  Expected: 2; Actual: 0
LiveLegacyPidAndStartOwnerIsNeverExpired
  Expected: 2; Actual: 0
MalformedNonemptyOwnerFailsClosed
  Expected: 2; Actual: 0
LiveLegacyPidOwnerIsNeverExpired
  Expected: 2; Actual: 0
SigkillOrphanedHolderReleasesItsLeaseToTheNextAcquirer
  Assert.True failure: Expected True; Actual False
UnknownCanonicalLiveOwnerCannotBeReclaimedOnTimeout
  Assert.True failure: Expected True; Actual False
CpuActiveMathlibScalePhaseOutlivingTheStallThresholdIsNeverKilled
  Expected: 0; Actual: 2
```

Passed cases in the same old-tree run:

```text
ManualBashInvocationWatchdogFailureReturnsAndRecordsExactlyTwo
ThreeFieldOwnerWhosePidWasReusedIsReclaimed
DirectSingleProcessWatchdogFailureReturnsAndRecordsExactlyTwo
FaultInjectedPartialLakeArtifactIsRebuiltAndImportableOnTheNextBuild
```

The old implementation was also invoked directly outside VSTest with a
single sleeping producer. The trace reached the watchdog diagnostic and then
escaped from termination under `set -e`; both externally observed and recorded
results were wrong:

```text
report-supervisor: infrastructure failure: no Lean progress for 2s
rc=126
metric_rc=126
```

The focused command selected these names explicitly:

```text
ExpiredCanonicalLeaseWithoutProducerFenceIsNotReclaimed
SigkillOrphanedHolderReleasesItsLeaseToTheNextAcquirer
CpuActiveMathlibScalePhaseOutlivingTheStallThresholdIsNeverKilled
DirectSingleProcessWatchdogFailureReturnsAndRecordsExactlyTwo
ManualBashInvocationWatchdogFailureReturnsAndRecordsExactlyTwo
LiveLegacyPidAndStartOwnerIsNeverExpired
LiveLegacyPidOwnerIsNeverExpired
MalformedNonemptyOwnerFailsClosed
UnknownCanonicalLiveOwnerCannotBeReclaimedOnTimeout
ThreeFieldOwnerWhosePidWasReusedIsReclaimed
OneFailedRenewalWriteIsRetriedInsideTheRemainingLeaseWindow
FaultInjectedPartialLakeArtifactIsRebuiltAndImportableOnTheNextBuild
```
