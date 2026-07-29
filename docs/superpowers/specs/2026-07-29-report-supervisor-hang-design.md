# Report Supervisor Hang Design

## Problem and Evidence

`TerminationReapsADescendantThatCreatesANewSession` can fail and leave its
supervisor alive. The leaked process keeps the test job from completing, so an
outer devloop watchdog eventually reports `Hangup` instead of a typed failure.
The production supervisor also discovers and signals descendants in one
pipeline; killing an ancestor can reparent a `setsid` descendant before the
same scan reaches it.

The current test neither drains redirected output nor terminates the supervisor
from `finally`. The current supervisor retains no process identity between
normal sampling and termination. PR #452 commit `8105229` records PID/start
identity pairs for this case. Commits `324731a` and `56dc5ae` use an independent
timer watchdog and remove xUnit `Timeout`, which cannot bound a blocked
synchronous test body.

The restricted local sandbox separately denies VSTest loopback sockets and
`ps`. Direct invocation of the exact test body therefore reaches a readiness
failure in about 10 seconds. That is environment evidence, not a substitute
for the #499 Hangup evidence.

## Design

The supervisor creates a private candidate file per run. Every normal sample
records each observed process as `PID|start identity`. Termination revalidates
each identity and signals matching records before the existing marker and
process-group fallbacks. PID reuse fails closed.

The fixture models worker -> helper parent -> `setsid` child and supplies
fixture-scoped `ps` and `pgrep` views. The child closes stdout, stderr, and fd 9,
then becomes orphaned before supervisor termination. This prevents marker or
process-group discovery from making the test pass accidentally.

The target test drains output through an independent timer watchdog. Every
assertion path cleans up the supervisor and detached PID in `finally`. Timeout
produces an explicit xUnit failure with bounded output tails; it does not use
xUnit `Timeout`.

## Verification

The strengthened test must fail against the old supervisor because no
candidate file exists, then pass after the production change. A watchdog unit
test proves a tracked long-running process is killed and reported explicitly.
Run focused stress, related tests, warning-as-error build, and preflight where
the sandbox permits their process/socket capabilities.
