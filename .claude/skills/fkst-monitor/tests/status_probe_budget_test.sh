#!/usr/bin/env bash
# Regression test: the backlog probe must be time-bounded, and exceeding the bound must degrade.
#
# Measured 2026-07-30T14:2xZ on the live host: `fkst-framework observe --durable-root …` returned exit 0
# after **79 seconds**, while a `status.sh` run minutes earlier completed in 27s. The probe's latency is
# variable and grows with the backlog it is reporting on — the durable db was 54 MB with 14k+ pending
# entries at the time. `status.sh` placed no upper bound on that call, so as the backlog grows the health
# snapshot blocks for longer and longer, and under `--watch` (or any automated caller) it eventually just
# stops reporting. A monitor that hangs is worse than one that says DEGRADED: silence reads as "nothing to
# report".
#
# Note the distinction from the wall-clock defects filed as #602 / #608. Those are *fixed sleeps followed
# by one check* — waiting a guessed duration for a condition, which fails under load. Bounding an external
# call is the opposite and is correct: the budget is generous, configurable, and exceeding it is reported
# as a probe failure rather than silently absorbed. Fail-closed either way (see status_probe_failure_test).
#
# `timeout(1)` is NOT used: it is absent from a base macOS install (present here only via Homebrew
# coreutils at /opt/homebrew/bin/timeout), and this repo must bring up a second host without host-specific
# tool assumptions. The bound is implemented in plain bash.
#
# Asserts:
#   - a probe that outruns the budget degrades the verdict and names the timeout as the cause
#   - the snapshot still terminates promptly rather than waiting for the probe
#   - a probe that answers within budget behaves exactly as before (no spurious degradation)
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
STATUS_SH="${STATUS_SH:-$SCRIPT_DIR/../scripts/status.sh}"

fail() { echo "FAIL: $1" >&2; exit 1; }

tmpdir="$(mktemp -d -t fkst-monitor-budget.XXXXXX)"
cleanup() { rm -rf "$tmpdir"; }
trap cleanup EXIT

mkdir -p "$tmpdir/logs" "$tmpdir/durable" "$tmpdir/bin"
cat > "$tmpdir/logs/supervise-launchd.log" <<'LOG'
exec: /x/fkst-substrate/target/debug/fkst-framework supervise --project-root /x/checkout --package-root /x
TIMESTAMP=2026-07-30T00:00:00Z LEVEL=INFO package_roots=["/live/instance"] MSG=compose
TIMESTAMP=2026-07-30T00:00:10Z LEVEL=INFO MSG=delivery acked
LOG

mkdir -p "$tmpdir/repo/.claude/skills/fkst-monitor/scripts" "$tmpdir/repo/.fkst/scripts"
cp "$STATUS_SH" "$tmpdir/repo/.claude/skills/fkst-monitor/scripts/status.sh"
cat > "$tmpdir/repo/.fkst/scripts/run.sh" <<'RUN'
#!/usr/bin/env bash
echo "supervise running pid=$$"
RUN
chmod +x "$tmpdir/repo/.fkst/scripts/run.sh"
STATUS_UNDER_TEST="$tmpdir/repo/.claude/skills/fkst-monitor/scripts/status.sh"

# Stub observe. FIXTURE=slow reproduces the measured behaviour: a correct answer, arriving far too late.
cat > "$tmpdir/bin/fkst-framework" <<'BIN'
#!/usr/bin/env bash
if [[ "${FIXTURE:-fast}" == "slow" ]]; then
  sleep "${STUB_SLEEP:-30}"
fi
cat <<'OUT'
delivery queue snapshot only
queues
  queue=github-proxy.github_issue_observed depth=48 pending=47 in_flight=1 retrying=0 oldest_pending_age_ms=12000 subscriber_status=current
dead_letters
OUT
BIN
chmod +x "$tmpdir/bin/fkst-framework"

run_status() { # $1=FIXTURE $2=budget seconds
  FIXTURE="$1" STUB_SLEEP=30 FKST_OBSERVE_BUDGET_S="$2" \
  FKST_HOME="$tmpdir" BIN="$tmpdir/bin/fkst-framework" \
  bash "$STATUS_UNDER_TEST" 2>&1 || true
}

# --- a probe that outruns its budget must degrade, and must not hold the snapshot hostage ---
start="$(date +%s)"
out_slow="$(run_status slow 2)"
elapsed=$(( $(date +%s) - start ))

grep -qE 'verdict *: *(DEGRADED|DOWN|UNKNOWN)' <<<"$out_slow" \
  || fail "a probe that exceeded its budget must not leave the verdict HEALTHY. Output:
$out_slow"
grep -qiE 'budget|timed out|timeout|exceeded' <<<"$out_slow" \
  || fail "the reported cause must name the exceeded budget, so the reader is not sent hunting elsewhere. Output:
$out_slow"
if (( elapsed > 20 )); then
  fail "the snapshot waited ${elapsed}s on a 2s budget against a 30s stub — the bound is not enforced."
fi

# --- a probe that answers within budget must behave exactly as before ---
out_fast="$(run_status fast 60)"
grep -qE 'verdict *: *HEALTHY' <<<"$out_fast" \
  || fail "a prompt probe over a current consumer must still read HEALTHY — the bound must not fire early. Output:
$out_fast"
grep -qE 'backlog' <<<"$out_fast" \
  || fail "a prompt probe must still produce the backlog line. Output:
$out_fast"

echo "PASS: the backlog probe is bounded; exceeding the budget degrades and is named; a prompt probe is unaffected"
