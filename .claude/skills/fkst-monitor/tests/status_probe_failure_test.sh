#!/usr/bin/env bash
# Regression test: a probe that CANNOT RUN must never be reported as a clean bill of health.
#
# Observed 2026-07-30T12:12Z: this snapshot printed
#   verdict     : HEALTHY
#   durable     : (observe unavailable — BIN or durable root missing)
# while BOTH the binary and the durable root existed. `observe` had exited 2 with
#   [framework] startup error: open existing durable delivery database `.../delivery.redb`:
#   Database already open. Cannot acquire ...
# because the running engine held the redb lock.
#
# Two defects in one line, and they compound:
#   1. MISATTRIBUTION — the message blames absent prerequisites when the real cause is a failing probe.
#      A reader who trusts it goes looking for a missing file that is right there.
#   2. DETECTION DOWNGRADE — `observe` is the *only* source of the backlog-lag check that exists
#      precisely to stop this tool reporting HEALTHY over a 26-hour consumer lag (see
#      status_backlog_lag_test.sh). When the probe fails, that check silently does not run and the
#      verdict flips to HEALTHY — not because the backlog cleared, but because nothing looked.
#      A green light earned by not looking is worse than a red one: it retires the check invisibly.
#
# Fail-closed is the only honest shape: an unavailable probe degrades the verdict and says why, in the
# probe's own words. Asserts:
#   - observe failing (non-zero exit) does NOT leave the verdict HEALTHY
#   - the probe's real error text is surfaced, not a fabricated "missing" cause
#   - a genuinely missing binary / durable root also degrades, and says which prerequisite is absent
#   - a working probe over a current consumer still reads HEALTHY, so this cannot fire spuriously
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
STATUS_SH="${STATUS_SH:-$SCRIPT_DIR/../scripts/status.sh}"

fail() { echo "FAIL: $1" >&2; exit 1; }

tmpdir="$(mktemp -d -t fkst-monitor-probe.XXXXXX)"
cleanup() { rm -rf "$tmpdir"; }
trap cleanup EXIT

mkdir -p "$tmpdir/logs" "$tmpdir/durable" "$tmpdir/bin" "$tmpdir/dotnet-bin" \
  "$tmpdir/checkout/Meta/StrataLint/StrataLint.Cli"
touch "$tmpdir/checkout/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"
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

# Stub `observe`. FIXTURE=locked reproduces the real failure: exit 2, message on stderr, nothing on stdout.
cat > "$tmpdir/bin/fkst-framework" <<'BIN'
#!/usr/bin/env bash
case "${FIXTURE:-healthy}" in
  locked)
    echo "[framework] startup error: open existing durable delivery database \`/x/durable/delivery.redb\`: Database already open. Cannot acquire exclusive lock" >&2
    exit 2
    ;;
  *)
    cat <<'OUT'
delivery queue snapshot only
queues
  queue=github-proxy.github_issue_observed depth=48 pending=47 in_flight=1 retrying=0 oldest_pending_age_ms=12000 subscriber_status=current
dead_letters
OUT
    ;;
esac
BIN
chmod +x "$tmpdir/bin/fkst-framework"
cat > "$tmpdir/dotnet-bin/dotnet" <<'DOTNET'
#!/usr/bin/env bash
printf '{"schema":"stratalint-formalize-candidates-v2","candidates":[]}\n'
DOTNET
chmod +x "$tmpdir/dotnet-bin/dotnet"

run_status() { # $1=FIXTURE $2=BIN override (optional) $3=FKST_HOME override (optional)
  FIXTURE="$1" \
  PATH="$tmpdir/dotnet-bin:$PATH" \
  FKST_HOME="${3:-$tmpdir}" \
  BIN="${2:-$tmpdir/bin/fkst-framework}" \
  bash "$STATUS_UNDER_TEST" 2>&1 || true
}

# --- a probe that cannot run must not yield a green light ---
out="$(run_status locked)"
grep -qE 'verdict *: *(DEGRADED|DOWN|UNKNOWN)' <<<"$out" \
  || fail "observe exiting non-zero must NOT leave the verdict HEALTHY — a check that did not run is not a pass. Output:
$out"

# --- and it must say why, in the probe's own words, rather than inventing a missing prerequisite ---
grep -qiE 'already open|Cannot acquire|exit 2|observe failed' <<<"$out" \
  || fail "the probe's real error must be surfaced so the reader can act on the actual cause. Output:
$out"
if grep -qi 'BIN or durable root missing' <<<"$out"; then
  fail "misattribution: the binary and durable root both exist; reporting them as missing sends the reader after a file that is right there. Output:
$out"
fi

# --- a genuinely absent binary must also degrade, and name the real prerequisite ---
out_nobin="$(run_status healthy "$tmpdir/bin/does-not-exist")"
grep -qE 'verdict *: *(DEGRADED|DOWN|UNKNOWN)' <<<"$out_nobin" \
  || fail "an absent observe binary leaves the backlog check unrun; that cannot read HEALTHY. Output:
$out_nobin"

# --- a genuinely absent durable root must also degrade ---
mkdir -p "$tmpdir/nodurable/logs"
cp "$tmpdir/logs/supervise-launchd.log" "$tmpdir/nodurable/logs/"
out_noroot="$(run_status healthy "$tmpdir/bin/fkst-framework" "$tmpdir/nodurable")"
grep -qE 'verdict *: *(DEGRADED|DOWN|UNKNOWN)' <<<"$out_noroot" \
  || fail "an absent durable root leaves the backlog check unrun; that cannot read HEALTHY. Output:
$out_noroot"

# --- a working probe over a current consumer still reads HEALTHY: the guard cannot fire spuriously ---
out_ok="$(run_status healthy)"
grep -qE 'verdict *: *HEALTHY' <<<"$out_ok" \
  || fail "a working probe over a current consumer must still read HEALTHY. Output:
$out_ok"

echo "PASS: an unavailable probe degrades the verdict and reports its real cause; a working probe still reads HEALTHY"
