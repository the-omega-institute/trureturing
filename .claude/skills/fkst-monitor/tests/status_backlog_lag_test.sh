#!/usr/bin/env bash
# Regression test: the health snapshot must not report HEALTHY while a consumer is hours behind.
#
# Observed 2026-07-30: status.sh reported HEALTHY with
#   queue=github-proxy.github_issue_observed depth=11207 pending=11191 in_flight=16
#     oldest_pending_age_ms=93266721 subscriber_status=current
# i.e. the oldest pending observation was 25.9 HOURS old on a queue whose entries are superseded every
# 300s, and growing ~1080/hour. A newly created issue's observation sat behind ~11,000 superseded
# entries, so it was unreachable — the pipeline was busy and none of it was current.
#
# None of the signals the snapshot already had could see this: liveness was fine, no fatals, no
# dead-letter growth, acks flowing, CPU idle. "Busy and current" and "busy and hopelessly behind" look
# identical unless backlog lag is measured. That is exactly a bad-raw-material defect in this tool: the
# reader cannot be blamed for trusting a verdict the tool computed without the one number that mattered.
#
# `oldest_pending_age_ms` is the honest signal — it answers "is the consumer current?" directly and is
# immune to arguments about what `depth` counts. Asserts:
#   - a queue whose oldest pending entry exceeds the lag threshold downgrades the verdict and is named
#   - the backlog line reports the worst queue, its pending count, and its lag
#   - deep-but-fresh (large pending, tiny age) does NOT downgrade — depth alone is not the defect
#   - a healthy fixture stays HEALTHY, so the check cannot fire spuriously
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
STATUS_SH="${STATUS_SH:-$SCRIPT_DIR/../scripts/status.sh}"

fail() { echo "FAIL: $1" >&2; exit 1; }

tmpdir="$(mktemp -d -t fkst-monitor-backlog.XXXXXX)"
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

# `run.sh status` is invoked as "$RUN_SH status"; REPO_ROOT is derived from the script location, so point
# the fixture's own tree at a stub that reports a live pid.
mkdir -p "$tmpdir/repo/.claude/skills/fkst-monitor/scripts" "$tmpdir/repo/.fkst/scripts"
cp "$STATUS_SH" "$tmpdir/repo/.claude/skills/fkst-monitor/scripts/status.sh"
cat > "$tmpdir/repo/.fkst/scripts/run.sh" <<'RUN'
#!/usr/bin/env bash
echo "supervise running pid=$$"
RUN
chmod +x "$tmpdir/repo/.fkst/scripts/run.sh"
STATUS_UNDER_TEST="$tmpdir/repo/.claude/skills/fkst-monitor/scripts/status.sh"

# Stub `observe`: first arg set decides which fixture to emit, chosen via an env var.
cat > "$tmpdir/bin/fkst-framework" <<'BIN'
#!/usr/bin/env bash
case "${FIXTURE:-healthy}" in
  behind)
    cat <<'OUT'
delivery queue snapshot only
queues
  queue=github-proxy.github_poll_tick depth=1 pending=0 in_flight=1 retrying=0 oldest_pending_age_ms=- subscriber_status=current
  queue=github-proxy.github_issue_observed depth=11207 pending=11191 in_flight=16 retrying=0 oldest_pending_age_ms=93266721 subscriber_status=current
dead_letters
OUT
    ;;
  deep_but_fresh)
    cat <<'OUT'
delivery queue snapshot only
queues
  queue=github-proxy.github_issue_observed depth=9000 pending=9000 in_flight=0 retrying=0 oldest_pending_age_ms=4000 subscriber_status=current
dead_letters
OUT
    ;;
  *)
    cat <<'OUT'
delivery queue snapshot only
queues
  queue=github-proxy.github_poll_tick depth=1 pending=0 in_flight=1 retrying=0 oldest_pending_age_ms=- subscriber_status=current
  queue=github-proxy.github_issue_observed depth=48 pending=47 in_flight=1 retrying=0 oldest_pending_age_ms=12000 subscriber_status=current
dead_letters
OUT
    ;;
esac
BIN
chmod +x "$tmpdir/bin/fkst-framework"
cat > "$tmpdir/dotnet-bin/dotnet" <<'DOTNET'
#!/usr/bin/env bash
printf '{"schema":"stratalint-formalize-candidates-v3","candidates":[],"recorded_formalizations":[],"withheld":[]}\n'
DOTNET
chmod +x "$tmpdir/dotnet-bin/dotnet"

run_status() { FIXTURE="$1" PATH="$tmpdir/dotnet-bin:$PATH" FKST_HOME="$tmpdir" BIN="$tmpdir/bin/fkst-framework" bash "$STATUS_UNDER_TEST" 2>&1 || true; }

# --- a consumer 25.9h behind must NOT read as HEALTHY ---
out="$(run_status behind)"
grep -qE 'verdict *: *(DEGRADED|DOWN)' <<<"$out" \
  || fail "a 25.9h-behind consumer must not be HEALTHY. Output:
$out"
grep -q 'github_issue_observed' <<<"$out" \
  || fail "the offending queue must be named. Output:
$out"
grep -qE 'backlog' <<<"$out" \
  || fail "a backlog line must be reported. Output:
$out"
grep -qE '11191|11207' <<<"$out" \
  || fail "the pending/depth count must be reported. Output:
$out"

# --- depth alone is not the defect: deep but fresh stays HEALTHY ---
out_fresh="$(run_status deep_but_fresh)"
grep -qE 'verdict *: *HEALTHY' <<<"$out_fresh" \
  || fail "a deep but FRESH queue (age 4s) must stay HEALTHY — lag, not depth, is the signal. Output:
$out_fresh"

# --- a current consumer stays HEALTHY, so the check cannot fire spuriously ---
out_ok="$(run_status healthy)"
grep -qE 'verdict *: *HEALTHY' <<<"$out_ok" \
  || fail "a current consumer must stay HEALTHY. Output:
$out_ok"

echo "PASS: backlog lag downgrades the verdict and names the queue; depth alone and a current consumer do not"
