#!/usr/bin/env bash
# Regression test: JSON must distinguish an unmeasured durable probe from measured zeroes.
#
# `status.sh --json` used to initialize the durable counters to zero and serialize those zeroes even
# when `observe` never produced a measurement. A consumer could therefore read `"dlq":0` as proof
# that the dead-letter queue had drained when the probe had timed out, was missing, or exited non-zero.
#
# Asserts:
#   - every failed-probe path reports observe_ok=false, null durable counters, and the failure reason
#   - a successful probe reports observe_ok=true and the actual measured integer values
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
STATUS_SH="${STATUS_SH:-$SCRIPT_DIR/../scripts/status.sh}"

tmpdir="$(mktemp -d -t fkst-monitor-json.XXXXXX)"
cleanup() { rm -rf "$tmpdir"; }
trap cleanup EXIT

mkdir -p "$tmpdir/logs" "$tmpdir/durable" "$tmpdir/bin" "$tmpdir/dotnet-bin" \
  "$tmpdir/checkout/Meta/StrataLint/StrataLint.Cli"
touch "$tmpdir/checkout/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"
cat > "$tmpdir/logs/supervise-launchd.log" <<'LOG'
exec: /x/fkst-substrate/target/debug/fkst-framework supervise --project-root /x/checkout --package-root /x
TIMESTAMP=2026-08-02T00:00:00Z LEVEL=INFO package_roots=["/live/instance"] MSG=compose
TIMESTAMP=2026-08-02T00:00:10Z LEVEL=INFO MSG=delivery acked
LOG

mkdir -p "$tmpdir/repo/.claude/skills/fkst-monitor/scripts" "$tmpdir/repo/.fkst/scripts"
cp "$STATUS_SH" "$tmpdir/repo/.claude/skills/fkst-monitor/scripts/status.sh"
cat > "$tmpdir/repo/.fkst/scripts/run.sh" <<'RUN'
#!/usr/bin/env bash
echo "supervise running pid=$$"
RUN
chmod +x "$tmpdir/repo/.fkst/scripts/run.sh"
STATUS_UNDER_TEST="$tmpdir/repo/.claude/skills/fkst-monitor/scripts/status.sh"

cat > "$tmpdir/bin/fkst-framework" <<'BIN'
#!/usr/bin/env bash
case "${FIXTURE:-measured}" in
  slow)
    sleep 30
    ;;
  failed)
    printf 'backend "locked": cannot read C:\\cache\n' >&2
    exit 7
    ;;
esac
cat <<'OUT'
delivery queue snapshot only
queues
  queue=alpha depth=4 pending=3 in_flight=1 retrying=2 oldest_pending_age_ms=1000 subscriber_status=current
  queue=beta depth=6 pending=5 in_flight=1 retrying=5 oldest_pending_age_ms=2000 subscriber_status=absent
dead_letters
  id=dead-1
  id=dead-2
OUT
BIN
chmod +x "$tmpdir/bin/fkst-framework"
cat > "$tmpdir/dotnet-bin/dotnet" <<'DOTNET'
#!/usr/bin/env bash
printf '{"schema":"stratalint-formalize-candidates-v2","candidates":[]}\n'
DOTNET
chmod +x "$tmpdir/dotnet-bin/dotnet"

run_status() { # $1=fixture $2=BIN $3=budget
  FIXTURE="$1" FKST_OBSERVE_BUDGET_S="$3" \
  PATH="$tmpdir/dotnet-bin:$PATH" \
  FKST_HOME="$tmpdir" BIN="$2" \
  bash "$STATUS_UNDER_TEST" --json 2>&1 || true
}

failures=0
record_failure() {
  echo "FAIL: $1" >&2
  failures=$(( failures + 1 ))
}

assert_unmeasured() { # $1=name $2=json $3=reason regex
  local name="$1" json="$2" reason_re="$3"
  if ! jq -e --arg reason_re "$reason_re" '
    .observe_ok == false and
    .dlq == null and
    .retrying == null and
    .absent_subscribers == null and
    (.observe_error | type == "string" and test($reason_re; "i"))
  ' <<<"$json" >/dev/null 2>&1; then
    record_failure "$name must carry observe_ok=false, null durable counters, and its reason. Output: $json"
  fi
}

out_budget="$(run_status slow "$tmpdir/bin/fkst-framework" 1)"
assert_unmeasured "budget-exceeded probe" "$out_budget" 'exceeded 1s budget'

out_missing="$(run_status measured "$tmpdir/bin/does-not-exist" 10)"
assert_unmeasured "missing-binary probe" "$out_missing" 'binary not found'

out_failed="$(run_status failed "$tmpdir/bin/fkst-framework" 10)"
assert_unmeasured "non-zero probe" "$out_failed" 'failed.*exit 7.*backend.*locked'

out_measured="$(run_status measured "$tmpdir/bin/fkst-framework" 10)"
if ! jq -e '
  .observe_ok == true and
  .observe_error == null and
  .dlq == 2 and (.dlq | type == "number") and
  .retrying == 7 and (.retrying | type == "number") and
  .absent_subscribers == 1 and (.absent_subscribers | type == "number")
' <<<"$out_measured" >/dev/null 2>&1; then
  record_failure "successful probe must report its real measured integer values. Output: $out_measured"
fi

if (( failures > 0 )); then
  echo "FAIL: $failures JSON probe-measurement scenario(s) violated the contract" >&2
  exit 1
fi

echo "PASS: JSON distinguishes three unmeasured probe failures from measured durable values"
