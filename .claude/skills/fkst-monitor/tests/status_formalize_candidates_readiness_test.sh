#!/usr/bin/env bash
# Regression test: formalize-candidate readiness is measured by digest-status, bounded, and explicit.
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
STATUS_SH="${STATUS_SH:-$SCRIPT_DIR/../scripts/status.sh}"

fail() { echo "FAIL: $1" >&2; exit 1; }

tmpdir="$(mktemp -d -t fkst-monitor-formalize.XXXXXX)"
cleanup() { rm -rf "$tmpdir"; }
trap cleanup EXIT

mkdir -p \
  "$tmpdir/logs" \
  "$tmpdir/durable" \
  "$tmpdir/bin" \
  "$tmpdir/checkout/Meta/StrataLint/StrataLint.Cli" \
  "$tmpdir/repo/.claude/skills/fkst-monitor/scripts" \
  "$tmpdir/repo/.fkst/scripts"
touch "$tmpdir/checkout/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"
cat > "$tmpdir/logs/supervise-launchd.log" <<'LOG'
exec: /x/fkst-substrate/target/debug/fkst-framework supervise --project-root /x/checkout --package-root /x
TIMESTAMP=2026-08-04T00:00:00Z LEVEL=INFO package_roots=["/live/instance"] MSG=compose
TIMESTAMP=2026-08-04T00:00:10Z LEVEL=INFO MSG=delivery acked
LOG
cp "$STATUS_SH" "$tmpdir/repo/.claude/skills/fkst-monitor/scripts/status.sh"
cat > "$tmpdir/repo/.fkst/scripts/run.sh" <<'RUN'
#!/usr/bin/env bash
echo "supervise running pid=$$"
RUN
chmod +x "$tmpdir/repo/.fkst/scripts/run.sh"
STATUS_UNDER_TEST="$tmpdir/repo/.claude/skills/fkst-monitor/scripts/status.sh"

cat > "$tmpdir/bin/fkst-framework" <<'BIN'
#!/usr/bin/env bash
cat <<'OUT'
delivery queue snapshot only
queues
  queue=alpha depth=0 pending=0 in_flight=0 retrying=0 oldest_pending_age_ms=- subscriber_status=current
dead_letters
OUT
BIN
cat > "$tmpdir/bin/dotnet" <<'DOTNET'
#!/usr/bin/env bash
printf '%s\n' "$PWD|$*" >> "$DOTNET_CALLS"
case "${FORMALIZE_FIXTURE:-ready}" in
  ready)
    printf '{"schema":"stratalint-formalize-candidates-v2","candidates":[]}\n'
    ;;
  invalid)
    printf 'DIGEST_STATUS_INVALID Raw Lean report source hash does not match D5/Changed.lean.\n' >&2
    exit 1
    ;;
  slow)
    sleep 30
    ;;
esac
DOTNET
chmod +x "$tmpdir/bin/fkst-framework" "$tmpdir/bin/dotnet"

run_status() { # $1=fixture $2=mode $3=budget
  FORMALIZE_FIXTURE="$1" DOTNET_CALLS="$tmpdir/dotnet.calls" \
  PATH="$tmpdir/bin:$PATH" FKST_HOME="$tmpdir" BIN="$tmpdir/bin/fkst-framework" \
  FKST_FORMALIZE_CANDIDATES_BUDGET_S="$3" \
  bash "$STATUS_UNDER_TEST" "$2" 2>&1 || true
}

out_ready="$(run_status ready --json 10)"
jq -e '
  .formalize_candidates_probe_ok == true and
  .formalize_candidates_ready == true and
  .formalize_candidates_error == null
' <<<"$out_ready" >/dev/null 2>&1 \
  || fail "zero candidates from a successful command must be measured READY. Output: $out_ready"
expected_call="$tmpdir/checkout|run --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release --verbosity quiet -- digest-status --formalize-candidates"
grep -qxF "$expected_call" "$tmpdir/dotnet.calls" \
  || fail "readiness probe did not run the canonical command from the deployed checkout"

out_invalid="$(run_status invalid --json 10)"
jq -e '
  .verdict == "DEGRADED" and
  .formalize_candidates_probe_ok == false and
  .formalize_candidates_ready == false and
  (.formalize_candidates_error | test("DIGEST_STATUS_INVALID.*source hash does not match"))
' <<<"$out_invalid" >/dev/null 2>&1 \
  || fail "digest-status rejection must be a measured NOT READY verdict. Output: $out_invalid"
human_invalid="$(run_status invalid --report 10)"
grep -qE 'formalize +: NOT READY.*DIGEST_STATUS_INVALID' <<<"$human_invalid" \
  || fail "human report did not expose measured formalize-candidate failure. Output: $human_invalid"

out_slow="$(run_status slow --json 1)"
jq -e '
  .verdict == "DEGRADED" and
  .formalize_candidates_probe_ok == false and
  .formalize_candidates_ready == null and
  (.formalize_candidates_error | test("exceeded 1s budget"))
' <<<"$out_slow" >/dev/null 2>&1 \
  || fail "timed-out readiness probe must be NOT CHECKED, not false or zero. Output: $out_slow"
human_slow="$(run_status slow --report 1)"
grep -qE 'formalize +: NOT CHECKED.*exceeded 1s budget' <<<"$human_slow" \
  || fail "human report did not distinguish an unrun verdict. Output: $human_slow"

echo "PASS: formalize-candidate readiness is command-derived, bounded, and three-valued in human and JSON output"
