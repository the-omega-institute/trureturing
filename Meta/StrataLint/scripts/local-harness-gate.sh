#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
source "$ROOT/Meta/StrataLint/scripts/perf-event-lib.sh"
CANDIDATE_ROOT="$ROOT"
BASE_REF="origin/dev"
SKIP_ENGINEERING=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate)
      [[ $# -ge 2 ]] || { echo "local-harness-gate: --candidate requires a value" >&2; exit 2; }
      CANDIDATE_ROOT="$2"
      shift 2
      ;;
    --base)
      [[ $# -ge 2 ]] || { echo "local-harness-gate: --base requires a value" >&2; exit 2; }
      BASE_REF="$2"
      shift 2
      ;;
    --skip-engineering)
      [[ "$SKIP_ENGINEERING" == "0" ]] \
        || { echo "local-harness-gate: duplicate --skip-engineering" >&2; exit 2; }
      SKIP_ENGINEERING=1
      shift
      ;;
    *)
      echo "local-harness-gate: unknown arg '$1'" >&2
      exit 2
      ;;
  esac
done

[[ -d "$CANDIDATE_ROOT" ]] \
  || { echo "local-harness-gate: candidate '$CANDIDATE_ROOT' is absent" >&2; exit 2; }
CANDIDATE_ROOT="$(cd "$CANDIDATE_ROOT" && pwd -P)"
export PATH="$HOME/.elan/bin:/usr/local/share/dotnet:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin:${PATH:-}"

GATE_STARTED="$(date +%s)"
TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-local-gate.XXXXXXXX")"
LOCAL_TIMING_FILE="$TMP_ROOT/local-gate-timing.jsonl"
SHARED_TIMING_FILE="$TMP_ROOT/shared-gate-timing.jsonl"
PERF_TMP="$(perf_make_spool_dir "$CANDIDATE_ROOT" stratalint-local-gate-perf 2>/dev/null || true)"
PERF_EVENT_SPOOL=""
JUDGE_ROOT=""
BASE_SHA=""
CREATED_JUDGE=0
: > "$LOCAL_TIMING_FILE"
if [[ -n "$PERF_TMP" ]]; then
  PERF_EVENT_SPOOL="$PERF_TMP/events.jsonl"
  : > "$PERF_EVENT_SPOOL" || PERF_EVENT_SPOOL=""
fi
PERF_COMMIT="$(git -C "$CANDIDATE_ROOT" rev-parse --verify HEAD 2>/dev/null || printf unknown)"
PERF_BASE="$(git -C "$CANDIDATE_ROOT" rev-parse --verify "${BASE_REF}^{commit}" 2>/dev/null || printf unknown)"
PERF_RUN_ID="${STRATALINT_PERF_RUN_ID:-local-${GATE_STARTED}-$$-${PERF_COMMIT:0:12}}"

record_timing() {
  local scope="$1"
  local stage="$2"
  local status="$3"
  local elapsed="$4"
  printf '{"event":"gate_stage_timing","scope":"%s","stage":"%s","status":"%s","elapsed_seconds":%s}\n' \
    "$scope" "$stage" "$status" "$elapsed" >> "$LOCAL_TIMING_FILE" || true
  perf_capture_event \
    "$PERF_EVENT_SPOOL" \
    "$CANDIDATE_ROOT" \
    "$PERF_RUN_ID" \
    "local-harness-gate" \
    "${BASE_SHA:-$PERF_BASE}" \
    "$stage" \
    "$status" \
    "$elapsed" || true
}

run_stage() {
  local stage="$1"
  shift
  local started
  local finished
  local rc
  local status
  started="$(date +%s)"
  set +e
  "$@"
  rc=$?
  set -e
  finished="$(date +%s)"
  status="passed"
  if [[ "$rc" -ne 0 ]]; then status="failed"; fi
  record_timing local "$stage" "$status" "$((finished-started))"
  return "$rc"
}

cleanup() {
  if [[ "$CREATED_JUDGE" == "1" && -n "$JUDGE_ROOT" ]]; then
    git -C "$CANDIDATE_ROOT" worktree remove --force "$JUDGE_ROOT" >/dev/null 2>&1 || true
  fi
  rm -rf -- "$TMP_ROOT"
  if [[ -n "$PERF_TMP" ]]; then rm -rf -- "$PERF_TMP"; fi
}

finish() {
  local rc=$?
  local finished
  local status="failed"
  local timing_payload=""
  trap - EXIT HUP INT TERM
  set +e
  if [[ -s "$SHARED_TIMING_FILE" ]]; then
    cat "$SHARED_TIMING_FILE" >> "$LOCAL_TIMING_FILE"
  fi
  finished="$(date +%s)"
  if [[ "$rc" -eq 0 ]]; then status="passed"; fi
  record_timing local total "$status" "$((finished-GATE_STARTED))"
  if [[ -f "$LOCAL_TIMING_FILE" ]]; then
    timing_payload="$(cat "$LOCAL_TIMING_FILE")"
  fi
  perf_flush_events "$CANDIDATE_ROOT" "$PERF_EVENT_SPOOL" >/dev/null 2>&1 || true
  cleanup
  printf '[local-gate] timing-summary status=%s exit=%s\n' "$status" "$rc" >&2
  if [[ -n "$timing_payload" ]]; then printf '%s\n' "$timing_payload" >&2; fi
  printf '{"event":"gate_timing_summary","status":"%s","exit_code":%s,"elapsed_seconds":%s}\n' \
    "$status" "$rc" "$((finished-GATE_STARTED))" >&2
  exit "$rc"
}

trap finish EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

prepare_judge() {
  local remote="${BASE_REF%%/*}"
  if [[ "$remote" != "$BASE_REF" ]] \
    && git -C "$CANDIDATE_ROOT" remote | grep -Fxq "$remote"; then
    git -C "$CANDIDATE_ROOT" fetch --prune "$remote"
  fi
  BASE_SHA="$(git -C "$CANDIDATE_ROOT" rev-parse --verify "${BASE_REF}^{commit}")"

  local current_path=""
  local current_head=""
  local current_branch=""
  while IFS= read -r -d '' field; do
    case "$field" in
      worktree\ *) current_path="${field#worktree }" ;;
      HEAD\ *) current_head="${field#HEAD }" ;;
      branch\ *) current_branch="${field#branch }" ;;
      "")
        if [[ -z "$JUDGE_ROOT" \
          && "$current_head" == "$BASE_SHA" \
          && "$current_branch" == "refs/heads/dev" \
          && -d "$current_path" ]] \
          && git -C "$current_path" diff --quiet \
          && git -C "$current_path" diff --cached --quiet; then
          JUDGE_ROOT="$current_path"
        fi
        current_path=""
        current_head=""
        current_branch=""
        ;;
    esac
  done < <(git -C "$CANDIDATE_ROOT" worktree list --porcelain -z)

  if [[ -z "$JUDGE_ROOT" ]]; then
    JUDGE_ROOT="$TMP_ROOT/dev-judge"
    git -C "$CANDIDATE_ROOT" worktree add --detach "$JUDGE_ROOT" "$BASE_SHA"
    CREATED_JUDGE=1
    # Warm the freshly-created judge worktree's Lean build cache from the candidate so
    # the baseline report build is INCREMENTAL (rebuild only the base-vs-candidate diffs)
    # instead of a COLD full compile of the whole D5 project. Measured on this repo: a
    # cold baseline build takes ~2h and starves the devloop implement codex (it burns its
    # whole timeout at the `make preflight` finish gate with "no baseline output"), while a
    # warm build is ~8s. lake is content-addressed, so a warmed `.lake` yields byte-identical
    # oleans for unchanged sources and rebuilds exactly the changed ones — the baseline report
    # is the same, only fast. Prefer an APFS clone (near-instant, space-shared) and fall back
    # to a plain copy; never fail the gate on a copy error (that just falls back to the cold
    # build). Only the newly-created judge is warmed; a reused existing worktree is untouched.
    if [[ -d "$CANDIDATE_ROOT/.lake" && ! -e "$JUDGE_ROOT/.lake" ]]; then
      cp -cR "$CANDIDATE_ROOT/.lake" "$JUDGE_ROOT/.lake" 2>/dev/null \
        || cp -R "$CANDIDATE_ROOT/.lake" "$JUDGE_ROOT/.lake" 2>/dev/null \
        || true
    fi
  fi

  printf '[local-gate] candidate=%s judge=%s base=%s\n' \
    "$CANDIDATE_ROOT" "$JUDGE_ROOT" "$BASE_SHA" >&2
}

run_stage setup prepare_judge

if [[ "$SKIP_ENGINEERING" == "1" ]]; then
  record_timing local engineering-dotnet skipped 0
  record_timing local engineering-test skipped 0
  record_timing local engineering-selftest skipped 0
else
  run_stage engineering-dotnet make -C "$CANDIDATE_ROOT" dotnet
  run_stage engineering-test make -C "$CANDIDATE_ROOT" test
  run_stage engineering-selftest make -C "$CANDIDATE_ROOT" selftest
fi

LAKE_BIN="${LAKE_BIN:-$(command -v lake || true)}"
[[ -n "$LAKE_BIN" && "$LAKE_BIN" == /* && -x "$LAKE_BIN" ]] \
  || { echo "local-harness-gate: an absolute lake executable is required" >&2; exit 2; }
REPORTS="$TMP_ROOT/reports"
mkdir -p "$REPORTS"
PRODUCER="$JUDGE_ROOT/Meta/StrataLint/lean-inspector/inspect.sh"
[[ -x "$PRODUCER" ]] \
  || { echo "local-harness-gate: dev Lean producer is absent" >&2; exit 2; }
PAIR_PRODUCER="$CANDIDATE_ROOT/Meta/StrataLint/scripts/lean-report-pair.sh"
[[ -x "$PAIR_PRODUCER" ]] \
  || { echo "local-harness-gate: candidate Lean report pair helper is absent" >&2; exit 2; }

CANDIDATE_REPORT="$CANDIDATE_ROOT/.lake/build/stratalint/raw-lean-report.json"
run_stage lean-reports \
  "$PAIR_PRODUCER" \
  --producer "$PRODUCER" \
  --lake-bin "$LAKE_BIN" \
  --candidate-root "$CANDIDATE_ROOT" \
  --candidate-output "$CANDIDATE_REPORT" \
  --baseline-root "$JUDGE_ROOT" \
  --baseline-output "$REPORTS/baseline-lean-report.json"
run_stage emit-check make -C "$CANDIDATE_ROOT" emit-check BASE="$BASE_SHA"

GATE="$JUDGE_ROOT/.github/scripts/harness-gate.sh"
[[ -x "$GATE" ]] || { echo "local-harness-gate: dev gate is absent" >&2; exit 2; }
admission_started="$(date +%s)"
set +e
STRATALINT_TIMING="$SHARED_TIMING_FILE" "$GATE" \
  --candidate "$CANDIDATE_ROOT" \
  --judge-root "$JUDGE_ROOT" \
  --base "$BASE_SHA" \
  --candidate-lean-report "$CANDIDATE_REPORT" \
  --baseline-lean-report "$REPORTS/baseline-lean-report.json"
gate_rc=$?
set -e
if [[ -s "$SHARED_TIMING_FILE" ]]; then
  cat "$SHARED_TIMING_FILE" >> "$LOCAL_TIMING_FILE"
  : > "$SHARED_TIMING_FILE"
fi
admission_status="passed"
if [[ "$gate_rc" -ne 0 && "$gate_rc" -ne 3 ]]; then admission_status="failed"; fi
record_timing local admission "$admission_status" "$(( $(date +%s) - admission_started ))"

# Bootstrap only while the frozen base predates #297. Once dev owns echo-verify,
# the shared base gate above is the sole local and CI verdict.
if [[ "$gate_rc" -eq 0 || "$gate_rc" -eq 3 ]] \
  && ! grep -qF 'dotnet "$JUDGE_DLL" echo-verify' "$GATE"; then
  run_stage echo-verify-bootstrap \
    make -C "$CANDIDATE_ROOT" echo-verify BASE="$BASE_SHA"
fi

if [[ $gate_rc -eq 3 ]]; then
  printf '%s\n' "local-harness-gate: certified SL-022 conservative extension" >&2
  exit 0
fi
exit "$gate_rc"
