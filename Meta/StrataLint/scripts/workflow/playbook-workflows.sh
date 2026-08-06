#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
PROJECT="Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"
REPORT=".lake/build/stratalint/raw-lean-report.json"
FROZEN_LEDGER="Meta/StrataLint/Golden/Frozen/events.jsonl"
ECHO_PROJECTION="Generated/echo-residual-summary.md"
COMMAND="${1:-}"
BASE="${2:-origin/dev}"
ATOM_ID="${3:-}"
GID="${4:-}"

run_cli() {
  dotnet run --project "$PROJECT" --configuration Release -- "$@"
}

run_digest_status() {
  run_cli digest-status --base "$BASE"
}

receipts_stage() {
  make ingest BASE="$BASE"
  run_digest_status
}

step() {
  local label="$1"
  shift
  printf 'PLAYBOOK_STEP command=%s detail=%s\n' "$COMMAND" "$label" >&2
  "$@"
}

require_transaction_arguments() {
  if [[ ! "$ATOM_ID" =~ ^[a-z0-9-]+$ || "$GID" != D5/*.* || "$GID" == *[[:space:]]* ]]; then
    echo "usage: playbook-workflows.sh $COMMAND BASE ATOM_ID GID" >&2
    return 2
  fi

  DOCUMENT_GID="${GID%.*}"
  MODULE_PATH="${DOCUMENT_GID}.lean"
  RECEIPT_PATH="Meta/Digestion/formalizations/${ATOM_ID}.v1.json"
  if [[ "$DOCUMENT_GID" == "$GID" || ! -f "$MODULE_PATH" ]]; then
    echo "PLAYBOOK_INVALID GID does not resolve to a Lean module: $GID" >&2
    return 2
  fi
}

refresh_echo_projection() {
  local temporary
  mkdir -p "$(dirname "$ECHO_PROJECTION")"
  temporary="$(mktemp "${ECHO_PROJECTION}.tmp.XXXXXX")"
  printf 'PLAYBOOK_STEP command=%s detail=echo-residual-summary-atomic\n' "$COMMAND" >&2
  if make echo-residual-summary BASE="$BASE" >"$temporary"; then
    mv "$temporary" "$ECHO_PROJECTION"
    printf 'PLAYBOOK_WRITE path=%s mode=temporary-move\n' "$ECHO_PROJECTION" >&2
  else
    local status=$?
    rm -f "$temporary"
    printf 'PLAYBOOK_FAILED step=echo-residual-summary target-preserved=%s exit=%d\n' \
      "$ECHO_PROJECTION" "$status" >&2
    return "$status"
  fi
}

cleanup_transaction_temporaries() {
  local temporary
  for temporary in "${ECHO_PROJECTION}.tmp."* "${RECEIPT_PATH}.tmp."*; do
    [[ -e "$temporary" ]] || continue
    printf 'PLAYBOOK_CLEANUP command=%s path=%s reason=interrupted-transaction\n' \
      "$COMMAND" "$temporary" >&2
    rm -f -- "$temporary"
  done
}

commit_phase_a_if_needed() {
  printf 'PLAYBOOK_STEP command=deposit detail=stage-phase-a\n' >&2
  git add -A
  git reset --quiet HEAD -- "$FROZEN_LEDGER" "$RECEIPT_PATH"
  if git diff --cached --quiet; then
    printf 'PLAYBOOK_SKIP command=deposit detail=phase-a-tree-unchanged\n' >&2
    return
  fi

  git commit -m "formalize: deposit $GID"
}

commit_all_if_needed() {
  local message="$1"
  printf 'PLAYBOOK_STEP command=%s detail=stage-final-tree\n' "$COMMAND" >&2
  git add -A
  if git diff --cached --quiet; then
    printf 'PLAYBOOK_SKIP command=%s detail=final-tree-unchanged\n' "$COMMAND" >&2
    return
  fi

  git commit -m "$message"
}

freeze_exists() {
  if ! command -v jq >/dev/null 2>&1; then
    echo "PLAYBOOK_INVALID jq is required to inspect $FROZEN_LEDGER" >&2
    return 2
  fi
  if [[ ! -f "$FROZEN_LEDGER" ]]; then
    echo "PLAYBOOK_INVALID frozen ledger is missing: $FROZEN_LEDGER" >&2
    return 2
  fi
  if ! jq empty "$FROZEN_LEDGER" >/dev/null; then
    echo "PLAYBOOK_INVALID frozen ledger is not valid JSONL: $FROZEN_LEDGER" >&2
    return 2
  fi

  if jq -e --arg node "$MODULE_PATH" \
      'select(.event_type == "Freeze" and .payload.node_path == $node)' \
      "$FROZEN_LEDGER" >/dev/null; then
    return 0
  else
    local status=$?
    [[ "$status" -eq 4 ]] && return 1
    echo "PLAYBOOK_INVALID failed to inspect frozen ledger: $FROZEN_LEDGER" >&2
    return 2
  fi
}

freeze_module_if_needed() {
  if freeze_exists; then
    printf 'PLAYBOOK_SKIP command=deposit detail=module-already-frozen path=%s\n' \
      "$MODULE_PATH" >&2
    return
  else
    local status=$?
    [[ "$status" -eq 1 ]] || return "$status"
  fi

  step "ledger-append $MODULE_PATH" run_cli \
    ledger-append --candidate-lean-report "$REPORT"
  if ! freeze_exists; then
    echo "PLAYBOOK_INVALID ledger append did not freeze target module: $MODULE_PATH" >&2
    return 1
  fi
}

ensure_formalization_receipt() {
  local temporary
  mkdir -p "$(dirname "$RECEIPT_PATH")"
  temporary="$(mktemp "${RECEIPT_PATH}.tmp.XXXXXX")"
  printf 'PLAYBOOK_STEP command=deposit detail=emit-formalization-receipt\n' >&2
  if run_cli emit-formalization-receipt \
      --atom-id "$ATOM_ID" --gid "$GID" --out "$temporary"; then
    :
  else
    local status=$?
    rm -f "$temporary"
    return "$status"
  fi

  if [[ -f "$RECEIPT_PATH" ]]; then
    if cmp -s "$temporary" "$RECEIPT_PATH"; then
      rm -f "$temporary"
      printf 'PLAYBOOK_SKIP command=deposit detail=receipt-already-aligned path=%s\n' \
        "$RECEIPT_PATH" >&2
      return
    fi

    rm -f "$temporary"
    echo "PLAYBOOK_INVALID existing formalization receipt conflicts with current atom/GID: $RECEIPT_PATH" >&2
    return 1
  fi

  mv "$temporary" "$RECEIPT_PATH"
  printf 'PLAYBOOK_WRITE path=%s mode=atom-derived\n' "$RECEIPT_PATH" >&2
}

cover_atom_or_resume() {
  local output
  if output="$(run_cli cover-atom --cover-atom "$ATOM_ID" --gid "$GID" \
      --base "$BASE" --envelope "$RECEIPT_PATH" 2>&1)"; then
    [[ -z "$output" ]] || printf '%s\n' "$output"
    return
  else
    local status=$?
    printf '%s\n' "$output" >&2
    if grep -Fq "cover atom $ATOM_ID already has coverage: $GID" <<<"$output"; then
      printf 'PLAYBOOK_SKIP command=cover detail=coverage-already-applied atom_id=%s gid=%s\n' \
        "$ATOM_ID" "$GID" >&2
      return
    fi
    return "$status"
  fi
}

cd "$ROOT"
case "$COMMAND" in
  deliver-check)
    make lean-report
    make emit
    receipts_stage
    # Freeze last among all mutating derivations so the receipt binds committed source bytes.
    run_cli ledger-append --candidate-lean-report "$REPORT"
    make emit-check BASE="$BASE"
    run_digest_status
    make preflight BASE="$BASE"
    ;;
  receipts-stage)
    receipts_stage
    ;;
  derived-refresh)
    git merge --no-edit "$BASE"
    make lean-report
    make emit
    receipts_stage
    make emit-check BASE="$BASE"
    ;;
  deposit)
    require_transaction_arguments
    cleanup_transaction_temporaries
    if freeze_exists; then
      printf 'PLAYBOOK_SKIP command=deposit detail=phase-a-already-committed path=%s\n' \
        "$MODULE_PATH" >&2
    else
      status=$?
      [[ "$status" -eq 1 ]] || exit "$status"
      if [[ -f "$RECEIPT_PATH" ]]; then
        echo "PLAYBOOK_INVALID formalization receipt exists before target Freeze: $RECEIPT_PATH" >&2
        exit 1
      fi
      step lean-report make lean-report
      step emit make emit
      refresh_echo_projection
      step emit-check make emit-check BASE="$BASE"
      commit_phase_a_if_needed
    fi
    freeze_module_if_needed
    ensure_formalization_receipt
    step lean-report-refresh make lean-report
    refresh_echo_projection
    step emit-check-final make emit-check BASE="$BASE"
    commit_all_if_needed "formalize: record deposit receipt for $GID"
    ;;
  cover)
    require_transaction_arguments
    cleanup_transaction_temporaries
    step lean-report make lean-report
    step cover-atom cover_atom_or_resume
    step emit-post-cover make emit
    step align-scribe-receipt run_cli \
      align-scribe-receipt --atom-id "$ATOM_ID" --gid "$GID"
    step emit-post-alignment make emit
    refresh_echo_projection
    step emit-check make emit-check BASE="$BASE"
    commit_all_if_needed "formalize: cover $ATOM_ID with $GID"
    ;;
  *)
    echo "usage: playbook-workflows.sh deliver-check|receipts-stage|derived-refresh|deposit|cover [BASE] [ATOM_ID GID]" >&2
    exit 2
    ;;
esac
