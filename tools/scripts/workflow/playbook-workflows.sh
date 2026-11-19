#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="tools/StrataLint.Cli/StrataLint.Cli.csproj"
REPORT=".lake/build/stratalint/raw-lean-report.json"
FROZEN_LEDGER="Golden/Frozen/state"
COMMAND="${1:-}"
BASE="${2:-origin/dev}"
GID="${3:-}"

run_cli() {
  dotnet run --project "$PROJECT" --configuration Release -- "$@"
}

align_delivery_ledger() {
  local closed_modules module closed_query_output targets=''
  local align_args=(ledger-align)

  if ! command -v jq >/dev/null 2>&1; then
    echo "PLAYBOOK_INVALID jq is required to read Closed module selectors" >&2
    return 2
  fi
  if ! closed_query_output="$(run_cli ledger-align --list-closed --candidate-lean-report "$REPORT")"; then
    echo "PLAYBOOK_INVALID current Closed module query failed" >&2
    return 2
  fi
  if ! closed_modules="$(jq -r '.[]' <<< "$closed_query_output" 2>&1)"; then
    echo "PLAYBOOK_INVALID failed to read Closed modules: $closed_modules" >&2
    return 2
  fi

  while IFS= read -r module; do
    if [[ -n "$module" && ! -f "$FROZEN_LEDGER/$module.json" ]]; then
      align_args+=(--add "$module")
      targets+="${targets:+ }${module%.lean}"
    fi
  done <<< "$closed_modules"
  if [[ -n "$targets" ]]; then
    targets="${targets//\//.}"
    step lean-report-scoped make lean-report-scoped "LEAN_TARGETS=$targets"
    run_cli "${align_args[@]}" --candidate-lean-report .lake/build/stratalint/scoped-lean-report.json
  fi
}


begin_step() {
  local label="$1"
  printf 'PLAYBOOK_STEP command=%s detail=%s\n' "$COMMAND" "$label" >&2
}

complete_step() {
  :
}

step() {
  local label="$1"
  shift
  begin_step "$label"
  "$@" || return $?
  complete_step passed
}

require_module_argument() {
  DOCUMENT_GID="${GID%.*}"
  MODULE_PATH="${DOCUMENT_GID}.lean"
  if [[ "$GID" != D5/*.* || "$GID" == *[[:space:]]* || ! -f "$MODULE_PATH" ]]; then
    echo "PLAYBOOK_INVALID GID does not resolve to a Lean module: $GID" >&2
    return 2
  fi
}

build_scoped_report() {
  [[ -n "$LEAN_TARGETS" ]] || { echo 'PLAYBOOK_INVALID deposit report scope is empty' >&2; return 2; }
  REPORT=".lake/build/stratalint/delivery-lean-report.json"
  export STRATALINT_LEAN_REPORT="$ROOT/$REPORT"
  step lean-report-scoped make lean-report-scoped "LEAN_TARGETS=$LEAN_TARGETS" "LEAN_REPORT=$ROOT/$REPORT"
}

emit_target() {
  local paths status=0
  paths="$(mktemp "${TMPDIR:-/tmp}/deposit-scribe-paths.XXXXXXXX")"
  printf '%s\0' "$MODULE_PATH" > "$paths"
  step emit make emit "PATHS=$paths" || status=$?
  rm -f -- "$paths"
  return "$status"
}

require_new_module_blueprint_mirror() {
  local mirror_path="Blueprint/${MODULE_PATH%.lean}.md"

  if ! git rev-parse --verify "${BASE}^{commit}" >/dev/null 2>&1; then
    echo "PLAYBOOK_INVALID base does not resolve to a commit: $BASE" >&2
    return 2
  fi
  git cat-file -e "${BASE}:${MODULE_PATH}" >/dev/null 2>&1 && return 0

  if [[ ! -f "$mirror_path" ]]; then
    echo "PLAYBOOK_INVALID missing Blueprint mirror: $mirror_path; run make emit" >&2
    return 1
  fi
}


freeze_exists() {
  local output status=0
  output="$(run_cli ledger-frozen --target "$MODULE_PATH" 2>&1)" || status=$?
  [[ -z "$output" ]] || printf '%s\n' "$output" >&2
  # The query's absent-member result is silent. Launcher/build failures must
  # not be interpreted as permission to write a new freeze.
  if [[ "$status" -eq 1 && -n "$output" ]]; then
    return 2
  fi
  return "$status"
}

freeze_module_if_needed() {
  local already_frozen="$1"
  if [[ "$already_frozen" -eq 1 ]]; then
    printf 'PLAYBOOK_SKIP command=deposit detail=module-already-frozen path=%s\n' \
      "$MODULE_PATH" >&2
    return
  fi

  step "ledger-align --add $MODULE_PATH" run_cli \
    ledger-align --add "$MODULE_PATH" --candidate-lean-report "$REPORT"
  if ! freeze_exists; then
    echo "PLAYBOOK_INVALID ledger align did not freeze target module: $MODULE_PATH" >&2
    return 1
  fi
}

deposit_module() {
  local deposit_base_sha freeze_precheck status
  require_new_module_blueprint_mirror
  LEAN_TARGETS="${DOCUMENT_GID//\//.}"
  build_scoped_report
  deposit_base_sha="$(git rev-parse --verify "${BASE}^{commit}")"
  step deposit-header-check run_cli deposit-header-check --target "$MODULE_PATH" --protected-base "$deposit_base_sha"
  emit_target
  if freeze_exists; then
    freeze_precheck=1
    printf 'PLAYBOOK_SKIP command=deposit detail=module-already-frozen path=%s\n' \
      "$MODULE_PATH" >&2
  else
    status=$?
    [[ "$status" -eq 1 ]] || exit "$status"
    freeze_precheck=0
  fi
  freeze_module_if_needed "$freeze_precheck"
}


case "$COMMAND" in
  deliver-check)
    make lean-report
    make emit
    # Freeze last among all mutating derivations so the proposition snapshot is current.
    align_delivery_ledger
    make gate BASE="$BASE"
    ;;
  deposit|deposit-uncovered)
    if [[ "$#" -ne 3 || -n "${ATOM_ID+x}" ]]; then
      echo "usage: playbook-workflows.sh $COMMAND BASE GID" >&2
      exit 2
    fi
    require_module_argument
    deposit_module
    printf 'PLAYBOOK_DEPOSIT_FROZEN gid=%s\n' "$GID" >&2
    ;;
  *)
    echo "usage: playbook-workflows.sh deliver-check [BASE] | deposit BASE GID" >&2
    exit 2
    ;;
esac
