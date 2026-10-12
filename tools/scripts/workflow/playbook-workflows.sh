#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="tools/StrataLint.Cli/StrataLint.Cli.csproj"
REPORT=".lake/build/stratalint/raw-lean-report.json"
FROZEN_LEDGER="Golden/Frozen/state"
COMMAND="${1:-}"
# cover and cover-batch read nothing from git, so they take no base.
case "$COMMAND" in
  cover|cover-batch)
    BASE=""
    ATOM_ID="${2:-}"
    GID="${3:-}"
    ;;
  deposit-uncovered)
    BASE="${2:-origin/dev}"
    ;;
  *)
    BASE="${2:-origin/dev}"
    ATOM_ID="${3:-}"
    GID="${4:-}"
    ;;
esac
COVER_FAILURE_REASON=""

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

# 该 atom id 必须解析得到一个账目条目。账目有三种形态:
# CAS blob、per-atom 的 backfill 分片、以及 Meta/BACKFILL.yaml 单文件。三者皆无即拒。
# 字符形状合法不代表条目存在;存在性检查必须先于不可逆的冻结动作。
atom_id_resolves() {
  [[ -e "Meta/Digestion/atoms/sha256/$1" ]] && return 0
  local hit
  for hit in Meta/Digestion/backfill/*/*/"$1".yaml; do
    [[ -e "$hit" ]] && return 0
  done
  [[ -f Meta/BACKFILL.yaml ]] && grep -q "atom_id: $1\$" Meta/BACKFILL.yaml && return 0
  return 1
}

require_atom_argument() {
  if [[ ! "$ATOM_ID" =~ ^[a-z0-9-]+$ ]]; then
    if [[ "$COMMAND" == cover ]]; then
      echo "usage: playbook-workflows.sh cover ATOM_ID GID" >&2
    else
      echo "usage: playbook-workflows.sh $COMMAND BASE ATOM_ID GID" >&2
    fi
    return 2
  fi

  if ! atom_id_resolves "$ATOM_ID"; then
    echo "PLAYBOOK_INVALID atom not found in the digestion ledger: $ATOM_ID" >&2
    return 2
  fi
}

require_module_argument() {
  DOCUMENT_GID="${GID%.*}"
  MODULE_PATH="${DOCUMENT_GID}.lean"
  if [[ "$GID" != D5/*.* || "$GID" == *[[:space:]]* || ! -f "$MODULE_PATH" ]]; then
    echo "PLAYBOOK_INVALID GID does not resolve to a Lean module: $GID" >&2
    return 2
  fi
}

require_transaction_arguments() {
  require_atom_argument
  require_module_argument
}

require_cover_batch_arguments() {
  local atoms_file="$ATOM_ID"
  if [[ -z "$atoms_file" || -n "$GID" || ! -f "$atoms_file" || ! -r "$atoms_file" ]]; then
    echo "usage: playbook-workflows.sh cover-batch ATOMS_FILE" >&2
    return 2
  fi
  LEAN_TARGETS="$(run_cli cover-batch --lean-inputs --atoms "$atoms_file")"
}

prepare_cover_report() {
  local selected
  selected="$(run_cli cover-atom --lean-inputs --cover-atom "$ATOM_ID" --gid "$GID")" || return $?
  if [[ "$COMMAND" != deposit || "$selected" != "${LEAN_TARGETS:-}" ]]; then
    LEAN_TARGETS="$selected"
    build_scoped_report
  fi
}

build_scoped_report() {
  [[ -n "$LEAN_TARGETS" ]] || { echo 'PLAYBOOK_INVALID cover report scope is empty' >&2; return 2; }
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


cover_atom_or_resume() {
  local output
  if output="$(run_cli cover-atom --cover-atom "$ATOM_ID" --gid "$GID" 2>&1)"; then
    [[ -z "$output" ]] || printf '%s\n' "$output"
    return
  else
    local status=$?
    COVER_FAILURE_REASON="${output##*$'\n'}"
    [[ -n "$COVER_FAILURE_REASON" ]] || COVER_FAILURE_REASON="cover-atom-exit-$status"
    printf '%s\n' "$output" >&2
    if grep -Fq "cover atom $ATOM_ID already has coverage:" <<<"$output"; then
      printf 'PLAYBOOK_SKIP command=cover detail=coverage-already-applied atom_id=%s gid=%s\n' \
        "$ATOM_ID" "$GID" >&2
      return
    fi
    return "$status"
  fi
}

cover_row() {
  local status
  if prepare_cover_report; then
    :
  else
    status=$?
    COVER_FAILURE_REASON="cover-report-exit-$status"
    return "$status"
  fi
  begin_step cover-atom
  if cover_atom_or_resume; then
    complete_step passed
  else
    status=$?
    complete_step failed
    return "$status"
  fi
}

cd "$ROOT"
case "$COMMAND" in
  deliver-check)
    make lean-report
    make emit
    # Freeze last among all mutating derivations so the proposition snapshot is current.
    align_delivery_ledger
    make gate BASE="$BASE"
    ;;
  deposit)
    require_transaction_arguments
    deposit_module
    cover_row || {
      status=$?
      printf 'PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED atom_id=%s gid=%s reason=%s\n' \
        "$ATOM_ID" "$GID" "$COVER_FAILURE_REASON" >&2
      exit "$status"
    }
    ;;
  deposit-uncovered)
    if [[ "$#" -ne 3 || -n "${ATOM_ID+x}" ]]; then
      echo "usage: playbook-workflows.sh deposit-uncovered BASE GID (ATOM_ID is not accepted)" >&2
      exit 2
    fi
    GID="$3"
    require_module_argument
    deposit_module
    printf 'PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED gid=%s reason=NO_ATOM\n' "$GID" >&2
    ;;
  cover)
    require_transaction_arguments
    cover_row
    ;;
  cover-batch)
    require_cover_batch_arguments
    build_scoped_report
    step cover-batch run_cli cover-batch --atoms "$ATOM_ID"
    ;;
  *)
    echo "usage: playbook-workflows.sh deliver-check [BASE] | deposit BASE ATOM_ID GID | deposit-uncovered BASE GID | cover ATOM_ID GID | cover-batch ATOMS_FILE" >&2
    exit 2
    ;;
esac
