#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="tools/StrataLint.Cli/StrataLint.Cli.csproj"
REPORT=".lake/build/stratalint/raw-lean-report.json"
FROZEN_LEDGER="Golden/Frozen/accepted"
TRUTH_GRAPH="Generated/truth-graph.v1.json"
COMMAND="${1:-}"
BASE="${2:-origin/dev}"
if [[ "$COMMAND" != deposit-uncovered ]]; then
  ATOM_ID="${3:-}"
  GID="${4:-}"
fi
COVER_FAILURE_REASON=""

run_cli() {
  dotnet run --project "$PROJECT" --configuration Release -- "$@"
}

run_digest_status() {
  run_cli digest-status --base "$BASE"
}

align_delivery_ledger() {
  local accepted_modules='[]' closed_modules module
  local accepted_files=("$FROZEN_LEDGER"/*.json)
  local align_args=(ledger-align)

  if ! command -v jq >/dev/null 2>&1; then
    echo "PLAYBOOK_INVALID jq is required to derive ledger additions" >&2
    return 2
  fi
  if [[ ! -f "$TRUTH_GRAPH" ]]; then
    echo "PLAYBOOK_INVALID truth graph is missing after emit: $TRUTH_GRAPH" >&2
    return 2
  fi
  if [[ ! -e "${accepted_files[0]}" ]]; then
    accepted_files=()
  fi
  if [[ "${#accepted_files[@]}" -gt 0 ]] \
      && ! accepted_modules="$(jq -sc '
        [ .[]
          | select(.event_type == "Freeze" and .schema_version == 5)
          | .payload.descriptor_selector
          | select(type == "string") ]
        | unique
      ' "${accepted_files[@]}" 2>&1)"; then
    echo "PLAYBOOK_INVALID failed to read accepted module selectors: $accepted_modules" >&2
    return 2
  fi
  if ! closed_modules="$(jq -r --argjson accepted "$accepted_modules" '
      .truth.nodes[]
      | select(.state == "closed")
      | .repo_path as $path
      | select(($accepted | index($path)) == null)
      | $path
    ' "$TRUTH_GRAPH" 2>&1)"; then
    echo "PLAYBOOK_INVALID failed to derive Closed modules from $TRUTH_GRAPH: $closed_modules" >&2
    return 2
  fi

  while IFS= read -r module; do
    [[ -z "$module" ]] || align_args+=(--add "$module")
  done <<< "$closed_modules"
  align_args+=(--candidate-lean-report "$REPORT")
  run_cli "${align_args[@]}"
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
  "$@"
  complete_step passed
}

# 该 atom id 是否真的解析得到一个账目条目。三处都认,因为账目有三种既有形态:
# CAS blob、per-atom 的 backfill 分片、以及 Meta/BACKFILL.yaml 单文件。三者皆无即拒。
#
# 立条依据 #6676(2026-09-10 实测):require_transaction_arguments 原本**只查字符形状**
# (`^[a-z0-9-]+$`),不查该 atom 是否存在;而 deposit 分支的次序是
#   require_transaction_arguments → … → freeze_module_if_needed → cover_row
# 于是一个凭空杜撰的 id(实例:`ATOM_ID=none`,该串完全满足那个正则)会**先把模块冻掉**,
# 再在 cover 处失败,留下一个已冻结而无覆盖的模块。冻结不可逆(第 1.3 条),
# 而不可逆动作排在了唯一能证伪其前提的那一步之前 —— 次序反了(第 7.8 条)。
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
    echo "usage: playbook-workflows.sh $COMMAND BASE ATOM_ID GID" >&2
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
    echo "usage: playbook-workflows.sh cover-batch BASE ATOMS_FILE" >&2
    return 2
  fi

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
  run_cli ledger-frozen --target "$MODULE_PATH"
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
  step lean-report make lean-report
  deposit_base_sha="$(git rev-parse --verify "${BASE}^{commit}")"
  step deposit-header-check run_cli deposit-header-check --target "$MODULE_PATH" --protected-base "$deposit_base_sha"
  step emit make emit
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

verify_added_frozen_event_v5() {
  local path="$1" event_type
  if ! event_type="$(jq -er '.event_type | select(type == "string")' "$path")"; then
    echo "PLAYBOOK_INVALID added frozen event has no valid event_type: $path; re-freeze before delivery" >&2
    return 1
  fi

  if [[ "$event_type" == "Freeze" ]] \
      && jq -e '
        def exact_keys($expected): (keys | sort) == ($expected | sort);
        exact_keys(["event_hash", "event_type", "payload", "schema_version"])
        and .schema_version == 5
        and (.payload | exact_keys([
          "declaration_statement_ids",
          "descriptor_selector",
          "prerequisite_frozen_node_ids",
          "statement_id"
        ]))
        and (.event_hash | type) == "string"
        and (.payload.descriptor_selector | type) == "string"
        and (.payload.statement_id | type) == "string"
        and (.payload.declaration_statement_ids | type) == "array"
        and all(.payload.declaration_statement_ids[];
          type == "object"
          and exact_keys(["declaration_name_key", "kind", "statement_id"])
          and (.declaration_name_key | type) == "string"
          and (.kind | type) == "string"
          and (.statement_id | type) == "string")
        and (.payload.prerequisite_frozen_node_ids | type) == "array"
        and all(.payload.prerequisite_frozen_node_ids[]; type == "string")
      ' "$path" >/dev/null; then
    return 0
  fi
  echo "PLAYBOOK_INVALID added frozen event is not a v5 Freeze: $path" >&2
  return 1

}

verify_added_frozen_events_v5() {
  local added_paths path
  added_paths="$(mktemp)"
  if ! git diff --diff-filter=A --name-only -z "$BASE"...HEAD -- "$FROZEN_LEDGER/*.json" \
      > "$added_paths"; then
    rm -f -- "$added_paths"
    echo "PLAYBOOK_INVALID cannot determine added frozen events from base $BASE" >&2
    return 1
  fi
  if ! git ls-files --others --exclude-standard -z -- "$FROZEN_LEDGER/*.json" \
      >> "$added_paths"; then
    rm -f -- "$added_paths"
    echo "PLAYBOOK_INVALID cannot determine untracked frozen events" >&2
    return 1
  fi
  if [[ ! -s "$added_paths" ]]; then
    rm -f -- "$added_paths"
    return 0
  fi
  if ! command -v jq >/dev/null 2>&1; then
    rm -f -- "$added_paths"
    echo "PLAYBOOK_INVALID jq is required to verify added frozen events" >&2
    return 2
  fi

  while IFS= read -r -d '' path; do
    if verify_added_frozen_event_v5 "$path"; then
      :
    else
      local status=$?
      rm -f -- "$added_paths"
      return "$status"
    fi
  done < "$added_paths"
  rm -f -- "$added_paths"
}


cover_atom_or_resume() {
  local output
  if output="$(run_cli cover-atom --cover-atom "$ATOM_ID" --gid "$GID" \
      --base "$BASE" 2>&1)"; then
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
  begin_step cover-atom
  if cover_atom_or_resume; then
    complete_step passed
  else
    local status=$?
    complete_step failed
    return "$status"
  fi
}

cd "$ROOT"
case "$COMMAND" in
  deliver-check)
    make lean-report
    make emit
    make align-digestion-status BASE="$BASE"
    run_digest_status
    # Freeze last among all mutating derivations so the proposition snapshot is current.
    verify_added_frozen_events_v5
    align_delivery_ledger
    run_digest_status
    make preflight BASE="$(git rev-parse HEAD^1)"
    verify_added_frozen_events_v5
    ;;
  deposit)
    require_transaction_arguments
    deposit_module
    if cover_row; then
      step emit make emit
    else
      status=$?
      printf 'PLAYBOOK_DEPOSIT_FROZEN_UNCOVERED atom_id=%s gid=%s reason=%s\n' \
        "$ATOM_ID" "$GID" "$COVER_FAILURE_REASON" >&2
      exit "$status"
    fi
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
    step lean-report make lean-report
    cover_row
    step emit make emit
    ;;
  cover-batch)
    require_cover_batch_arguments
    step lean-report make lean-report
    step cover-batch run_cli cover-batch --atoms "$ATOM_ID" --base "$BASE"
    ;;
  *)
    echo "usage: playbook-workflows.sh deliver-check|deposit|deposit-uncovered|cover|cover-batch [BASE] [ATOM_ID GID|GID|ATOMS_FILE]" >&2
    exit 2
    ;;
esac
