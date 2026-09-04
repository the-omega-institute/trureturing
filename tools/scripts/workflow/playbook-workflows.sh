#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="tools/StrataLint.Cli/StrataLint.Cli.csproj"
REPORT=".lake/build/stratalint/raw-lean-report.json"
FROZEN_LEDGER="Golden/Frozen/accepted"
TRUTH_GRAPH="Generated/truth-graph.v1.json"
COMMAND="${1:-}"
BASE="${2:-origin/dev}"
ATOM_ID="${3:-}"
GID="${4:-}"
BATCH_ATOM_IDS=()
BATCH_GIDS=()

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

require_transaction_arguments() {
  if [[ ! "$ATOM_ID" =~ ^[a-z0-9-]+$ || "$GID" != D5/*.* || "$GID" == *[[:space:]]* ]]; then
    echo "usage: playbook-workflows.sh $COMMAND BASE ATOM_ID GID" >&2
    return 2
  fi

  DOCUMENT_GID="${GID%.*}"
  MODULE_PATH="${DOCUMENT_GID}.lean"
  if [[ "$DOCUMENT_GID" == "$GID" || ! -f "$MODULE_PATH" ]]; then
    echo "PLAYBOOK_INVALID GID does not resolve to a Lean module: $GID" >&2
    return 2
  fi
}

require_cover_batch_arguments() {
  local atoms_file="$ATOM_ID" line atom gid remainder status line_number=0
  if [[ -z "$atoms_file" || -n "$GID" || ! -f "$atoms_file" || ! -r "$atoms_file" ]]; then
    echo "usage: playbook-workflows.sh cover-batch BASE ATOMS_FILE" >&2
    return 2
  fi

  while IFS= read -r line || [[ -n "$line" ]]; do
    line_number=$((line_number + 1))
    if [[ "$line" == *$'\r'* || "$line" != *$'\t'* ]]; then
      echo "PLAYBOOK_INVALID cover-batch line $line_number must be ATOM_ID<TAB>GID" >&2
      return 2
    fi
    atom="${line%%$'\t'*}"
    remainder="${line#*$'\t'}"
    if [[ "$remainder" == *$'\t'* ]]; then
      echo "PLAYBOOK_INVALID cover-batch line $line_number must contain exactly two TSV fields" >&2
      return 2
    fi
    gid="$remainder"
    ATOM_ID="$atom"
    GID="$gid"
    if require_transaction_arguments; then
      :
    else
      status=$?
      return "$status"
    fi
    BATCH_ATOM_IDS+=("$atom")
    BATCH_GIDS+=("$gid")
  done < "$atoms_file"

  if [[ "${#BATCH_ATOM_IDS[@]}" -eq 0 ]]; then
    echo "PLAYBOOK_INVALID cover-batch input is empty: $atoms_file" >&2
    return 2
  fi
}

derive_cover_batch_row_state() {
  local index="$1"
  ATOM_ID="${BATCH_ATOM_IDS[index]}"
  GID="${BATCH_GIDS[index]}"
  require_transaction_arguments
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
  local active_state grep_output grep_status ledger_file
  local module_ledger_files=()
  if ! command -v jq >/dev/null 2>&1; then
    echo "PLAYBOOK_INVALID jq is required to inspect $FROZEN_LEDGER" >&2
    return 2
  fi
  if [[ ! -d "$FROZEN_LEDGER" ]]; then
    echo "PLAYBOOK_INVALID frozen ledger is missing: $FROZEN_LEDGER" >&2
    return 2
  fi

  if grep_output="$(git grep --untracked -l -F -e "$MODULE_PATH" \
      -- "$FROZEN_LEDGER/*.json" 2>&1)"; then
    while IFS= read -r ledger_file; do
      [[ -z "$ledger_file" ]] || module_ledger_files+=("$ledger_file")
    done <<< "$grep_output"
  else
    grep_status=$?
    if [[ "$grep_status" -eq 1 ]]; then
      return 1
    fi
    echo "PLAYBOOK_INVALID failed to locate target module ledger shards: $grep_output" >&2
    return 2
  fi

  if ! active_state="$(jq -sc --arg node "$MODULE_PATH" '
      def exact_keys($expected): (keys | sort) == ($expected | sort);
      if all(.[];
          exact_keys(["event_hash", "event_type", "payload", "schema_version"])
          and .event_type == "Freeze"
          and .schema_version == 5
          and (.payload | exact_keys([
            "declaration_statement_ids",
            "descriptor_selector",
            "prerequisite_frozen_node_ids",
            "statement_id"
          ]))
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
          and all(.payload.prerequisite_frozen_node_ids[]; type == "string"))
      then any(.[]; .payload.descriptor_selector == $node)
      else error("matching shard is not a canonical v5 Freeze")
      end
    ' "${module_ledger_files[@]}" 2>&1)"; then
    echo "PLAYBOOK_INVALID failed to inspect target module v5 Freeze shards: $active_state" >&2
    return 2
  fi

  case "$active_state" in
    true) return 0 ;;
    false) return 1 ;;
    *)
      echo "PLAYBOOK_INVALID frozen ledger query returned an invalid state: $active_state" >&2
      return 2
      ;;
  esac
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
    exit "$status"
  fi
}

cover_batch_row() {
  cover_row
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
    require_new_module_blueprint_mirror
    step lean-report make lean-report
    step deposit-header-check run_cli deposit-header-check --target "$MODULE_PATH"
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
    for index in "${!BATCH_ATOM_IDS[@]}"; do
      derive_cover_batch_row_state "$index"
      cover_batch_row
    done
    step emit make emit
    ;;
  *)
    echo "usage: playbook-workflows.sh deliver-check|deposit|cover|cover-batch [BASE] [ATOM_ID GID|ATOMS_FILE]" >&2
    exit 2
    ;;
esac
