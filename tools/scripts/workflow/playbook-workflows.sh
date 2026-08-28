#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="tools/StrataLint.Cli/StrataLint.Cli.csproj"
REPORT=".lake/build/stratalint/raw-lean-report.json"
FROZEN_LEDGER="Golden/Frozen/accepted"
COMMAND="${1:-}"
BASE="${2:-origin/dev}"
ATOM_ID="${3:-}"
GID="${4:-}"
BATCH_ATOM_IDS=()
BATCH_GIDS=()
PREPARED_RECEIPT_PATH=""
PREPARED_RECEIPT_ORIGINAL_PATH=""
PREPARED_RECEIPT_REPLACES_EXISTING=0

cleanup_prepared_receipt() {
  [[ -z "$PREPARED_RECEIPT_PATH" ]] || rm -f -- "$PREPARED_RECEIPT_PATH"
  [[ -z "$PREPARED_RECEIPT_ORIGINAL_PATH" ]] \
    || rm -f -- "$PREPARED_RECEIPT_ORIGINAL_PATH"
}

finish_playbook() {
  local rc=$?
  trap - EXIT
  set +e
  cleanup_prepared_receipt
  exit "$rc"
}
trap finish_playbook EXIT

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
  RECEIPT_PATH="Meta/Digestion/formalizations/${ATOM_ID}.v1.json"
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

cleanup_cover_batch_temporaries() {
  local index
  for index in "${!BATCH_ATOM_IDS[@]}"; do
    derive_cover_batch_row_state "$index"
    cleanup_transaction_temporaries
  done
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

cleanup_transaction_temporaries() {
  local temporary
  for temporary in "${RECEIPT_PATH}.tmp."*; do
    [[ -e "$temporary" ]] || continue
    printf 'PLAYBOOK_CLEANUP command=%s path=%s reason=interrupted-transaction\n' \
      "$COMMAND" "$temporary" >&2
    rm -f -- "$temporary"
  done
}

commit_phase_a_if_needed() {
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
  git add -A
  if git diff --cached --quiet; then
    printf 'PLAYBOOK_SKIP command=%s detail=final-tree-unchanged\n' "$COMMAND" >&2
    return
  fi

  git commit -m "$message"
}

freeze_exists() {
  local active_state freeze_case_ids grep_output grep_status
  local ledger_file target_case_id
  local git_grep_arguments=() module_ledger_files=() related_ledger_files=()
  local target_case_ids=()
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

  if ! freeze_case_ids="$(jq -rsc --arg node "$MODULE_PATH" '
      map(select(.event_type == "Freeze" and .payload.input.descriptor_selector == $node))
      | map(
          (.payload.case_id // null) as $case
          | if (($case | type) == "string") then
              $case
            else
              error("Freeze is missing its case identity")
            end)
      | unique[]
    ' "${module_ledger_files[@]}" 2>&1)"; then
    echo "PLAYBOOK_INVALID failed to inspect target module ledger shards: $freeze_case_ids" >&2
    return 2
  fi
  [[ -n "$freeze_case_ids" ]] || return 1

  while IFS= read -r target_case_id; do
    [[ -z "$target_case_id" ]] || target_case_ids+=("$target_case_id")
  done <<< "$freeze_case_ids"
  git_grep_arguments=(grep --untracked -l -F)
  for target_case_id in "${target_case_ids[@]}"; do
    git_grep_arguments+=(-e "$target_case_id")
  done
  git_grep_arguments+=(-- "$FROZEN_LEDGER/*.json")
  if grep_output="$(git "${git_grep_arguments[@]}" 2>&1)"; then
    while IFS= read -r ledger_file; do
      [[ -z "$ledger_file" ]] || related_ledger_files+=("$ledger_file")
    done <<< "$grep_output"
  else
    grep_status=$?
    if [[ "$grep_status" -eq 1 ]]; then
      echo "PLAYBOOK_INVALID target Freeze case has no ledger shards" >&2
    else
      echo "PLAYBOOK_INVALID failed to locate target case ledger shards: $grep_output" >&2
    fi
    return 2
  fi

  if ! active_state="$(jq -sc \
      --arg node "$MODULE_PATH" \
      --arg target_cases "$freeze_case_ids" '
      ($target_cases | split("\n")) as $target_case_ids
      | [.[]
        | select(
            if .event_type == "Freeze" then
              (.payload.case_id // null) as $case
              | (($case | type) == "string"
                  and (($target_case_ids | index($case)) != null))
            elif .event_type == "Reattest" then
              (.payload.case_id // null) as $case
              | (($case | type) == "string"
                  and (($target_case_ids | index($case)) != null))
            elif .event_type == "Revoke" then
              (.payload.affected_case_ids // null) as $cases
              | if (($cases | type) != "array") then
                  error("Revoke is missing affected active identities")
                else
                  any($cases[];
                    . as $case | (($target_case_ids | index($case)) != null))
                end
            else
              false
            end)] as $events
      | def replay_reattests($pending):
          if ($pending | length) == 0 then
            .
          else
            . as $active
            | [$pending[]
              | select(
                  (.payload.case_id // null) as $case
                  | (.payload.previous_attestation_event_hash // null) as $previous
                  | (($case | type) == "string"
                      and ($previous | type) == "string"
                      and ($active | has($case))
                      and $active[$case].attestation_event_hash == $previous))] as $ready
            | if ($ready | length) == 0 then
                error("Reattest chain has no active predecessor")
              else
                reduce $ready[] as $event (.;
                  ($event.payload.case_id // null) as $case
                  | ($event.payload.frozen_node_id // null) as $frozen_id
                  | ($event.payload.previous_attestation_event_hash // null) as $previous
                  | ($event.payload.input.descriptor_selector // null) as $path
                  | ($event.payload.input.descriptor_blob_oid // null) as $blob
                  | ($event.event_hash // null) as $event_hash
                  | if (($case | type) != "string"
                      or (($frozen_id | type) != "null"
                        and ($frozen_id | type) != "string")
                      or ($previous | type) != "string"
                      or ($path | type) != "string"
                      or ($blob | type) != "string"
                      or ($event_hash | type) != "string") then
                      error("Reattest is missing replay identity fields")
                    elif (has($case) | not) then
                      error("Reattest targets an inactive case")
                    elif .[$case].attestation_event_hash != $previous then
                      error("Reattest branches from a stale attestation")
                    elif .[$case].node_path != $path then
                      error("Reattest changes the active module path")
                    else
                      .[$case].frozen_node_id as $current_id
                      | .[$case] = {
                          frozen_node_id: ($frozen_id // $current_id),
                          node_path: $path,
                          descriptor_blob_oid: $blob,
                          attestation_event_hash: $event_hash
                        }
                    end)
                | replay_reattests($pending - $ready)
              end
          end;
      ($events | map(select(.event_type == "Freeze"))) as $freezes
      | ($events | map(select(.event_type == "Reattest"))) as $reattests
      | ($events | map(select(.event_type == "Revoke"))) as $revokes
      | reduce $freezes[] as $event ({};
          ($event.payload.case_id // null) as $case
          | ($event.payload.frozen_node_id // null) as $frozen_id
          | ($event.payload.input.descriptor_selector // null) as $path
          | ($event.payload.input.descriptor_blob_oid // null) as $blob
          | ($event.event_hash // null) as $event_hash
          | if (($case | type) != "string"
              or ($frozen_id | type) != "string"
              or ($path | type) != "string"
              or ($blob | type) != "string"
              or (($event_hash | type) != "null"
                and ($event_hash | type) != "string")) then
              error("Freeze is missing replay identity fields")
            elif has($case) then
              error("Freeze reuses an active case")
            else
              .[$case] = {
                frozen_node_id: $frozen_id,
                node_path: $path,
                descriptor_blob_oid: $blob,
                attestation_event_hash: $event_hash
              }
            end)
      | replay_reattests($reattests)
      | reduce $revokes[] as $event (.;
          ($event.payload.affected_case_ids // null) as $cases
          | ($event.payload.affected_frozen_node_ids // null) as $frozen_ids
          | if (($cases | type) != "array" or ($frozen_ids | type) != "array") then
              error("Revoke is missing affected active identities")
            else
              reduce ($cases[]
                | . as $case
                | select(($target_case_ids | index($case)) != null)) as $case (.;
                if (has($case) | not) then
                  error("Revoke targets an inactive frozen case")
                elif (.[$case].frozen_node_id as $id
                    | ($frozen_ids | index($id)) == null) then
                  error("Revoke targets a stale frozen node identity")
                else
                  del(.[$case])
                end)
            end)
      | any(.[]; .node_path == $node)
    ' "${related_ledger_files[@]}" 2>&1)"; then
    echo "PLAYBOOK_INVALID failed to replay target module frozen ledger shards: $active_state" >&2
    return 2
  fi

  case "$active_state" in
    true) return 0 ;;
    false) return 1 ;;
    *)
      echo "PLAYBOOK_INVALID frozen ledger replay returned an invalid state: $active_state" >&2
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

  step "ledger-append $MODULE_PATH" run_cli \
    ledger-append --candidate-lean-report "$REPORT"
  if ! freeze_exists; then
    echo "PLAYBOOK_INVALID ledger append did not freeze target module: $MODULE_PATH" >&2
    return 1
  fi
}

verify_added_frozen_event_ancestor() {
  local path="$1" head="$2" event_type input_selector base_commit_oid commit_oid
  if ! event_type="$(jq -er '.event_type | select(type == "string")' "$path")"; then
    echo "PLAYBOOK_INVALID added frozen event has no valid event_type: $path; re-freeze before delivery" >&2
    return 1
  fi

  case "$event_type" in
    Freeze) input_selector='.payload.input.base_commit_oid' ;;
    Genesis|Revoke) return 0 ;;
    *)
      echo "PLAYBOOK_INVALID added frozen event has unsupported event_type $event_type: $path" >&2
      return 1
      ;;
  esac

  if ! base_commit_oid="$(jq -er "$input_selector | select(type == \"string\")" "$path")"; then
    echo "PLAYBOOK_INVALID added frozen event has no snapshot base_commit_oid: $path; re-freeze before delivery" >&2
    return 1
  fi
  case "$base_commit_oid" in
    git-sha1:*) commit_oid="${base_commit_oid#git-sha1:}" ;;
    git-sha256:*) commit_oid="${base_commit_oid#git-sha256:}" ;;
    *)
      echo "PLAYBOOK_INVALID added frozen event has malformed base_commit_oid $base_commit_oid: $path" >&2
      return 1
      ;;
  esac

  if ! git cat-file -e "${commit_oid}^{commit}" >/dev/null 2>&1; then
    echo "PLAYBOOK_INVALID added frozen event $path recorded snapshot base $base_commit_oid was not pushed or is inconsistent: it does not resolve to a commit in this repository; re-freeze from a pushed base on the producing side before delivery" >&2
    return 1
  fi
  if ! git merge-base --is-ancestor "$commit_oid" "$head"; then
    echo "PLAYBOOK_INVALID added frozen event $path recorded snapshot base $base_commit_oid was not pushed or is inconsistent: it is not an ancestor of current HEAD $head; re-freeze from a pushed base on the producing side before delivery" >&2
    return 1
  fi
}

verify_added_frozen_event_ancestors() {
  local added_paths head path
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
    echo "PLAYBOOK_INVALID jq is required to verify added frozen event ancestry" >&2
    return 2
  fi
  if ! head="$(git rev-parse --verify HEAD^{commit})"; then
    rm -f -- "$added_paths"
    echo "PLAYBOOK_INVALID current HEAD does not resolve to a commit" >&2
    return 2
  fi

  while IFS= read -r -d '' path; do
    if verify_added_frozen_event_ancestor "$path" "$head"; then
      :
    else
      local status=$?
      rm -f -- "$added_paths"
      return "$status"
    fi
  done < "$added_paths"
  rm -f -- "$added_paths"
}

prepare_formalization_receipt() {
  local receipt_gid="$GID" temporary original="" receipt_existed=0
  if [[ -f "$RECEIPT_PATH" ]]; then
    receipt_existed=1
    if ! receipt_gid="$(jq -er \
        '.primary_gid | select(type == "string" and length > 0)' "$RECEIPT_PATH")"; then
      echo "PLAYBOOK_INVALID formalization receipt has no primary_gid: $RECEIPT_PATH" >&2
      return 2
    fi

    original="$(mktemp "${RECEIPT_PATH}.tmp.original.XXXXXX")"
    if ! cp -- "$RECEIPT_PATH" "$original"; then
      rm -f -- "$original"
      echo "PLAYBOOK_INVALID failed to snapshot formalization receipt: $RECEIPT_PATH" >&2
      return 1
    fi
  fi

  mkdir -p "$(dirname "$RECEIPT_PATH")"
  temporary="$(mktemp "${RECEIPT_PATH}.tmp.XXXXXX")"
  local receipt_arguments=(
    emit-formalization-receipt
    --atom-id "$ATOM_ID"
    --gid "$GID"
    --out "$temporary"
  )

  if run_cli "${receipt_arguments[@]}"; then
    :
  else
    local status=$?
    rm -f -- "$temporary" "$original"
    return "$status"
  fi

  if [[ "$receipt_existed" -eq 1 ]]; then
    if [[ ! -f "$RECEIPT_PATH" ]]; then
      rm -f -- "$temporary" "$original"
      echo "PLAYBOOK_INVALID formalization receipt disappeared during extension validation: $RECEIPT_PATH" >&2
      return 1
    fi
    if ! cmp -s "$original" "$RECEIPT_PATH"; then
      rm -f -- "$temporary" "$original"
      echo "PLAYBOOK_INVALID formalization receipt changed during extension validation: $RECEIPT_PATH" >&2
      return 1
    fi

    if cmp -s "$temporary" "$RECEIPT_PATH"; then
      rm -f -- "$temporary" "$original"
      printf 'PLAYBOOK_HOST path=%s atom_id=%s gid=%s mode=existing-atom-receipt\n' \
        "$RECEIPT_PATH" "$ATOM_ID" "$receipt_gid" >&2
      return
    fi

    if [[ "$GID" != "$receipt_gid" ]]; then
      PREPARED_RECEIPT_PATH="$temporary"
      PREPARED_RECEIPT_ORIGINAL_PATH="$original"
      PREPARED_RECEIPT_REPLACES_EXISTING=1
      printf 'PLAYBOOK_PREPARED path=%s mode=hosted-extension gid=%s\n' \
        "$RECEIPT_PATH" "$GID" >&2
      return
    fi

    rm -f -- "$temporary" "$original"
    echo "PLAYBOOK_INVALID existing formalization receipt conflicts with current atom/GID: $RECEIPT_PATH" >&2
    return 1
  fi

  PREPARED_RECEIPT_PATH="$temporary"
  printf 'PLAYBOOK_PREPARED path=%s mode=canonical-temporary\n' "$RECEIPT_PATH" >&2
}

install_prepared_formalization_receipt() {
  [[ -n "$PREPARED_RECEIPT_PATH" ]] || return 0
  if [[ "$PREPARED_RECEIPT_REPLACES_EXISTING" -eq 1 ]]; then
    if [[ ! -f "$RECEIPT_PATH" ]]; then
      echo "PLAYBOOK_INVALID formalization receipt disappeared after extension validation: $RECEIPT_PATH" >&2
      return 1
    fi
    if [[ -z "$PREPARED_RECEIPT_ORIGINAL_PATH" \
        || ! -f "$PREPARED_RECEIPT_ORIGINAL_PATH" ]]; then
      echo "PLAYBOOK_INVALID formalization receipt validation snapshot is missing: $RECEIPT_PATH" >&2
      return 1
    fi
    if ! cmp -s "$PREPARED_RECEIPT_ORIGINAL_PATH" "$RECEIPT_PATH"; then
      echo "PLAYBOOK_INVALID formalization receipt changed after extension validation: $RECEIPT_PATH" >&2
      return 1
    fi

    mv "$PREPARED_RECEIPT_PATH" "$RECEIPT_PATH"
    rm -f -- "$PREPARED_RECEIPT_ORIGINAL_PATH"
    PREPARED_RECEIPT_PATH=""
    PREPARED_RECEIPT_ORIGINAL_PATH=""
    PREPARED_RECEIPT_REPLACES_EXISTING=0
    printf 'PLAYBOOK_WRITE path=%s mode=hosted-extension\n' "$RECEIPT_PATH" >&2
    return
  fi

  if [[ -e "$RECEIPT_PATH" ]]; then
    echo "PLAYBOOK_INVALID formalization receipt appeared after canonical validation: $RECEIPT_PATH" >&2
    return 1
  fi

  mv "$PREPARED_RECEIPT_PATH" "$RECEIPT_PATH"
  PREPARED_RECEIPT_PATH=""
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
    step stage-final-tree commit_all_if_needed \
      "formalize: record failed cover disposition for $ATOM_ID"
    exit "$status"
  fi
  step align-scribe-receipt run_cli \
    align-scribe-receipt --atom-id "$ATOM_ID" --gid "$GID" --base "$BASE"
}

cover_batch_row() {
  local output status
  begin_step cover-atom-aligned
  if output="$(run_cli cover-atom --cover-atom "$ATOM_ID" --gid "$GID" \
      --base "$BASE" --envelope "$RECEIPT_PATH" --align-scribe-receipt 2>&1)"; then
    [[ -z "$output" ]] || printf '%s\n' "$output"
    if grep -Fq "COVER_ATOM_ALIGNED cover=resumed align=passed" <<<"$output"; then
      printf 'PLAYBOOK_SKIP command=cover detail=coverage-already-applied atom_id=%s gid=%s\n' \
        "$ATOM_ID" "$GID" >&2
    fi
    complete_step passed
    return
  else
    status=$?
  fi

  printf '%s\n' "$output" >&2
  complete_step failed
  if grep -Fq "COVER_ATOM_ALIGNED cover=failed" <<<"$output"; then
    step stage-final-tree commit_all_if_needed \
      "formalize: record failed cover disposition for $ATOM_ID"
  fi
  exit "$status"
}

cd "$ROOT"
case "$COMMAND" in
  deliver-check)
    make lean-report
    make emit
    receipts_stage
    # Freeze last among all mutating derivations so the receipt binds committed source bytes.
    verify_added_frozen_event_ancestors
    run_cli ledger-append --candidate-lean-report "$REPORT"
    run_digest_status
    make preflight BASE="$BASE"
    verify_added_frozen_event_ancestors
    ;;
  receipts-stage)
    receipts_stage
    ;;
  deposit)
    require_transaction_arguments
    require_new_module_blueprint_mirror
    cleanup_transaction_temporaries
    if freeze_exists; then
      freeze_precheck=1
      printf 'PLAYBOOK_SKIP command=deposit detail=phase-a-already-committed path=%s\n' \
        "$MODULE_PATH" >&2
      step deposit-header-check run_cli deposit-header-check --target "$MODULE_PATH"
    else
      status=$?
      [[ "$status" -eq 1 ]] || exit "$status"
      freeze_precheck=0
      step lean-report make lean-report
      step deposit-header-check run_cli deposit-header-check --target "$MODULE_PATH"
      step emit make emit
      step stage-phase-a commit_phase_a_if_needed
    fi
    step validate-formalization-receipt prepare_formalization_receipt
    freeze_module_if_needed "$freeze_precheck"
    install_prepared_formalization_receipt
    step stage-final-tree commit_all_if_needed "formalize: record deposit receipt for $GID"
    ;;
  cover)
    require_transaction_arguments
    cleanup_transaction_temporaries
    step lean-report make lean-report
    cover_row
    step emit-post-alignment make emit
    step stage-final-tree commit_all_if_needed "formalize: cover $ATOM_ID with $GID"
    ;;
  cover-batch)
    require_cover_batch_arguments
    cleanup_cover_batch_temporaries
    step lean-report make lean-report
    for index in "${!BATCH_ATOM_IDS[@]}"; do
      derive_cover_batch_row_state "$index"
      cover_batch_row
      step stage-final-tree commit_all_if_needed "formalize: cover $ATOM_ID with $GID"
    done
    step emit-post-alignment make emit
    step stage-final-tree commit_all_if_needed "formalize: emit projections after cover batch"
    ;;
  *)
    echo "usage: playbook-workflows.sh deliver-check|receipts-stage|deposit|cover|cover-batch [BASE] [ATOM_ID GID|ATOMS_FILE]" >&2
    exit 2
    ;;
esac
