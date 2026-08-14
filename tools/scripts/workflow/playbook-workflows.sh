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
PREPARED_RECEIPT_PATH=""
PREPARED_RECEIPT_ORIGINAL_PATH=""
PREPARED_RECEIPT_REPLACES_EXISTING=0

cleanup_prepared_receipt() {
  [[ -z "$PREPARED_RECEIPT_PATH" ]] || rm -f -- "$PREPARED_RECEIPT_PATH"
  [[ -z "$PREPARED_RECEIPT_ORIGINAL_PATH" ]] \
    || rm -f -- "$PREPARED_RECEIPT_ORIGINAL_PATH"
}
trap cleanup_prepared_receipt EXIT

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
  local active_state current_blob current_identity
  local ledger_files=()
  if ! command -v jq >/dev/null 2>&1; then
    echo "PLAYBOOK_INVALID jq is required to inspect $FROZEN_LEDGER" >&2
    return 2
  fi
  if [[ ! -d "$FROZEN_LEDGER" ]]; then
    echo "PLAYBOOK_INVALID frozen ledger is missing: $FROZEN_LEDGER" >&2
    return 2
  fi
  while IFS= read -r ledger_file; do
    ledger_files+=("$ledger_file")
  done < <(compgen -G "$FROZEN_LEDGER/*.json" || true)
  if [[ "${#ledger_files[@]}" -gt 0 ]] && ! jq empty "${ledger_files[@]}" >/dev/null; then
    echo "PLAYBOOK_INVALID frozen ledger contains invalid JSON: $FROZEN_LEDGER" >&2
    return 2
  fi

  if ! current_blob="$(git hash-object -- "$MODULE_PATH")"; then
    echo "PLAYBOOK_INVALID failed to identify current module: $MODULE_PATH" >&2
    return 2
  fi
  case "${#current_blob}" in
    40) current_identity="git-sha1:$current_blob" ;;
    64) current_identity="git-sha256:$current_blob" ;;
    *)
      echo "PLAYBOOK_INVALID git returned a malformed module identity: $current_blob" >&2
      return 2
      ;;
  esac
  [[ "${#ledger_files[@]}" -gt 0 ]] || return 1

  if ! active_state="$(jq -sc --arg node "$MODULE_PATH" --arg identity "$current_identity" '
      ([.[]
        | select(.event_type == "Revoke")
        | .payload.affected_frozen_node_ids[]] | unique) as $revoked_ids
      | . as $events
      | (reduce $events[] as $event ({};
          ($event.event_hash // null) as $event_hash
          | if (($event_hash | type) == "string") then .[$event_hash] = $event else . end
        )) as $events_by_hash
      | def replay_rank:
          if . == "Genesis" then 0
          elif . == "Freeze" then 1
          elif . == "Reattest" then 2
          elif . == "EnvironmentRecoordinate" then 2
          elif . == "Revoke" then 3
          else 4
          end;
      def attestation_depth($event; $visited):
          if $event.event_type == "Freeze" then
            0
          elif ($event.event_type == "Reattest" or $event.event_type == "EnvironmentRecoordinate") then
            ($event.event_hash // null) as $event_hash
            | if (($event_hash | type) != "string") then
                error("Reattest is missing its event hash")
              elif ($visited[$event_hash] // false) then
                error("Reattest chain contains a cycle")
              else
                ($event.payload.previous_attestation_event_hash // null) as $previous_hash
                | if (($previous_hash | type) != "string") then
                    error("Reattest references an unknown previous attestation")
                  else
                    ($events_by_hash[$previous_hash] // null) as $previous
                    | if (($previous | type) != "object") then
                        error("Reattest references an unknown previous attestation")
                      else
                        1 + attestation_depth($previous; $visited + {($event_hash): true})
                      end
                  end
              end
          else
            error("Reattest chain does not terminate at Freeze")
          end;
      to_entries
      | sort_by([
          (.value.event_type | replay_rank),
          (if (.value.event_type == "Reattest" or .value.event_type == "EnvironmentRecoordinate")
            then attestation_depth(.value; {}) else 0 end),
          .key
        ])
      | map(.value)
      | reduce .[] as $event ({};
        if $event.event_type == "Genesis" then
          .
        elif $event.event_type == "Freeze" then
          ($event.payload.case_id // null) as $case
          | ($event.payload.frozen_node_id // null) as $frozen_id
          | ($event.payload.node_path // null) as $path
          | ($event.payload.input.descriptor_blob_oid // null) as $blob
          | if (($case | type) != "string"
              or ($frozen_id | type) != "string"
              or ($path | type) != "string"
              or ($blob | type) != "string") then
              error("Freeze is missing replay identity fields")
            elif has($case) then
              error("Freeze reuses an active case")
            else
              .[$case] = {
                frozen_node_id: $frozen_id,
                node_path: $path,
                descriptor_blob_oid: $blob
              }
            end
        elif $event.event_type == "Reattest" then
          ($event.payload.case_id // null) as $case
          | ($event.payload.input.descriptor_blob_oid // null) as $blob
          | if (($case | type) != "string" or ($blob | type) != "string" or (has($case) | not)) then
              error("Reattest targets no active case or lacks module identity")
            else
              .[$case].descriptor_blob_oid = $blob
              | if (($event.payload.frozen_node_id? // null) | type) == "string" then
                  .[$case].frozen_node_id = $event.payload.frozen_node_id
                else . end
            end
        elif $event.event_type == "EnvironmentRecoordinate" then
          ($event.payload.case_id // null) as $case
          | ($event.payload.new_input.descriptor_blob_oid // null) as $blob
          | ($event.payload.new_frozen_node_id // null) as $frozen_id
          | if (($case | type) != "string"
              or ($blob | type) != "string"
              or ($frozen_id | type) != "string"
              or (has($case) | not)) then
              error("EnvironmentRecoordinate targets no active case or lacks module identity")
            else
              .[$case].descriptor_blob_oid = $blob
              | .[$case].frozen_node_id = $frozen_id
            end
        elif $event.event_type == "Revoke" then
          ($event.payload.affected_case_ids // null) as $cases
          | ($event.payload.affected_frozen_node_ids // null) as $frozen_ids
          | if (($cases | type) != "array" or ($frozen_ids | type) != "array") then
              error("Revoke is missing affected active identities")
            else
              .
            end
        else
          error("unknown frozen ledger event type")
        end)
      | with_entries(
          select(.value.frozen_node_id as $id | ($revoked_ids | index($id) | not)))
      | any(.[]; .node_path == $node and .descriptor_blob_oid == $identity)
    ' "${ledger_files[@]}" 2>&1)"; then
    echo "PLAYBOOK_INVALID failed to replay frozen ledger $FROZEN_LEDGER: $active_state" >&2
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
    --gid "$receipt_gid"
    --out "$temporary"
  )
  if [[ "$GID" != "$receipt_gid" ]]; then
    receipt_arguments+=(--gid "$GID" --require-existing-coverage true)
  fi

  printf 'PLAYBOOK_STEP command=deposit detail=validate-formalization-receipt\n' >&2
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
  local output primary_gid
  if ! primary_gid="$(jq -er \
      '.primary_gid | select(type == "string" and length > 0)' "$RECEIPT_PATH")"; then
    echo "PLAYBOOK_INVALID formalization receipt has no primary_gid: $RECEIPT_PATH" >&2
    return 2
  fi

  local gid_arguments=(--gid "$primary_gid")
  if [[ "$GID" != "$primary_gid" ]]; then
    gid_arguments+=(--gid "$GID")
  fi

  if output="$(run_cli cover-atom --cover-atom "$ATOM_ID" "${gid_arguments[@]}" \
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

cd "$ROOT"
case "$COMMAND" in
  deliver-check)
    make lean-report
    make emit
    receipts_stage
    # Freeze last among all mutating derivations so the receipt binds committed source bytes.
    run_cli ledger-append --candidate-lean-report "$REPORT"
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
    ;;
  deposit)
    require_transaction_arguments
    require_new_module_blueprint_mirror
    cleanup_transaction_temporaries
    if freeze_exists; then
      printf 'PLAYBOOK_SKIP command=deposit detail=phase-a-already-committed path=%s\n' \
        "$MODULE_PATH" >&2
    else
      status=$?
      [[ "$status" -eq 1 ]] || exit "$status"
      step lean-report make lean-report
      step emit make emit
      commit_phase_a_if_needed
    fi
    prepare_formalization_receipt
    freeze_module_if_needed
    install_prepared_formalization_receipt
    step lean-report-refresh make lean-report
    step emit-post-receipt make emit
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
    commit_all_if_needed "formalize: cover $ATOM_ID with $GID"
    ;;
  *)
    echo "usage: playbook-workflows.sh deliver-check|receipts-stage|derived-refresh|deposit|cover [BASE] [ATOM_ID GID]" >&2
    exit 2
    ;;
esac
