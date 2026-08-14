namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    private sealed partial class TransactionFixture
    {
        private void WriteMakeStub() => WriteExecutable("make", """
            printf 'make:%s\n' "$*" >> "$PLAYBOOK_TEST_CALLS"
            case "${1:-}" in
              lean-report)
                if [[ ${PLAYBOOK_STALE_REPORT:-0} != 1 ]]; then
                  cp D5/S0/Carrier/Probe.lean .report-source
                fi
                ;;
              emit)
                if ! cmp -s D5/S0/Carrier/Probe.lean .report-source; then
                  echo 'STALE_LEAN_REPORT emit refused stale input' >&2
                  exit 41
                fi
                if grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
                  printf 'emission: covered\n' > Blueprint/D5/S0/Carrier/Probe.md
                else
                  printf 'emission: open\n' > Blueprint/D5/S0/Carrier/Probe.md
                fi
                ;;
            esac
            """);

        private void WriteDotnetStub() => WriteExecutable("dotnet", """
            args="$*"
            command=${args##* -- }
            printf 'dotnet:%s\n' "$command" >> "$PLAYBOOK_TEST_CALLS"
            read -r -a parts <<< "$command"
            case "${parts[0]:-}" in
              ledger-append)
                target_module=${PLAYBOOK_TARGET_MODULE:-D5/S0/Carrier/Probe.lean}
                descriptor_blob_oid="git-sha1:$(git hash-object -- "$target_module")"
                base_commit_oid="git-sha1:$(git rev-parse HEAD)"
                if [[ $target_module == D5/S0/Carrier/Probe.lean ]]; then
                  event_id=2222222222222222222222222222222222222222222222222222222222222222
                else
                  event_id=3333333333333333333333333333333333333333333333333333333333333333
                fi
                printf '{"event_type": "Freeze", "payload": {"case_id": "active-frozen/%s", "frozen_node_id": "sha256:%s", "input": {"base_commit_oid": "%s", "descriptor_blob_oid": "%s"}, "node_path": "%s"}}\n' \
                  "$event_id" "$event_id" "$base_commit_oid" "$descriptor_blob_oid" "$target_module" \
                  > "Golden/Frozen/accepted/${event_id}.json"
                if [[ -n ${PLAYBOOK_MUTATE_RECEIPT_AFTER_PREPARE:-} ]]; then
                  printf '%s' "$PLAYBOOK_MUTATE_RECEIPT_AFTER_PREPARE" \
                    > Meta/Digestion/formalizations/atom-1.v1.json
                fi
                if [[ -f fail-ledger-once ]]; then
                  rm fail-ledger-once
                  echo 'LEDGER_APPEND_INTERRUPTED synthetic kill after append' >&2
                  exit 75
                fi
                ;;
              emit-formalization-receipt)
                if [[ ${PLAYBOOK_INVALID_RECEIPT:-0} == 1 ]]; then
                  echo 'FORMALIZATION_RECEIPT_INVALID synthetic canonical rejection' >&2
                  exit 45
                fi
                atom=''
                gids=()
                out=''
                require_existing_coverage=false
                for ((index=1; index<${#parts[@]}; index+=2)); do
                  case "${parts[index]}" in
                    --atom-id) atom=${parts[index+1]} ;;
                    --gid) gids+=("${parts[index+1]}") ;;
                    --out) out=${parts[index+1]} ;;
                    --require-existing-coverage) require_existing_coverage=${parts[index+1]} ;;
                  esac
                done
                primary_gid=${gids[0]:-}
                if [[ $require_existing_coverage == true \
                    && $primary_gid != D5/S0/Carrier/Probe.probe ]]; then
                  echo "FORMALIZATION_RECEIPT_INVALID receipt primary GID $primary_gid is not already bound to atom $atom" >&2
                  exit 46
                fi
                [[ -n $out ]] || out="Meta/Digestion/formalizations/${atom}.v1.json"
                mkdir -p "$(dirname "$out")"
                existing="Meta/Digestion/formalizations/${atom}.v1.json"
                if [[ ${#gids[@]} -gt 1 && -f $existing ]]; then
                  existing_atom=$(jq -r '.atom_id // ""' "$existing")
                  existing_primary=$(jq -r '.primary_gid // ""' "$existing")
                  if [[ $existing_atom != "$atom" || $existing_primary != "$primary_gid" ]]; then
                    echo "FORMALIZATION_RECEIPT_INVALID existing formalization receipt conflicts with atom/GID: $atom" >&2
                    exit 47
                  fi
                fi
                if [[ ${#gids[@]} -gt 1 ]]; then
                  secondary_gid=${gids[1]}
                  secondary_name=${secondary_gid##*.}
                  printf '{"atom_id":"%s","hosted_extensions":[{"gid":"%s","precommitted_signature":{"kind":"theorem","name_key":"%s","type":"True"}}],"primary_gid":"%s"}\n' \
                    "$atom" "$secondary_gid" "$secondary_name" "$primary_gid" > "$out"
                else
                  printf '{"atom_id":"%s","primary_gid":"%s"}\n' "$atom" "$primary_gid" > "$out"
                fi
                ;;
              cover-atom)
                if grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
                  [[ $command == *'--gid D5/S0/Carrier/Probe.probe --gid D5/S3/Observer/WindowRegisterCRT.window_register_crt_decomposition'* ]] || {
                    echo 'COVER_INVALID hosted cover omitted the primary GID' >&2
                    exit 1
                  }
                fi
                printf 'atom_id: atom-1\ncoverage: true\naligned: false\n' > Meta/BACKFILL.yaml
                ;;
              align-scribe-receipt)
                [[ $(cat Blueprint/D5/S0/Carrier/Probe.md) == 'emission: covered' ]] || {
                  echo 'ALIGN_SCRIBE_RECEIPT_INVALID emission is stale' >&2
                  exit 1
                }
                if grep -q '^aligned: covered$' Meta/BACKFILL.yaml; then
                  echo 'ALIGN_SCRIBE_RECEIPT ledger_changed=false'
                else
                  printf 'atom_id: atom-1\ncoverage: true\naligned: covered\n' > Meta/BACKFILL.yaml
                  echo 'ALIGN_SCRIBE_RECEIPT ledger_changed=true'
                fi
                ;;
            esac
            """);
    }
}
