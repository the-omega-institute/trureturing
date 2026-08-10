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
              echo-residual-summary)
                if [[ ${PLAYBOOK_FAIL_ECHO:-0} == 1 ]]; then
                  printf 'partial projection'
                  echo 'ECHO_PROJECTION_FAILED synthetic interruption' >&2
                  exit 42
                fi
                if grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
                  printf 'echo: covered\n'
                elif [[ -f Meta/Digestion/formalizations/atom-1.v1.json ]]; then
                  printf 'echo: receipt\n'
                else
                  printf 'echo: open\n'
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
                descriptor_blob_oid="git-sha1:$(git hash-object -- D5/S0/Carrier/Probe.lean)"
                printf '{"event_type": "Freeze", "payload": {"case_id": "active-frozen/current-probe", "frozen_node_id": "sha256:2222222222222222222222222222222222222222222222222222222222222222", "input": {"descriptor_blob_oid": "%s"}, "node_path": "D5/S0/Carrier/Probe.lean"}}\n' \
                  "$descriptor_blob_oid" > Meta/StrataLint/Golden/Frozen/accepted/2222222222222222222222222222222222222222222222222222222222222222.json
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
                gid=''
                out=''
                for ((index=1; index<${#parts[@]}; index+=2)); do
                  case "${parts[index]}" in
                    --atom-id) atom=${parts[index+1]} ;;
                    --gid) gid=${parts[index+1]} ;;
                    --out) out=${parts[index+1]} ;;
                  esac
                done
                [[ -n $out ]] || out="Meta/Digestion/formalizations/${atom}.v1.json"
                mkdir -p "$(dirname "$out")"
                printf '{"atom_id":"%s","primary_gid":"%s"}\n' "$atom" "$gid" > "$out"
                ;;
              cover-atom)
                if grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
                  echo 'COVER_INVALID cover atom atom-1 already has coverage: D5/S0/Carrier/Probe.probe' >&2
                  exit 1
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
