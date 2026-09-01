using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    internal sealed partial class TransactionFixture
    {
        internal int FreezeProbeCount() => File.Exists(freezeProbePath)
            ? File.ReadAllLines(freezeProbePath).Length
            : 0;

        private void CopyScript()
        {
            var root = TestRepositoryLayout.FindRoot();
            var target = Path.Combine(Root, ScriptPath);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(Path.Combine(root, ScriptPath), target);
        }

        private void WriteGitGuardStub() => WriteExecutable("git", """
            arguments=("$@")
            index=0
            while [[ $index -lt ${#arguments[@]} ]]; do
              token=${arguments[index]}
              case "$token" in
                -C|-c|--git-dir|--work-tree|--namespace|--super-prefix|--config-env)
                  index=$((index + 2))
                  ;;
                --git-dir=*|--work-tree=*|--namespace=*|--super-prefix=*|--config-env=*)
                  index=$((index + 1))
                  ;;
                --no-pager|--paginate|--bare|--literal-pathspecs|--no-literal-pathspecs|--glob-pathspecs|--noglob-pathspecs|--icase-pathspecs)
                  index=$((index + 1))
                  ;;
                --)
                  index=$((index + 1))
                  break
                  ;;
                -*) index=$((index + 1)) ;;
                *) break ;;
              esac
            done
            subcommand=${arguments[index]:-}
            if [[ $subcommand == hash-object && ${PLAYBOOK_INSIDE_LEDGER_STUB:-0} != 1 ]]; then
              printf 'freeze-exists\n' >> "$PLAYBOOK_TEST_FREEZE_PROBES"
            fi
            if [[ $subcommand == merge ]]; then
              printf 'git-branch-merge:%s\n' "${arguments[*]}" >> "$PLAYBOOK_TEST_CALLS"
              exit 97
            fi
            exec /usr/bin/git "${arguments[@]}"
            """);

        private void WriteMakeStub() => WriteExecutable("make", """
            printf 'make:%s\n' "$*" >> "$PLAYBOOK_TEST_CALLS"
            case "${1:-}" in
              lean-report)
                if compgen -G 'Meta/Digestion/formalizations/*.tmp.*' > /dev/null; then
                  echo 'LEAN_REPORT_INVALID interrupted receipt temporary still exists' >&2
                  exit 42
                fi
                mkdir -p .lake/build/stratalint
                printf '{"schema":"synthetic-lean-report"}\n' \
                  > .lake/build/stratalint/raw-lean-report.json
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
              deposit-header-check)
                if [[ ${parts[1]:-} != --target \
                    || ${parts[2]:-} != "${PLAYBOOK_TARGET_MODULE:-}" ]]; then
                  echo 'DEPOSIT_HEADER_CHECK_INVALID synthetic target transport mismatch' >&2
                  exit 96
                fi
                if [[ ${PLAYBOOK_REJECT_DEPOSIT_HEADER:-0} == 1 ]]; then
                  printf 'SL-012 %s: expected the exact six-line header at byte zero\n' \
                    "${parts[2]}"
                  exit 1
                fi
                ;;
              ledger-append)
                target_module=${PLAYBOOK_TARGET_MODULE:-D5/S0/Carrier/Probe.lean}
                if [[ $target_module == D5/S0/Carrier/Probe.lean ]]; then
                  event_id=2222222222222222222222222222222222222222222222222222222222222222
                else
                  event_id=3333333333333333333333333333333333333333333333333333333333333333
                fi
                printf '{"event_hash":"sha256:%s","event_type":"Freeze","payload":{"declaration_statement_ids":[],"descriptor_selector":"%s","prerequisite_frozen_node_ids":[],"statement_id":"sha256:%s"},"schema_version":5}\n' \
                  "$event_id" "$target_module" "$event_id" \
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
                for ((index=1; index<${#parts[@]}; index+=2)); do
                  case "${parts[index]}" in
                    --atom-id) atom=${parts[index+1]} ;;
                    --gid) gids+=("${parts[index+1]}") ;;
                    --out) out=${parts[index+1]} ;;
                  esac
                done
                requested_gid=${gids[0]:-}
                primary_gid=$requested_gid
                [[ -n $out ]] || out="Meta/Digestion/formalizations/${atom}.v1.json"
                mkdir -p "$(dirname "$out")"
                existing="Meta/Digestion/formalizations/${atom}.v1.json"
                if [[ -f $existing ]]; then
                  existing_atom=$(jq -r '.atom_id // ""' "$existing")
                  existing_primary=$(jq -r '.primary_gid // ""' "$existing")
                  if [[ $existing_atom != "$atom" || -z $existing_primary ]]; then
                    echo "FORMALIZATION_RECEIPT_INVALID existing formalization receipt conflicts with atom: $atom" >&2
                    exit 47
                  fi
                  primary_gid=$existing_primary
                fi
                if [[ -f $existing && $requested_gid != "$primary_gid" ]]; then
                  secondary_name=${requested_gid##*.}
                  printf '{"atom_id":"%s","hosted_extensions":[{"gid":"%s","precommitted_signature":{"kind":"theorem","name_key":"%s","type":"True"}}],"primary_gid":"%s"}\n' \
                    "$atom" "$requested_gid" "$secondary_name" "$primary_gid" > "$out"
                elif [[ -f $existing ]]; then
                  cp -- "$existing" "$out"
                else
                  printf '{"atom_id":"%s","primary_gid":"%s"}\n' "$atom" "$primary_gid" > "$out"
                fi
                ;;
              cover-atom)
                atom=''
                gid=''
                envelope=''
                align=0
                for ((index=1; index<${#parts[@]}; index+=2)); do
                  case "${parts[index]}" in
                    --cover-atom) atom=${parts[index+1]} ;;
                    --gid) gid=${parts[index+1]} ;;
                    --envelope) envelope=${parts[index+1]} ;;
                    --align-scribe-receipt) align=1 ;;
                  esac
                done
                expected_envelope="Meta/Digestion/formalizations/${atom}.v1.json"
                if [[ $envelope != "$expected_envelope" ]]; then
                  echo "COVER_INVALID envelope $envelope does not match atom $atom" >&2
                  exit 46
                fi
                if [[ ${PLAYBOOK_COVER_DISPOSITION_FAILURE:-0} == 1 ]]; then
                  printf 'atom_id: %s\ncoverage: false\naligned: false\ncover_disposition: synthetic\n' "$atom" \
                    > Meta/BACKFILL.yaml
                  [[ $align -eq 0 ]] || echo 'COVER_ATOM_ALIGNED cover=failed' >&2
                  echo 'COVER_INVALID synthetic disposition' >&2
                  exit 1
                fi
                secondary=''
                existing_atom=$(sed -n 's/^atom_id: //p' Meta/BACKFILL.yaml)
                if [[ $existing_atom == "$atom" ]] \
                    && grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
                  [[ $gid == D5/S3/Observer/WindowRegisterCRT.window_register_crt_decomposition ]] || {
                    echo 'COVER_INVALID hosted cover omitted the selected secondary GID' >&2
                    exit 1
                  }
                  secondary='secondary: true'
                fi
                printf 'atom_id: %s\ncoverage: true\naligned: false\n%s\n' \
                  "$atom" "$secondary" > Meta/BACKFILL.yaml
                if [[ $align -eq 1 ]]; then
                  definition_path="Blueprint/${gid%.*}.scribe.cs"
                  verified_emission=''
                  if [[ -s $definition_path ]] \
                      && grep -q "^atom_id: ${atom}$" Meta/BACKFILL.yaml \
                      && grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
                    verified_emission='emission: covered'
                  fi
                  [[ $verified_emission == 'emission: covered' ]] || {
                    echo 'COVER_ATOM_ALIGNED cover=passed align=failed' >&2
                    echo 'ALIGN_SCRIBE_RECEIPT_INVALID no verified in-process Scribe emission' >&2
                    exit 1
                  }
                  printf 'atom_id: %s\ncoverage: true\naligned: covered\n%s\n' \
                    "$atom" "$secondary" > Meta/BACKFILL.yaml
                  echo 'COVER_ATOM_ALIGNED cover=passed align=passed'
                  echo 'ALIGN_SCRIBE_RECEIPT ledger_changed=true'
                fi
                ;;
              align-scribe-receipt)
                atom=''
                gid=''
                for ((index=1; index<${#parts[@]}; index+=2)); do
                  case "${parts[index]}" in
                    --atom-id) atom=${parts[index+1]} ;;
                    --gid) gid=${parts[index+1]} ;;
                  esac
                done
                definition_path="Blueprint/${gid%.*}.scribe.cs"
                verified_emission=''
                if [[ -s $definition_path ]] \
                    && grep -q "^atom_id: ${atom}$" Meta/BACKFILL.yaml \
                    && grep -q '^coverage: true$' Meta/BACKFILL.yaml; then
                  verified_emission='emission: covered'
                fi
                [[ $verified_emission == 'emission: covered' ]] || {
                  echo 'ALIGN_SCRIBE_RECEIPT_INVALID no verified in-process Scribe emission' >&2
                  exit 1
                }
                secondary=''
                grep -q '^secondary: true$' Meta/BACKFILL.yaml && secondary='secondary: true'
                if grep -q '^aligned: covered$' Meta/BACKFILL.yaml; then
                  echo 'ALIGN_SCRIBE_RECEIPT ledger_changed=false'
                else
                  printf 'atom_id: %s\ncoverage: true\naligned: covered\n%s\n' \
                    "$atom" "$secondary" > Meta/BACKFILL.yaml
                  echo 'ALIGN_SCRIBE_RECEIPT ledger_changed=true'
                fi
                ;;
            esac
            """);

        internal ProcessOutput Run(
            string command,
            string gid = Gid,
            string atomId = AtomId,
            bool staleReport = false,
            bool invalidReceipt = false,
            bool coverDispositionFailure = false,
            string? mutateReceiptAfterPrepare = null,
            TimeSpan? timeout = null,
            string? baseRevision = null,
            bool rejectDepositHeader = false) =>
            TestProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                    $"PLAYBOOK_TEST_CALLS={callsPath}",
                    $"PLAYBOOK_TEST_FREEZE_PROBES={freezeProbePath}",
                    $"PLAYBOOK_STALE_REPORT={(staleReport ? "1" : "0")}",
                    $"PLAYBOOK_INVALID_RECEIPT={(invalidReceipt ? "1" : "0")}",
                    $"PLAYBOOK_COVER_DISPOSITION_FAILURE={(coverDispositionFailure ? "1" : "0")}",
                    $"PLAYBOOK_MUTATE_RECEIPT_AFTER_PREPARE={mutateReceiptAfterPrepare ?? string.Empty}",
                    $"PLAYBOOK_TARGET_MODULE={(gid == SecondaryGid ? SecondaryLeanPath : gid == NewGid ? NewLeanPath : LeanPath)}",
                    $"PLAYBOOK_REJECT_DEPOSIT_HEADER={(rejectDepositHeader ? "1" : "0")}",
                    "/bin/bash",
                    Path.Combine(Root, ScriptPath),
                    command,
                    baseRevision ?? (command == "deposit" ? "HEAD" : "synthetic-base"),
                    atomId,
                    gid,
                ],
                Root,
                timeout ?? BoundedProcessRunner.HangDetectionBudget,
                128 * 1024);

        public void Dispose()
        {
            temporary.Dispose();
        }
    }
}
