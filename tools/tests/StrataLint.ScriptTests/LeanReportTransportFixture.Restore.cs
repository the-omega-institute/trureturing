using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

internal sealed partial class LeanReportTransportFixture
{
    internal string[] RestoreEvents => Calls("restore-events.log");

    internal void SkewCachedProvenanceCoordinates() => Success(Run(["python3", "-c", """
        import json, pathlib, subprocess, sys
        report, helper = map(pathlib.Path, sys.argv[1:])
        provenance = pathlib.Path(str(report) + '.provenance.json')
        value = json.loads(provenance.read_text())
        value['lean_sources_sha256'] = '0' * 64
        pair, repository = subprocess.check_output(['bash', str(helper), 'coordinates',
            *(value[key] for key in ('producer_sha256', 'repository_inspector_sha256',
                                     'lean_sources_sha256', 'lean_config_sha256'))], text=True).split()
        value['input_address'] = 'sha256:' + pair
        provenance.write_text(json.dumps(value) + '\n')
        attestation = pathlib.Path(str(report) + '.input.attestation')
        lines = attestation.read_text().splitlines()
        lines[1] = 'repository_input_sha256=' + repository
        attestation.write_text('\n'.join(lines) + '\n')
        """, CachedReport, Path.Combine(Repository, "tools/scripts/report/lean-report-input.sh")]));

    // Install before producing the baseline. Fault selection lives outside the
    // repository input closure, and is armed only by a successful real validate.
    internal void PrepareRestoreFaults()
    {
        Executable(Path.Combine(Bin, "python3"), """
            if [[ -n "${FIXTURE_RESTORE_FAILURE:-}" && "${1:-}" == *lean-report-cache.py && "${2:-}" == validate ]]; then
              /usr/bin/python3 "$@"
              printf 'canonical-validate=0\n' >> "$REPORT_FIXTURE/restore-events.log"
              touch "$REPORT_FIXTURE/restore-validated"
              if [[ "$FIXTURE_RESTORE_FAILURE" == checksum-read ]]; then
                chmod 000 "$3.sha256"
                printf 'fault=checksum-read\n' >> "$REPORT_FIXTURE/restore-events.log"
              fi
              exit 0
            fi
            if [[ "${FIXTURE_RESTORE_FAILURE:-}" == input-evaluation && "${1:-}" == *lean-report-selection.py && -e "$REPORT_FIXTURE/restore-validated" ]]; then
              printf 'fault=input-evaluation\n' >> "$REPORT_FIXTURE/restore-events.log"
              printf 'fixture registered input reader unavailable\n' >&2
              exit 69
            fi
            exec /usr/bin/python3 "$@"
            """);
        Executable(Path.Combine(Bin, "bash"), """
            if [[ "${FIXTURE_RESTORE_FAILURE:-}" == input-evaluation && "${1:-}" == *lean-report-input.sh && "${2:-}" == verify ]]; then
              rc=0
              /bin/bash "$@" || rc=$?
              printf 'input-verify=%s\n' "$rc" >> "$REPORT_FIXTURE/restore-events.log"
              exit "$rc"
            fi
            exec /bin/bash "$@"
            """);
        var bash = Path.Combine(Bin, "bash");
        File.WriteAllText(bash, File.ReadAllText(bash).Replace("#!/usr/bin/env bash", "#!/bin/bash", StringComparison.Ordinal));
        Executable(Path.Combine(Bin, "awk"), """
            if [[ "${FIXTURE_RESTORE_FAILURE:-}" == checksum-lines && "${1:-}" == 'END {print NR}' && "${2:-}" == "$STRATALINT_REPORT_CACHE_ROOT/"* && -e "$REPORT_FIXTURE/restore-validated" ]]; then
              printf 'fault=checksum-lines\n' >> "$REPORT_FIXTURE/restore-events.log"
              printf '2\n'
              exit 74
            fi
            exec /usr/bin/awk "$@"
            """);
        Executable(Path.Combine(Bin, "sha256sum"), """
            if [[ "${FIXTURE_RESTORE_FAILURE:-}" == report-hash && "${1:-}" == */.lean-report-bundle.*/raw-lean-report.json && -e "$REPORT_FIXTURE/restore-validated" ]]; then
              printf 'fault=report-hash\n' >> "$REPORT_FIXTURE/restore-events.log"
              printf 'partial-hash  %s\n' "$1"
              exit 74
            fi
            exec /usr/bin/shasum -a 256 "$@"
            """);
        File.WriteAllText(Path.Combine(Bin, "sitecustomize.py"), PublicationClockStub + "\n" + """
            import errno, pathlib
            original_open = pathlib.Path.open
            def open_path(path, *args, **kwargs):
                seam = os.environ.get('FIXTURE_RESTORE_FAILURE', '')
                if (seam in ('provenance-read', 'provenance-runtime')
                        and path.name == 'raw-lean-report.json.provenance.json'
                        and path.parent.name.startswith('.lean-report-bundle.')
                        and (pathlib.Path(os.environ['REPORT_FIXTURE']) / 'restore-validated').exists()):
                    with original_open(pathlib.Path(os.environ['REPORT_FIXTURE']) / 'restore-events.log', 'a') as log:
                        log.write('fault=' + seam + '\n')
                    if seam == 'provenance-read': raise PermissionError(errno.EACCES, 'fixture provenance read unavailable', str(path))
                    raise RuntimeError('fixture provenance IO runtime unavailable')
                return original_open(path, *args, **kwargs)
            pathlib.Path.open = open_path
            """);
        Stub("tools/scripts/report/report-supervisor.sh", """
            printf 'slot\n' >> "$REPORT_FIXTURE/slot.log"
            while [[ "$1" != -- ]]; do shift; done
            shift
            if [[ -n "${FIXTURE_RESTORE_FAILURE:-}" ]]; then
              output="${@: -1}"
              for suffix in '' .sha256 .input.attestation .provenance.json .materials.zip; do
                [[ ! -e "$output$suffix" ]] || { echo 'partial restore reached producer' >&2; exit 88; }
              done
              printf 'private-output=clean\n' >> "$REPORT_FIXTURE/restore-events.log"
            fi
            exec "$@"
            """);
        address = null;
    }

    internal void FinishRestoreFault() => Success(Run(["python3", "-c", """
        import pathlib, sys
        report, output = map(pathlib.Path, sys.argv[1:])
        sidecar = pathlib.Path(str(report) + '.sha256')
        if sidecar.exists(): sidecar.chmod(0o600)
        assert not list(output.parent.glob('.lean-report-bundle.*')), 'private staging directory leaked'
        """, CachedReport, Output]));
}
