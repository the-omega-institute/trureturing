// Demand-selection probe for the native report fixture.
using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Xml.Linq;
using StrataLint.EngineeringScope;
using Xunit;

namespace StrataLint.TestSupport;

internal static class NativeReportFixture
{
    internal static (int Exit, string Text) ProduceReport(string root)
    {
        var repository = TestRepositoryLayout.FindRoot();
        return EngineeringProcess.Process(root, "python3", ["-B", "-c", """
            import json, pathlib, shutil, sys, time
            repository, root, relative = map(pathlib.Path, sys.argv[1:])
            sys.path.insert(0, str(repository / 'tools/lean-inspector/tests'))
            from test_native import NativeTests
            import publication
            NativeTests.setUpClass()
            fixture = NativeTests('test_native_invalidation')
            fixture.setUp()
            phases = fixture.root / 'native-phases.jsonl'
            fixture.env['STRATALINT_INSPECTOR_PHASES'] = str(phases)
            observation = {'processes': None, 'phase_lines': 0}
            owned_processes = fixture.owned_processes
            def observed_processes(command, **options):
                rows = owned_processes(command, **options)
                identity = sorted((row['pid'], row['identity'], row['command']) for row in rows)
                if identity != observation['processes']:
                    print('NATIVE_HANDOFF_PROCESSES ' + json.dumps(dict(
                        monotonic_ms=time.monotonic_ns() // 1_000_000, processes=rows)),
                        file=sys.stderr, flush=True)
                    observation['processes'] = identity
                if phases.exists():
                    lines = phases.read_text().splitlines()
                    for line in lines[observation['phase_lines']:]:
                        print('NATIVE_HANDOFF_PHASE ' + line, file=sys.stderr, flush=True)
                    observation['phase_lines'] = len(lines)
                return rows
            fixture.owned_processes = observed_processes
            run_command = fixture.guarded_command
            def observed_output(stream, text):
                print('NATIVE_HANDOFF_OUTPUT ' + json.dumps(dict(stream=stream, text=text)),
                    file=sys.stderr, flush=True)
            def observed_command(args, **options):
                if pathlib.Path(args[0]).name == 'lake' and 'build' in args:
                    args = [args[0], '--verbose', *args[1:]]
                print('NATIVE_HANDOFF_COMMAND ' + json.dumps(list(args)), file=sys.stderr, flush=True)
                result = run_command(args, observe_output=observed_output, **options)
                print('NATIVE_HANDOFF_COMMAND_EXIT ' + str(result.returncode), file=sys.stderr, flush=True)
                return result
            fixture.guarded_command = observed_command
            try:
                # Native fixtures supply real Lake facets; this shape uses the
                # managed module names consumed by the C# report reader.
                source = fixture.root / 'Fixture.lean'
                source.rename(fixture.root / 'Trureturing.lean')
                for name in ('lakefile.toml', 'lean-report-inputs.json', 'utility.json'):
                    path = fixture.root / name
                    path.write_text(path.read_text().replace('Fixture', 'Trureturing'))
                fixture.write('utility.json', '[]\n')
                fixture.build()
                print('NATIVE_HANDOFF_PUBLISH', file=sys.stderr, flush=True)
                fixture.publish()
                for name in ('D5', 'Trureturing.lean', 'External.lean', 'ClaimSupport.lean',
                        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
                    source, target = fixture.root / name, root / name
                    if source.is_dir(): shutil.copytree(source, target, dirs_exist_ok=True)
                    else: shutil.copyfile(source, target)
                destination = root / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                for suffix in publication.SUFFIXES:
                    shutil.copyfile(publication.member(fixture.root / 'public.json', suffix),
                                    publication.member(destination, suffix))
                publication.member(destination, '.sha256').write_text(publication.digest(destination)
                    + '  ' + destination.name + '\n')
                print('NATIVE_CURRENT_HANDOFF files=' + str(len(publication.SUFFIXES)))
            finally:
                fixture.doCleanups()
            """, repository, root, CommonExecutionEvidence.ReportPath],
            hangGuard: TestBudgets.WorkflowProcessHangGuard);
    }




}
