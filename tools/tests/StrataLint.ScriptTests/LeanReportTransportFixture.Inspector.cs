using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

internal sealed partial class LeanReportTransportFixture
{
    internal const string AuxiliarySource = "tools/lean-inspector/LeanInformationAudit/Tests/SealEmptyBundle.lean";

    // A two-module repository with real report scripts. Only external tools
    // (MSBuild, utility input, the cache writer, and Lean) return synthetic data.
    internal void UseRealInspector()
    {
        File.Delete(Path.Combine(Repository, "tools/lean-inspector/inspect.sh"));
        foreach (var path in new[] { "tools/lean-inspector/inspect.sh", "tools/lean-inspector/materials.py",
                     "tools/scripts/lib/resource-observation-lib.sh", "tools/scripts/worktree/lean-cache-run.sh" })
            ScriptHarnessScratch.CopyScriptInto(Path.Combine(TestRepositoryLayout.FindRoot(), path), Path.Combine(Repository, path));
        WriteSource("D5/Probe.lean", "theorem probe : True := True.intro\n");
        WriteSource(AuxiliarySource, "-- auxiliary Lean source outside the managed module inventory\n");
        Executable(Path.Combine(Bin, "lake"), InspectorLakeStub);
        Executable(Path.Combine(Bin, "dotnet"), """
            if [[ "$1" == msbuild ]]; then
              printf '{"Items":{"Compile":[{"FullPath":"%s/Probe.cs"}]}}\n' "$(dirname "$2")"
            elif [[ "$1" == build ]]; then
              exit 0
            elif [[ "$1" == run ]]; then
              while [[ "$1" != -- ]]; do shift; done
              shift
              case "$1" in
                lean-utility-input) printf '{}\n' ;;
                worktree)
                  [[ "$2" == with-cache-writer && "$3" == -- ]]
                  shift 3
                  exec "$@"
                  ;;
                *) exit 2 ;;
              esac
            else
              exit 2
            fi
            """);
        address = null;
    }

    internal Attempt MakeInspectedReport() => MakeReport("STRATALINT_REPORT_CACHE_REMOTE=0", "LAKE_BIN=" + Path.Combine(Bin, "lake"));
    internal Attempt Input(params string[] arguments) => Run(["/bin/bash",
        Path.Combine(Repository, "tools/scripts/report/lean-report-input.sh"), .. arguments]);
    internal Attempt Validate(string report) => Run(["python3",
        Path.Combine(Repository, "tools/scripts/report/lean-report-cache.py"), "validate", report]);

    internal InspectorInputs ReadInspectorInputs()
    {
        var addressed = Input("address", "--repository", Repository);
        Success(addressed);
        var fields = addressed.Stdout.Trim().Split(' ');
        Assert.Equal(4, fields.Length);
        var coordinates = Input("coordinates", fields[1], fields[1], fields[2], fields[3]);
        Success(coordinates);
        var pair = coordinates.Stdout.Trim().Split(' ');
        Assert.Equal(2, pair.Length);
        Assert.Equal(fields[0], pair[1]);
        var inventory = Input("modules", "--repository", Repository);
        Success(inventory);
        var modules = inventory.Stdout.Trim().Split('\n').Order(StringComparer.Ordinal).ToArray();
        var hashes = modules.Select(line => Digest(File.ReadAllBytes(Path.Combine(Repository, line.Split('\t')[1])))).ToArray();
        return new InspectorInputs(pair[0], fields[0], fields[1], fields[1], fields[2], fields[3], modules, hashes);
    }

    internal sealed record InspectorInputs(string Pair, string Repository, string Producer, string Resident,
        string Sources, string Config, string[] Modules, string[] Hashes);

    private const string InspectorLakeStub = """
        if [[ "$*" == build ]]; then
          printf 'build\n' >> "$REPORT_FIXTURE/build.log"
          exit 0
        fi
        [[ "$1" == env && "$2" == lean && "$3" == --run ]]
        shift 4
        [[ "$1" == --output && "$3" == --material-spool && "$5" == --utility-input ]]
        printf 'produce\n' >> "$REPORT_FIXTURE/producer.log"
        python3 - "$@" <<'PY'
        import json, pathlib, sys
        args = sys.argv[1:]
        output, spool = pathlib.Path(args[1]), pathlib.Path(args[3])
        modules = []
        for index in range(6, len(args), 3):
            name, path, source = args[index:index+3]
            material_file = str(index) + '.statement'
            (spool / material_file).write_text('canonical material fixture\n')
            declaration = dict(name='probe', name_key='probe', kind='theorem', axioms=[],
                include_in_statement=True, material_file=material_file)
            modules.append(dict(module=name, source_path=path, source_sha256=source,
                imports=['D5.Probe'] if name == 'Trureturing' else [], declarations=[declaration]))
        output.write_text(json.dumps(dict(schema='stratalint-lean-inspector-spool-v1',
            modules=sorted(modules, key=lambda module: module['module']))) + '\n')
        PY
        """;
}
