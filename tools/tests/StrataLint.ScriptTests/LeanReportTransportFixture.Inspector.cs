using File = StrataLint.TestSupport.TemporaryFileSystem.File;

namespace StrataLint.Tests;

internal sealed partial class LeanReportTransportFixture
{
    internal const string AuxiliarySource = "tools/lean-inspector/LeanInformationAudit/Tests/SealEmptyBundle.lean";

    // A two-module repository with real report scripts. Only external tools
    // (utility input, the cache writer, and Lean) return synthetic data.
    internal void UseRealInspector()
    {
        File.Delete(Path.Combine(Repository, "tools/lean-inspector/inspect.sh"));
        foreach (var path in new[] { "tools/lean-inspector/inspect.sh",
                     "tools/lean-inspector/Census/config.lean",
                     "tools/scripts/lib/resource-observation-lib.sh", "tools/scripts/worktree/lean-cache-run.sh" })
            ScriptHarnessScratch.CopyScriptInto(Path.Combine(TestRepositoryLayout.FindRoot(), path), Path.Combine(Repository, path));
        WriteSource("D5/Probe.lean", "theorem probe : True := True.intro\n");
        WriteSource(AuxiliarySource, "-- auxiliary Lean source outside the managed module inventory\n");
        SetBuildConfiguration();
        SetUtilityInput("[]\n");
        Executable(Path.Combine(Bin, "lake"), InspectorLakeStub);
        Executable(Path.Combine(Bin, "dotnet"), """
            if [[ "$1" == build ]]; then
              exit 0
            elif [[ "$1" == run ]]; then
              while [[ "$1" != -- ]]; do shift; done
              shift
              case "$1" in
                lean-utility-input)
                  printf 'utility\n' >> "$REPORT_FIXTURE/utility.log"
                  [[ "${FIXTURE_UTILITY_EXIT:-0}" == 0 ]] || exit "$FIXTURE_UTILITY_EXIT"
                  cat "$REPORT_FIXTURE/utility-input.json"
                  ;;
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

    internal Attempt MakeInspectedReport(params string[] environment) => MakeReport(
        new[] { "STRATALINT_REPORT_CACHE_REMOTE=0", "LAKE_BIN=" + Path.Combine(Bin, "lake") }
            .Concat(environment).ToArray());
    internal Attempt Inspect(params string[] environment) => Run([
        Path.Combine(Repository, "tools/lean-inspector/inspect.sh"), "--repository", Repository, "--output", Output],
        new[] { "LAKE_BIN=" + Path.Combine(Bin, "lake") }.Concat(environment).ToArray());
    internal void SetBuildConfiguration(string reportOptions = "", bool extraDefault = false)
    {
        var defaults = extraDefault
            ? new[] { "Trureturing", "LeanInformationAudit", "D5.Probe" }
            : new[] { "Trureturing", "LeanInformationAudit" };
        WriteSource("lakefile.toml", "name = \"fixture\"\ndefaultTargets = "
            + System.Text.Json.JsonSerializer.Serialize(defaults) + "\n"
            + "[[lean_lib]]\nname = \"Trureturing\"\nroots = [\"Trureturing\", \"D5\"]\nglobs = [\"Trureturing\", \"D5.+\"]\n"
            + reportOptions + "\n[[lean_lib]]\nname = \"LeanInformationAudit\"\n"
            + "srcDir = \"tools/lean-inspector\"\nroots = [\"LeanInformationAudit\"]\nglobs = [\"LeanInformationAudit.+\"]\n");
        var library = System.Text.Json.Nodes.JsonNode.Parse(
            "{\"name\":\"Trureturing\",\"roots\":[\"Trureturing\",\"D5\"],\"globs\":[\"Trureturing\",\"D5.+\"]}")!;
        if (reportOptions.Length > 0) library["defaultFacets"] = new System.Text.Json.Nodes.JsonArray("static");
        File.WriteAllText(Path.Combine(temporary.Path, "lake-config.json"),
            new System.Text.Json.Nodes.JsonObject
            {
                ["defaultTargets"] = System.Text.Json.JsonSerializer.SerializeToNode(defaults),
                ["lean_lib"] = new System.Text.Json.Nodes.JsonArray(library),
            }.ToJsonString());
    }

    internal string Phase(string name, string suffix) => File.ReadAllText(Output + ".logs/" + name + "." + suffix + ".log").Trim();

    internal void UseNativeLean()
    {
        UseRealInspector();
        foreach (var path in new[] { "lean-toolchain", "tools/lean-inspector/Inspector.lean" })
        {
            File.Delete(Path.Combine(Repository, path));
            ScriptHarnessScratch.CopyScriptInto(Path.Combine(TestRepositoryLayout.FindRoot(), path), Path.Combine(Repository, path));
        }
        WriteSource("lake-manifest.json", "{\"version\":\"1.1.0\",\"packages\":[],\"name\":\"fixture\",\"lakeDir\":\".lake\"}\n");
        WriteSource("D5/External.lean", "def claim : Prop := False\n");
        WriteSource("D5/Unchanged.lean", "def untouched : Nat := 9\n");
        WriteSource("Trureturing.lean", "import D5.Probe\ntheorem result : ¬ False := fun h => h\n");
        WriteSource("tools/lean-inspector/LeanInformationAudit/One.lean", "def auditOne : Nat := 1\n");
        WriteSource("tools/lean-inspector/LeanInformationAudit/Two.lean", "def auditTwo : Nat := 2\n");
        SetUtilityInput(System.Text.Json.JsonSerializer.Serialize(new[] { new
        {
            modulePath = "Trureturing.lean", claimGid = "D5/External.claim", claimModule = "D5.External",
            claimSelector = "claim", claimSourcePath = "D5/External.lean",
            claimSourceSha256 = "sha256:" + Digest(File.ReadAllBytes(Path.Combine(Repository, "D5/External.lean"))),
            resultGid = "Trureturing.result", resultModule = "Trureturing", resultSelector = "result",
        } }));
    }

    internal Attempt MakeNativeReport(string lake)
    {
        var result = TestProcessRunner.Run("env", [
            $"PATH={Bin}:{Environment.GetEnvironmentVariable("PATH")}", $"REPORT_FIXTURE={temporary.Path}",
            $"REPORT_REPOSITORY={Repository}", $"STRATALINT_REPORT_CACHE_ROOT={CacheRoot}",
            "STRATALINT_REPORT_CACHE_REMOTE=0", $"LAKE_BIN={Path.Combine(Bin, "lake")}",
            $"FIXTURE_NATIVE_LAKE={lake}", "make", "lean-report"],
            Repository, StrataLint.Engine.BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        return new Attempt(result.ExitCode, System.Text.Encoding.UTF8.GetString(result.StandardOutput),
            System.Text.Encoding.UTF8.GetString(result.StandardError));
    }
    internal Attempt Input(params string[] arguments) => Run(["/bin/bash",
        Path.Combine(Repository, "tools/scripts/report/lean-report-input.sh"), .. arguments]);
    internal Attempt InspectReuse(InspectorInputs inputs) => Run([
        Path.Combine(Repository, "tools/lean-inspector/inspect.sh"), "--repository", Repository, "--output", Output],
        "LAKE_BIN=" + Path.Combine(Bin, "lake"), "STRATALINT_REPORT_INPUT_ADDRESS=" + new string('f', 64),
        "STRATALINT_REPORT_REPOSITORY_SHA256=" + inputs.Repository,
        "STRATALINT_REPORT_PRODUCER_SHA256=" + inputs.Producer,
        "STRATALINT_REPORT_RESIDENT_SHA256=" + inputs.Resident,
        "STRATALINT_REPORT_CONFIG_SHA256=" + inputs.Config);
    internal void AddIndependentRemovedModule()
    {
        WriteSource("D5/Removed.lean", "def removed : Nat := 0\n");
        var policy = System.Text.Json.Nodes.JsonNode.Parse(File.ReadAllText(Path.Combine(Repository, "lean-report-inputs.json")))!;
        var cohorts = policy["impact_cohorts"]!.AsArray();
        cohorts[1]!["exclude"] = new System.Text.Json.Nodes.JsonArray("D5/Removed.lean");
        cohorts.Add(System.Text.Json.Nodes.JsonNode.Parse(
            "{\"id\":\"removed\",\"members\":[\"D5/Removed.lean\"],\"exclude\":[],\"depends_on\":[]}"));
        WriteSource("lean-report-inputs.json", policy.ToJsonString());
    }
    internal Attempt Validate(string report) => Run(["python3",
        Path.Combine(Repository, "tools/scripts/report/lean-report-cache.py"), "validate", report]);
    internal string[][] ExtractedModules => Calls("extractions.jsonl")
        .Select(line => System.Text.Json.JsonSerializer.Deserialize<string[]>(line)!).ToArray();

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
        if [[ "$1" == build ]]; then
          printf '%s\n' "$*" >> "$REPORT_FIXTURE/build.log"
          printf 'build\n' >> "$REPORT_FIXTURE/events.log"
          if [[ -n "${FIXTURE_NATIVE_LAKE:-}" ]]; then exec "$FIXTURE_NATIVE_LAKE" "$@"; fi
          if [[ $# == 1 ]]; then exit "${FIXTURE_DEFAULT_BUILD_EXIT:-${FIXTURE_BUILD_EXIT:-0}}"; fi
          exit "${FIXTURE_BUILD_EXIT:-0}"
        fi
        [[ "$1" == env && "$2" == lean && "$3" == --run ]]
        if [[ -n "${FIXTURE_NATIVE_LAKE:-}" ]]; then exec "$FIXTURE_NATIVE_LAKE" "$@"; fi
        if [[ "$4" == */Census/config.lean ]]; then
          cat "$REPORT_FIXTURE/lake-config.json"
          exit 0
        fi
        printf 'inspect\n' >> "$REPORT_FIXTURE/events.log"
        if [[ -n "${FIXTURE_INSPECT_EXIT_ONCE:-}" && ! -e "$REPORT_FIXTURE/inspect-failed" ]]; then
          touch "$REPORT_FIXTURE/inspect-failed"
          exit "$FIXTURE_INSPECT_EXIT_ONCE"
        fi
        shift 4
        [[ "$1" == --output && "$3" == --material-spool && "$5" == --utility-input ]]
        printf 'produce\n' >> "$REPORT_FIXTURE/producer.log"
        python3 - "$@" <<'PY'
        import json, os, pathlib, sys
        args = sys.argv[1:]
        output, spool = pathlib.Path(args[1]), pathlib.Path(args[3])
        modules = []
        for index in range(6, len(args), 3):
            name, path, source = args[index:index+3]
            material_file = str(index) + '.statement'
            (spool / material_file).write_text('canonical material fixture ' + name + '\n')
            declaration = dict(name='probe', name_key='probe', kind='theorem', axioms=[],
                include_in_statement=True, material_file=material_file)
            modules.append(dict(module=name, source_path=path, source_sha256=source,
                imports=['D5.Probe'] if name == 'Trureturing' else [], declarations=[declaration]))
        with (pathlib.Path(os.environ['REPORT_FIXTURE']) / 'extractions.jsonl').open('a') as log:
            log.write(json.dumps([module['module'] for module in modules]) + '\n')
        output.write_text(json.dumps(dict(schema='stratalint-lean-inspector-spool-v1',
            modules=sorted(modules, key=lambda module: module['module']))) + '\n')
        PY
        """;
}
