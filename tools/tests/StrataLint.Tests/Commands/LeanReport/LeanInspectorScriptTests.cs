using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class LeanInspectorScriptTests
{
    private const string InspectorScript = "tools/lean-inspector/inspect.sh";
    private const string InspectorSource = "tools/lean-inspector/Inspector.lean";
    private const string MaterialCompactor = "tools/lean-inspector/materials.py";
    private const string InputScript = "tools/scripts/report/lean-report-input.sh";
    private const string ResourceObservationLibrary = "tools/scripts/lib/resource-observation-lib.sh";
    private const string CacheRunScript = "tools/scripts/worktree/lean-cache-run.sh";

    [Theory]
    [InlineData("reuse")]
    [InlineData("delta-empty")]
    [InlineData("delta")]
    [InlineData("delta-all")]
    [InlineData("fallback")]
    public void InspectorExecutesThePlannedBuildScope(string mode)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var (result, calls) = RunPlannedInspector(temporary.Path, mode);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal("runtime-prefix", calls[0][0]);
        Assert.Equal("plan", calls[1][0]);
        var builds = calls.Where(static call => call[0] == "build").ToArray();
        var inspections = calls.Where(static call => call[0] == "inspect").ToArray();
        if (mode is "reuse" or "delta-empty")
        {
            Assert.Equal(new[] { "runtime-prefix", "plan", "merge" }, calls.Select(static call => call[0]));
            Assert.Empty(builds);
            Assert.Empty(inspections);
            Assert.Equal("baseline", File.ReadAllText(Path.Combine(temporary.Path, "report.json")));
            Assert.Equal("baseline-materials", File.ReadAllText(Path.Combine(temporary.Path, "report.json.materials.zip")));
        }
        else
        {
            Assert.Equal(mode == "delta" ? ["build", "+D5.Probe"] : new[] { "build" }, Assert.Single(builds));
            var inspection = Assert.Single(inspections);
            Assert.Contains("D5.Probe", inspection);
            Assert.Equal(mode != "delta", inspection.Contains("Trureturing", StringComparer.Ordinal));
        }
        Assert.Contains("RAW_LEAN_REPORT", Encoding.UTF8.GetString(result.StandardOutput));
    }

    [Theory]
    [InlineData("reuse", false)]
    [InlineData("removal-only", false)]
    [InlineData("reuse", true)]
    [InlineData("removal-only", true)]
    public void InspectorProducesPhaseLogsWithoutBuildOrInspection(string mode, bool relativeCacheRoot)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var (result, calls) = RunPlannedInspector(temporary.Path, mode, relativeCacheRoot: relativeCacheRoot);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(new[] { "runtime-prefix", "plan", "merge" },
            calls.Select(static call => call[0]));
        var reuse = mode == "reuse";
        var deltaSummary = $"mode={(reuse ? "reuse" : "delta")} changed=0 added=0 removed={(reuse ? 0 : 1)} recheck=0";
        var stdout = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Contains("LEAN_REPORT_DELTA_PLAN " + deltaSummary, stdout);
        Assert.Contains("LEAN_REPORT_DELTA " + deltaSummary, stdout);
        var output = Path.Combine(temporary.Path, "report.json");
        Assert.Equal(reuse ? "baseline" : "merged", File.ReadAllText(output));
        Assert.Equal(reuse ? "baseline-materials" : "merged-materials", FixtureFile.ReadAllText(output + ".materials.zip"));
        var digest = Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(output))).ToLowerInvariant();
        Assert.Equal($"{digest}  report.json\n", FixtureFile.ReadAllText(output + ".sha256"));
        Assert.Contains($"RAW_LEAN_REPORT file={output} content_address=sha256:{digest}", stdout);

        AssertSuccessfulPhaseLogs(output + ".logs", "delta-merge", "delta.py merge ",
            "fixture merge stdout\n", "fixture merge stderr\n");
    }

    [Theory]
    [InlineData("utility-input-build", false)]
    [InlineData("utility-input", false)]
    [InlineData("utility-input", true)]
    [InlineData("build", false)]
    [InlineData("inspect", false)]
    [InlineData("compact", false)]
    public void InspectorStopsImmediatelyWhenADeltaProducerPhaseFails(string failedPhase, bool prebuilt)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var (result, calls) = RunPlannedInspector(temporary.Path, "delta", failedPhase, prebuilt: prebuilt);

        Assert.Equal(17, result.ExitCode);
        string[] phases = prebuilt
            ? ["runtime-prefix", "plan", "utility-input", "build", "inspect", "compact"]
            : ["runtime-prefix", "plan", "utility-input-build", "utility-input", "build", "inspect", "compact"];
        Assert.Equal(phases.Take(Array.IndexOf(phases, failedPhase) + 1), calls.Select(static call => call[0]));
        AssertNoReport(temporary.Path, result);
    }

    [Theory]
    [InlineData("reuse")]
    [InlineData("delta")]
    public void InspectorWidensToAFullBuildWhenSeedMergeFails(string mode)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var (result, calls) = RunPlannedInspector(temporary.Path, mode, "merge");

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var builds = calls.Where(static call => call[0] == "build").ToArray();
        Assert.Equal(mode == "delta" ? 2 : 1, builds.Length);
        if (mode == "delta") Assert.Equal(new[] { "build", "+D5.Probe" }, builds[0]);
        Assert.Equal(new[] { "build" }, builds[^1]);
        Assert.Contains("Trureturing", calls.Last(static call => call[0] == "inspect"));
        Assert.Contains("LEAN_REPORT_DELTA mode=full-fallback", Encoding.UTF8.GetString(result.StandardOutput));
    }

    [Fact]
    public void InspectorRejectsAFullFallbackBuildFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var (result, calls) = RunPlannedInspector(temporary.Path, "fallback", "build", alwaysFail: true);

        Assert.Equal(17, result.ExitCode);
        Assert.Equal(new[] { "runtime-prefix", "plan", "utility-input-build", "utility-input", "build" },
            calls.Select(static call => call[0]));
        AssertNoReport(temporary.Path, result);
    }

    [Fact]
    public void ValidReportSeedSkipsBuildAndReinspection() =>
        LeanSeedProcessContract.Run("InspectorTests.test_inspector_reuses_validated_seed_without_build_or_reinspection");

    [Fact]
    public void LakeAndInspectorFailuresKeepTheirRealExitCodes() =>
        LeanSeedProcessContract.Run("InspectorTests.test_inspector_real_failure_blocks_even_when_report_seed_exists");

    [Fact]
    public void DeltaReinspectionPreservesDependencyAndMaterialContracts() => LeanSeedProcessContract.Run("DeltaTests");

    [Theory]
    [InlineData("test_registration_evidence_survives_incremental_reuse")]
    [InlineData("test_malformed_registration_evidence_is_not_a_reuse_seed")]
    [InlineData("test_unknown_module_fields_are_not_a_reuse_seed")]
    public void InformationRegistrationEvidenceMatchesIncrementalReportContract(string behavior) =>
        LeanSeedProcessContract.Run("RegistrationEvidenceTests." + behavior);

    [Fact]
    public void ReportStagingDoesNotPreemptColdCacheProvisioning() =>
        LeanSeedProcessContract.Run("InspectorTests.test_report_staging_does_not_preempt_cold_cache_provisioning");

    [Fact]
    public void ColdInspectorRestoresReleaseBeforeLakeInitializesConfig() =>
        LeanSeedProcessContract.Run("InspectorTests.test_cold_inspector_restores_release_before_lake_initializes_config");

    [Fact]
    public void DeclaredRuntimeDependenciesInvalidateModuleResults() =>
        LeanSeedProcessContract.Run("InspectorTests.test_declared_runtime_material_change_reinspects_inside_same_partition");

    [Theory]
    [InlineData("standalone", 0)]
    [InlineData("prebuilt", 0)]
    [InlineData("missing-prebuilt", 2)]
    public void InspectorDefaultsToCompleteModuleEnumeration(string cliMode, int expectedExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var repository = CreateRepository(temporary.Path);
        var lake = Path.Combine(temporary.Path, "runtime/bin/lean");
        Directory.CreateDirectory(Path.GetDirectoryName(lake)!);
        File.WriteAllText(lake, "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >> \"$STUB_LOG\"\nif [[ \"$*\" == \"--print-prefix\" ]]; then dirname \"$(dirname \"$0\")\"; exit 0; fi\nif [[ \"$*\" == *' --output '* ]]; then while [[ $# -gt 0 ]]; do [[ $1 == --output ]] && { printf '{\"modules\": [], \"schema\": \"stratalint-lean-inspector-spool-v1\"}\\n' > \"$2\"; break; }; shift; done; fi\n", new UTF8Encoding(false));
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var log = Path.Combine(temporary.Path, "lake.log");
        var output = Path.Combine(temporary.Path, "report.json");
        var cli = Path.Combine(repository, "tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll");
        if (cliMode == "prebuilt")
        {
            var build = Run("dotnet", ["build", "tools/StrataLint.Lean/StrataLint.Lean.csproj", "--configuration", "Release"], repository);
            Assert.True(build.ExitCode == 0, Encoding.UTF8.GetString(build.StandardOutput) + Encoding.UTF8.GetString(build.StandardError));
            File.WriteAllText(Path.Combine(repository, "tools/StrataLint.Lean/Fixture.cs"), "invalid source forbids a repeated build");
        }

        var full = Run("env", [$"LAKE_BIN={lake}", $"LEAN_BIN={lake}", $"STUB_LOG={log}",
            $"STRATALINT_LEAN_PRODUCER_DLL={(cliMode == "standalone" ? "" : cli)}",
            Path.Combine(repository, InspectorScript), "--repository", repository, "--output", output], repository);
        Assert.True(full.ExitCode == expectedExit, Encoding.UTF8.GetString(full.StandardError));
        if (expectedExit != 0)
        {
            Assert.Contains("candidate producer is absent", Encoding.UTF8.GetString(full.StandardError), StringComparison.Ordinal);
            Assert.False(File.Exists(output));
            return;
        }
        Assert.Equal("[]", File.ReadAllText(output + ".logs/utility-input.stdout.log").Trim());
        var fullInspect = File.ReadAllLines(log).Single(static line => line.Contains(" --output ", StringComparison.Ordinal));
        Assert.Contains("Trureturing Trureturing.lean sha256:", fullInspect, StringComparison.Ordinal);
        Assert.Contains("D5.Probe D5/Probe.lean sha256:", fullInspect, StringComparison.Ordinal);
    }


    [Theory]
    [InlineData(false, null)]
    [InlineData(true, null)]
    [InlineData(false, "compatibility_version = 0\n")]
    [InlineData(true, "compatibility_version = \"1\"\n")]
    public void InspectorRejectsInvalidVersionBeforeBuildEvenWithPrecomputedIdentity(bool precomputed, string? version)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var repository = CreateRepository(temporary.Path);
        var manifest = Path.Combine(repository, LeanReportInputScriptTests.CompatibilityPath);
        if (version is null) File.Delete(manifest);
        else File.WriteAllText(manifest, version + LeanReportInputScriptTests.SourcePatterns);

        var result = RunInspector(temporary.Path, repository, "", precomputed);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("compatibility_version", Encoding.UTF8.GetString(result.StandardError));
        AssertNoReport(temporary.Path, result);
        Assert.False(File.Exists(Path.Combine(temporary.Path, "lake.log")), "invalid version reached the build/cache producer");
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("extra")]
    [InlineData("non-hex")]
    [InlineData("multiline")]
    public void InspectorRejectsMalformedAddressBeforeProducingReport(string malformed)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var repository = CreateRepository(temporary.Path);
        var digest = new string('a', 64);
        var output = malformed switch
        {
            "missing" => $"{digest}  {digest} {digest}",
            "extra" => string.Join(' ', Enumerable.Repeat(digest, 5)),
            "non-hex" => $"{digest} {new string('z', 64)} {digest} {digest}",
            "multiline" => string.Join(' ', Enumerable.Repeat(digest, 4)) + "\nextra",
            _ => throw new InvalidOperationException(malformed),
        };
        Write(repository, InputScript,
            $"#!/usr/bin/env bash\nif [[ $1 == compatibility-token ]]; then printf '%s\\n' '{digest}'; "
            + "elif [[ $1 == modules ]]; then printf 'Trureturing\\tTrureturing.lean\\n'; "
            + $"else printf '%s\\n' '{output}'; fi\n");

        var result = RunInspector(temporary.Path, repository, "");

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("repository input address is malformed", Encoding.UTF8.GetString(result.StandardError));
        Assert.False(File.Exists(Path.Combine(temporary.Path, "lake.log")));
        AssertNoReport(temporary.Path, result);
    }

    private static ProcessOutput RunInspector(string temporary, string repository, string bin, bool precomputed = false)
    {
        if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
        var lake = Path.Combine(temporary, "lake");
        File.WriteAllText(lake, """
            #!/usr/bin/env bash
            printf '%s\n' "$*" >> "$STUB_LOG"
            while [[ $# -gt 0 ]]; do
              if [[ "$1" == --output ]]; then
                printf '%s\n' '{"modules":[],"schema":"stratalint-lean-inspector-spool-v1"}' > "$2"
                break
              fi
              shift
            done
            """ + "\n");
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        return Run("/bin/bash", ["-c",
            (precomputed ? "export STRATALINT_REPORT_INPUT_ADDRESS=$7 STRATALINT_REPORT_REPOSITORY_SHA256=$7 "
                + "STRATALINT_REPORT_PRODUCER_SHA256=$7 STRATALINT_REPORT_RESIDENT_SHA256=$7 STRATALINT_REPORT_CONFIG_SHA256=$7; " : "")
            + "PATH=\"$1:$PATH\" LAKE_BIN=\"$2\" LEAN_BIN=\"$2\" STUB_LOG=\"$3\" exec \"$4\" --repository \"$5\" --output \"$6\"",
            "inspect-failure", bin, lake, Path.Combine(temporary, "lake.log"),
            Path.Combine(repository, InspectorScript), repository, Path.Combine(temporary, "report.json"), new string('a', 64)], repository);
    }

    private static void AssertNoReport(string temporary, ProcessOutput result)
    {
        Assert.DoesNotContain("RAW_LEAN_REPORT", Encoding.UTF8.GetString(result.StandardOutput));
        foreach (var suffix in new[] { "", ".sha256", ".materials.zip" })
            Assert.False(File.Exists(Path.Combine(temporary, "report.json") + suffix));

    }

    private static ProcessOutput Run(string command, IReadOnlyList<string> arguments, string cwd) =>
        TestProcessRunner.Run(command, arguments, cwd, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);

    // Run the real shell controller. Seed validation and material semantics use
    // the separate real planner/merger fixtures; these stubs expose phase order.
    private static (ProcessOutput Result, string[][] Calls) RunPlannedInspector(
        string temporary, string mode, string failedPhase = "", bool alwaysFail = false, bool prebuilt = false,
        bool relativeCacheRoot = false)
    {
        if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
        var repository = CreateRepository(Path.Combine(temporary, "path with spaces"));
        var bin = Path.Combine(temporary, "stub bin");
        var lake = Path.Combine(repository, "runtime/bin/lean");
        var cache = Path.Combine(temporary, "cache store");
        Directory.CreateDirectory(cache);
        File.SetUnixFileMode(cache, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var partition = Run("/bin/bash", [Path.Combine(repository, "tools/scripts/worktree/lean-cache-input.sh"),
            "partition-path", "--repository", repository], repository);
        Assert.True(partition.ExitCode == 0, Encoding.UTF8.GetString(partition.StandardError));
        var baseline = Path.Combine(cache, Encoding.UTF8.GetString(partition.StandardOutput).Trim(), "baseline.json");
        Directory.CreateDirectory(Path.GetDirectoryName(baseline)!);
        File.WriteAllText(baseline, "baseline");
        File.WriteAllText(baseline + ".materials.zip", "baseline-materials");
        var events = Path.Combine(temporary, "events.jsonl");
        const string producer = """
            #!/usr/bin/env python3
            import hashlib, json, os, pathlib, shutil, sys
            args = sys.argv[1:]
            name = pathlib.Path(sys.argv[0]).name
            if name == 'lean':
                phase = 'cache-bootstrap' if args == ['--version'] else 'runtime-prefix' if '--print-prefix' in args else 'build' if args[0] == 'build' else 'inspect'
            elif name == 'dotnet':
                phase = 'utility-input-build' if args[0] == 'build' else 'utility-input'
            else:
                phase = args[0]
            with open(os.environ['STUB_EVENTS'], 'a') as stream:
                stream.write(json.dumps([phase] + (args[1:] if phase == 'build' else args)) + '\n')
            marker = pathlib.Path(os.environ['STUB_EVENTS'] + '.failed')
            if phase == os.environ['STUB_FAILURE'] and (os.environ['STUB_ALWAYS_FAIL'] == '1' or not marker.exists()):
                marker.touch()
                sys.exit(17)
            if phase == 'runtime-prefix':
                print(pathlib.Path(__file__).parent.parent)
            elif phase == 'plan':
                mode = os.environ['STUB_PLAN']
                selected = ['D5.Probe', 'Trureturing'] if mode == 'delta-all' else ['D5.Probe'] if mode == 'delta' else []
                # Positional output precedes the registered runtime/partition options.
                pathlib.Path(args[8]).write_text(json.dumps({'status': 'delta' if mode.startswith('delta') or mode == 'removal-only' else mode,
                    'baseline': str(pathlib.Path(args[2]) / 'baseline.json'), 'baseline_report_sha256': hashlib.sha256(b'baseline').hexdigest(), 'recheck': selected,
                    'changed': [], 'added': [], 'removed': ['D5.Removed'] if mode == 'removal-only' else []}))
            elif phase == 'inspect':
                pathlib.Path(args[args.index('--output') + 1]).write_text('{"modules": []}')
            elif phase == 'compact':
                shutil.copyfile(args[1], args[3])
                pathlib.Path(args[3] + '.materials.zip').write_text('new-materials')
            elif phase == 'merge':
                plan = json.loads(pathlib.Path(args[1]).read_text())
                baseline = pathlib.Path(plan['baseline'])
                baseline_report = baseline.read_text()
                baseline_materials = pathlib.Path(str(baseline) + '.materials.zip').read_text()
                if os.environ['STUB_PLAN'] == 'removal-only':
                    pathlib.Path(args[3]).write_text(baseline_report.replace('baseline', 'merged'))
                    pathlib.Path(args[3] + '.materials.zip').write_text(baseline_materials.replace('baseline', 'merged'))
                else:
                    source = args[2] if plan['recheck'] else plan['baseline']
                    shutil.copyfile(source, args[3])
                    shutil.copyfile(source + '.materials.zip', args[3] + '.materials.zip')
                print('fixture merge stdout')
                print('fixture merge stderr', file=sys.stderr)
            elif phase == 'utility-input':
                print('[]')
            """;
        foreach (var path in new[] { lake, Path.Combine(bin, "dotnet"),
                     Path.Combine(repository, "tools/lean-inspector/delta.py"), Path.Combine(repository, MaterialCompactor) })
        {
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, producer + "\n");
            File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }
        var cli = Path.Combine(repository, "tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll");
        if (prebuilt)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(cli)!);
            File.WriteAllText(cli, "candidate fixture producer");
        }
        var result = Run("/bin/bash", ["--noprofile", "--norc", "-c",
            "export PATH=\"$1:$PATH\"; shift; exec env \"$@\"", "inspector-fixture", bin,
            $"LAKE_BIN={lake}", $"LEAN_BIN={lake}",
            $"STRATALINT_REPORT_CACHE_ROOT={(relativeCacheRoot ? Path.GetRelativePath(temporary, cache) : cache)}",
            $"STRATALINT_LEAN_PRODUCER_DLL={(prebuilt ? cli : "")}",
            $"STUB_EVENTS={events}", $"STUB_PLAN={mode}", $"STUB_FAILURE={failedPhase}",
            $"STUB_ALWAYS_FAIL={(alwaysFail ? "1" : "0")}",
            "/bin/bash", "--noprofile", "--norc", Path.Combine(repository, InspectorScript),
            "--repository", repository, "--output", Path.Combine(temporary, "report.json")], temporary);
        return (result, File.Exists(events)
            ? File.ReadAllLines(events).Select(static line => JsonSerializer.Deserialize<string[]>(line)!).ToArray()
            : []);
    }

    private static string CreateRepository(string temporary)
    {
        var repository = Path.Combine(temporary, "repo");
        var root = TestRepositoryLayout.FindRoot();
        Write(repository, "Trureturing.lean", "import D5.Probe\n");
        Write(repository, "D5/Probe.lean", "def probe : Nat := 1\n");
        LeanReportInputScriptTests.InstallReportConfiguration(repository);
        foreach (var relative in new[]
            { InspectorScript, InspectorSource, MaterialCompactor, InputScript, ResourceObservationLibrary,
                "tools/scripts/worktree/lean-cache-input.sh", "tools/scripts/worktree/lean_cache.py",
                "tools/scripts/report/producer_paths.py", "tools/scripts/report/dotnet_producer.py",
                "tools/lean-inspector/delta.py", "tools/lean-inspector/runtime_identity.py", "tools/lean-inspector/preparation.py",
                "tools/lean-inspector/report_cache.py" })
        {
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(repository, relative))!);
            File.Copy(Path.Combine(root, relative), Path.Combine(repository, relative));
        }
        InstallCacheRun(repository);
        InstallProducerInputs(repository);
        return repository;
    }

    private static void InstallProducerInputs(string repository)
    {
        Write(repository, "global.json", File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "global.json")));
        string[] projects = ["StrataLint.Lean", "StrataLint.Engine", "Trureturing.Truth"];
        foreach (var project in projects)
        {
            Write(repository, $"tools/{project}/{project}.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(repository, $"tools/{project}/Fixture.cs", "// fixture\n");
        }
        Write(repository, "tools/StrataLint.Lean/StrataLint.Lean.csproj",
            "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><OutputType>Exe</OutputType>"
            + "<TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>\n");
        Write(repository, "tools/StrataLint.Lean/Fixture.cs", "System.Console.WriteLine(\"[]\");\n");
        Write(repository, "tools/scripts/lean-report-pair.sh", "#!/usr/bin/env bash\n");
        Write(repository, "tools/scripts/worktree/lean-cache-publish.sh", "#!/usr/bin/env bash\n");
        Write(repository, "tools/scripts/workflow/scribe-content-checks.sh", "#!/usr/bin/env bash\n");
        Write(repository, "lean-toolchain", "leanprover/lean4:v4.31.0\n");
        Write(repository, "lakefile.toml", "name = \"Fixture\"\n");
        Write(repository, "lake-manifest.json",
            "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789abcdef0123456789abcdef01234567\"}]}\n");
        Write(repository, "Meta/engineering-projects.json", JsonSerializer.Serialize(new
        {
            version = 1, projects = projects.Select(name => new
            {
                path = $"tools/{name}/{name}.csproj", assembly = name, role = "test-support", ci = false,
                include = new[] { $"tools/{name}/Fixture.cs" }, exclude = Array.Empty<string>(),
                references = Array.Empty<string>(), owner = (object?)null, owned_test_assembly = (string?)null,
                test_partition = (string?)null,
                build_inputs = new[] { "global.json" }, execution_inputs = (string[]?)null,
                execution_excludes = (string[]?)null, execution_environment = (string[]?)null,
                root_namespace = "Fixture", namespace_exclude = Array.Empty<string>(), global_namespace_exceptions = Array.Empty<string>(),
            }), historical_projects = Array.Empty<object>(), rule_build_inputs = Array.Empty<string>(),
        }));
        Write(repository, "Meta/ReportProducers/lean-report.json", JsonSerializer.Serialize(new
        {
            schema = "report-producer-scope-v1", runtime = new { lean = new[] { "bin/lean" }, python = new[] { "executable" } }, projects = new[] { "tools/StrataLint.Lean/StrataLint.Lean.csproj" },
            materials = new[] { "global.json" }, scripts = new[]
            {
                InspectorScript, InspectorSource, MaterialCompactor, InputScript, ResourceObservationLibrary, CacheRunScript,
                "tools/scripts/worktree/lean-cache-input.sh", "tools/scripts/worktree/lean_cache.py",
                "tools/scripts/report/producer_paths.py", "tools/scripts/report/dotnet_producer.py",
                "tools/lean-inspector/delta.py", "tools/lean-inspector/runtime_identity.py", "tools/lean-inspector/preparation.py", "tools/lean-inspector/report_cache.py",
            },
        }));
        Write(repository, ".gitignore", "**/bin/\n**/obj/\n**/__pycache__/\n");
        Assert.Equal(0, Run("git", ["init", "--quiet"], repository).ExitCode);
        Assert.Equal(0, Run("git", ["add", "."], repository).ExitCode);
    }

    private static void AssertSuccessfulPhaseLogs(
        string directory, string phase, string command, string stdout, string stderr)
    {
        foreach (var sidecar in new[] { "command", "stdout", "stderr", "exit" })
            Assert.True(File.Exists(Path.Combine(directory, $"{phase}.{sidecar}.log")),
                $"missing phase log: {phase}.{sidecar}.log");
        Assert.Contains("cwd=", FixtureFile.ReadAllText(Path.Combine(directory, phase + ".command.log")));
        Assert.Contains(command, FixtureFile.ReadAllText(Path.Combine(directory, phase + ".command.log")));
        Assert.Equal(stdout, FixtureFile.ReadAllText(Path.Combine(directory, phase + ".stdout.log")));
        Assert.Equal(stderr, FixtureFile.ReadAllText(Path.Combine(directory, phase + ".stderr.log")));
        Assert.Equal("0\n", FixtureFile.ReadAllText(Path.Combine(directory, phase + ".exit.log")));
    }

    private static void Write(string root, string relative, string contents)
    {
        var path = Path.Combine(root, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, contents, new UTF8Encoding(false));
    }

    private static void InstallCacheRun(string repository)
    {
        if (OperatingSystem.IsWindows()) return;
        Write(repository, CacheRunScript, "#!/usr/bin/env bash\nexec \"$@\"\n");
        File.SetUnixFileMode(
            Path.Combine(repository, CacheRunScript),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
