using FixtureFile = StrataLint.TestSupport.TemporaryFileSystem.File;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean report environment")]
public sealed class LeanInspectorScriptTests
{
    private const string InspectorScript = "tools/lean-inspector/inspect.sh";
    private const string InspectorSource = "tools/lean-inspector/Inspector.lean";
    private const string MaterialCompactor = "tools/lean-inspector/materials.py";
    private const string InputScript = "tools/scripts/report/lean-report-input.sh";
    private const string ResourceObservationLibrary = "tools/scripts/lib/resource-observation-lib.sh";
    private const string CacheRunScript = "tools/scripts/worktree/lean-cache-run.sh";

    [Theory]
    [InlineData("reuse")]
    [InlineData("delta")]
    [InlineData("fallback")]
    public void InspectorExecutesThePlannedBuildScope(string mode)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var (result, calls) = RunPlannedInspector(temporary.Path, mode);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal("plan", calls[0][0]);
        var builds = calls.Where(static call => call[0] == "build").ToArray();
        var inspections = calls.Where(static call => call[0] == "inspect").ToArray();
        if (mode == "reuse")
        {
            Assert.Single(calls);
            Assert.Equal("baseline", File.ReadAllText(Path.Combine(temporary.Path, "report.json")));
            Assert.Equal("baseline-materials", File.ReadAllText(Path.Combine(temporary.Path, "report.json.materials.zip")));
        }
        else
        {
            Assert.Equal(mode == "delta" ? ["build", "+D5.Probe"] : new[] { "build" }, Assert.Single(builds));
            var inspection = Assert.Single(inspections);
            Assert.Contains("D5.Probe", inspection);
            Assert.Equal(mode == "fallback", inspection.Contains("Trureturing", StringComparer.Ordinal));
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
        var reuse = mode == "reuse";
        Assert.Equal(reuse ? new[] { "plan" } : new[] { "plan", "merge" },
            calls.Select(static call => call[0]));
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

        var logDirectory = output + ".logs";
        if (reuse)
        {
            AssertSuccessfulPhaseLogs(logDirectory, "reuse-report", "argv= cp ", "", "");
            AssertSuccessfulPhaseLogs(logDirectory, "reuse-materials", "argv= cp ", "", "");
            Assert.Contains("baseline.json ", FixtureFile.ReadAllText(Path.Combine(logDirectory, "reuse-report.command.log")));
            Assert.Contains("baseline.json.materials.zip ", FixtureFile.ReadAllText(Path.Combine(logDirectory, "reuse-materials.command.log")));
        }
        else
        {
            AssertSuccessfulPhaseLogs(logDirectory, "delta-merge", "delta.py merge ",
                "fixture merge stdout\n", "fixture merge stderr\n");
        }
        Assert.Equal(reuse ? 8 : 4, Directory.GetFiles(logDirectory).Length);
    }

    [Theory]
    [InlineData("utility-input-build")]
    [InlineData("utility-input")]
    [InlineData("build")]
    [InlineData("inspect")]
    [InlineData("compact")]
    [InlineData("merge")]
    public void InspectorRetriesAWholeBuildAfterADeltaPhaseFails(string failedPhase)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var (result, calls) = RunPlannedInspector(temporary.Path, "delta", failedPhase);

        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        string[] phases = ["plan", "utility-input-build", "utility-input", "build", "inspect", "compact", "merge"];
        var failedIndex = Array.IndexOf(phases, failedPhase);
        Assert.Equal(phases.Take(failedIndex + 1).Concat(["utility-input-build", "utility-input", "build", "inspect", "compact"]),
            calls.Select(static call => call[0]));
        Assert.Equal(new[] { "build" }, calls.Last(static call => call[0] == "build"));
        Assert.Contains("Trureturing", calls.Last(static call => call[0] == "inspect"));
        Assert.Contains("LEAN_REPORT_DELTA mode=full-fallback", Encoding.UTF8.GetString(result.StandardOutput));
    }

    [Fact]
    public void InspectorRejectsWhenBothDeltaAndFullBuildFail()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var (result, calls) = RunPlannedInspector(temporary.Path, "delta", "build", alwaysFail: true);

        Assert.Equal(17, result.ExitCode);
        Assert.Equal(new[] { "plan", "utility-input-build", "utility-input", "build", "utility-input-build", "utility-input", "build" },
            calls.Select(static call => call[0]));
        AssertNoReport(temporary.Path, result);
    }

    [Fact]
    public void InspectorDefaultsToCompleteModuleEnumeration()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var repository = CreateRepository(temporary.Path);
        var lake = Path.Combine(temporary.Path, "lake");
        File.WriteAllText(lake, "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >> \"$STUB_LOG\"\nif [[ \"$*\" == *' --output '* ]]; then while [[ $# -gt 0 ]]; do [[ $1 == --output ]] && { printf '{\"modules\": [], \"schema\": \"stratalint-lean-inspector-spool-v1\"}\\n' > \"$2\"; break; }; shift; done; fi\n", new UTF8Encoding(false));
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var log = Path.Combine(temporary.Path, "lake.log");
        var output = Path.Combine(temporary.Path, "report.json");

        var full = Run("env", [$"LAKE_BIN={lake}", $"STUB_LOG={log}", Path.Combine(repository, InspectorScript), "--repository", repository, "--output", output], repository);
        Assert.True(full.ExitCode == 0, Encoding.UTF8.GetString(full.StandardError));
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

    [Fact]
    public void ProducerDoesNotExecuteCandidateModuleEnumerator()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var repository = Path.Combine(temporary.Path, "repo");
        Directory.CreateDirectory(Path.Combine(repository, "D5"));
        Write(repository, "Trureturing.lean", "import D5.Probe\n");
        Write(repository, "D5/Probe.lean", "def probe : Nat := 1\n");
        var marker = Path.Combine(temporary.Path, "candidate-helper-ran");
        var poisoned = Path.Combine(repository, InputScript);
        Directory.CreateDirectory(Path.GetDirectoryName(poisoned)!);
        File.WriteAllText(
            poisoned,
            $"#!/usr/bin/env bash\ntouch '{marker}'\nprintf 'Trureturing\\tTrureturing.lean\\n'\n",
            new UTF8Encoding(false));
        File.SetUnixFileMode(poisoned, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        InstallCacheRun(repository);
        InstallProducerInputs(repository);
        Assert.Equal(0, Run("git", ["init", "--quiet"], repository).ExitCode);
        var lake = Path.Combine(temporary.Path, "lake");
        File.WriteAllText(lake, "#!/usr/bin/env bash\nif [[ \"$*\" == *' --output '* ]]; then while [[ $# -gt 0 ]]; do [[ $1 == --output ]] && { printf '{\"modules\": [], \"schema\": \"stratalint-lean-inspector-spool-v1\"}\\n' > \"$2\"; break; }; shift; done; fi\n", new UTF8Encoding(false));
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = Run("env", [$"LAKE_BIN={lake}", Path.Combine(root, InspectorScript), "--repository", repository, "--output", Path.Combine(temporary.Path, "report.json")], repository);

        Assert.Equal(0, result.ExitCode);
        Assert.False(File.Exists(marker), "producer executed the candidate-owned module enumerator");
    }

    private static ProcessOutput Run(string command, IReadOnlyList<string> arguments, string cwd) =>
        TestProcessRunner.Run(command, arguments, cwd, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);

    // Execute the real shell controller with deterministic producer boundaries.
    // The planner's own baseline validation and merge semantics have separate tests.
    private static (ProcessOutput Result, string[][] Calls) RunPlannedInspector(
        string temporary, string mode, string failedPhase = "", bool alwaysFail = false,
        bool relativeCacheRoot = false)
    {
        if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
        var repository = CreateRepository(Path.Combine(temporary, "path with spaces"));
        var bin = Path.Combine(temporary, "stub bin");
        var cache = Path.Combine(temporary, "cache store");
        Directory.CreateDirectory(cache);
        File.SetUnixFileMode(cache, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var baseline = Path.Combine(cache, "baseline.json");
        File.WriteAllText(baseline, "baseline");
        File.WriteAllText(baseline + ".materials.zip", "baseline-materials");
        var events = Path.Combine(temporary, "events.jsonl");
        const string producer = """
            #!/usr/bin/env python3
            import json, os, pathlib, shutil, sys
            args = sys.argv[1:]
            name = pathlib.Path(sys.argv[0]).name
            if name == 'lake':
                phase = 'build' if args[0] == 'build' else 'inspect'
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
            if phase == 'plan':
                mode = os.environ['STUB_PLAN']
                pathlib.Path(args[-1]).write_text(json.dumps({'status': 'delta' if mode == 'removal-only' else mode,
                    'baseline': str(pathlib.Path(args[2]) / 'baseline.json'), 'recheck': ['D5.Probe'] if mode == 'delta' else [],
                    'changed': [], 'added': [], 'removed': ['D5.Removed'] if mode == 'removal-only' else []}))
            elif phase == 'inspect':
                pathlib.Path(args[args.index('--output') + 1]).write_text('{"modules": []}')
            elif phase == 'compact':
                shutil.copyfile(args[1], args[3])
                pathlib.Path(args[3] + '.materials.zip').write_text('new-materials')
            elif phase == 'merge':
                baseline = pathlib.Path(json.loads(pathlib.Path(args[1]).read_text())['baseline'])
                baseline_report = baseline.read_text()
                baseline_materials = pathlib.Path(str(baseline) + '.materials.zip').read_text()
                if os.environ['STUB_PLAN'] == 'removal-only':
                    pathlib.Path(args[3]).write_text(baseline_report.replace('baseline', 'merged'))
                    pathlib.Path(args[3] + '.materials.zip').write_text(baseline_materials.replace('baseline', 'merged'))
                else:
                    shutil.copyfile(args[2], args[3])
                    shutil.copyfile(args[2] + '.materials.zip', args[3] + '.materials.zip')
                print('fixture merge stdout')
                print('fixture merge stderr', file=sys.stderr)
            elif phase == 'utility-input':
                print('[]')
            """;
        foreach (var path in new[] { Path.Combine(bin, "lake"), Path.Combine(bin, "dotnet"),
                     Path.Combine(repository, "tools/lean-inspector/delta.py"), Path.Combine(repository, MaterialCompactor) })
        {
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, producer + "\n");
            File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }
        var result = Run("/bin/bash", ["--noprofile", "--norc", "-c",
            "export PATH=\"$1:$PATH\"; shift; exec env \"$@\"", "inspector-fixture", bin,
            $"LAKE_BIN={Path.Combine(bin, "lake")}",
            $"STRATALINT_REPORT_CACHE_ROOT={(relativeCacheRoot ? Path.GetRelativePath(temporary, cache) : cache)}",
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
        foreach (var relative in new[]
            { InspectorScript, InspectorSource, MaterialCompactor, InputScript, ResourceObservationLibrary,
                "tools/scripts/worktree/lean-cache-input.sh" })
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
        LeanReportInputScriptTests.InstallReportConfiguration(repository);
        foreach (var project in new[] { "StrataLint.Cli", "StrataLint.Engine", "Trureturing.Truth" })
        {
            Write(repository, $"tools/{project}/{project}.csproj", "<Project Sdk=\"Microsoft.NET.Sdk\" />\n");
            Write(repository, $"tools/{project}/Fixture.cs", "// fixture\n");
        }
        Write(repository, "tools/StrataLint.Cli/StrataLint.Cli.csproj",
            "<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><OutputType>Exe</OutputType>"
            + "<TargetFramework>net10.0</TargetFramework></PropertyGroup></Project>\n");
        Write(repository, "tools/StrataLint.Cli/Fixture.cs", "System.Console.WriteLine(\"[]\");\n");
        Write(repository, "tools/scripts/lean-report-pair.sh", "#!/usr/bin/env bash\n");
        Write(repository, "tools/scripts/worktree/lean-cache-publish.sh", "#!/usr/bin/env bash\n");
        Write(repository, "tools/scripts/workflow/scribe-content-checks.sh", "#!/usr/bin/env bash\n");
        Write(repository, ".github/workflows/ci.yml",
            "jobs:\n  lean-inspect:\n    steps: []\n  baseline-admission:\n    steps: []\n");
        Write(repository, "lean-toolchain", "leanprover/lean4:v4.31.0\n");
        Write(repository, "lakefile.toml", "name = \"Fixture\"\n");
        Write(repository, "lake-manifest.json", "{\"version\":\"1.1.0\"}\n");
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
            + "PATH=\"$1:$PATH\" LAKE_BIN=\"$2\" STUB_LOG=\"$3\" exec \"$4\" --repository \"$5\" --output \"$6\"",
            "inspect-failure", bin, lake, Path.Combine(temporary, "lake.log"),
            Path.Combine(repository, InspectorScript), repository, Path.Combine(temporary, "report.json"), new string('a', 64)], repository);
    }

    private static void AssertNoReport(string temporary, ProcessOutput result)
    {
        Assert.DoesNotContain("RAW_LEAN_REPORT", Encoding.UTF8.GetString(result.StandardOutput));
        foreach (var suffix in new[] { "", ".sha256", ".materials.zip" })
            Assert.False(File.Exists(Path.Combine(temporary, "report.json") + suffix));

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
