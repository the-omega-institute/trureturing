using System.Text;
using System.Runtime.Versioning;
using StrataLint.Engine;

namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/workflow/scribe-content-checks.sh")]
public sealed class ScribeContentChecksScriptTests
{
    private const string ScribeContentChecksScriptPath =
        "tools/scripts/workflow/scribe-content-checks.sh";
    [Fact]
    public void ScribeContentChecksUseTheExplicitNonEmptyReport()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertScribeContentChecksSubjectExists();

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var explicitReport = Path.Combine(fixture.Path, "explicit-report.json");
        var ambientReport = Path.Combine(fixture.Path, "ambient-report.json");
        var scribe = Path.Combine(fixture.Path, "StrataLint.Scribe.dll");
        var log = Path.Combine(fixture.Path, "scribe.log");
        Directory.CreateDirectory(binDirectory);
        File.WriteAllText(explicitReport, "explicit\n");
        File.WriteAllText(ambientReport, "ambient\n");
        File.WriteAllText(scribe, "fixture\n");
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            "#!/usr/bin/env bash\nprintf '%s|%s\\n' \"$STRATALINT_LEAN_REPORT\" \"$*\" >> \"$SCRIBE_LOG\"");
        var headResult = TestProcessRunner.Run(
            "git",
            ["rev-parse", "HEAD"],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
        Assert.Equal(0, headResult.ExitCode);
        var baseRevision = Encoding.UTF8.GetString(headResult.StandardOutput).Trim();
        WriteExecutable(
            Path.Combine(binDirectory, "git"),
            $$"""
            #!/usr/bin/env bash
            if [[ "${1:-}" == -C ]]; then shift 2; fi
            case "$*" in
              "cat-file -e {{baseRevision}}^{commit}"|"ls-files --others --exclude-standard -z") exit 0 ;;
              "diff --name-only --no-renames -z {{baseRevision}} --") printf 'Blueprint/D5/Probe.scribe.cs\0' ;;
              *) echo "unexpected git invocation: $*" >&2; exit 90 ;;
            esac
            """);

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:/usr/bin:/bin\" STRATALINT_LEAN_REPORT=\"$2\" SCRIBE_LOG=\"$3\" "
                    + "exec /bin/bash \"$4\" \"$5\" \"$6\" \"$7\"",
                "scribe-content-checks",
                binDirectory,
                ambientReport,
                log,
                Path.Combine(root, ScribeContentChecksScriptPath),
                explicitReport,
                scribe,
                baseRevision,
            ],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.True(
            result.ExitCode == 0,
            $"expected exit 0, actual {result.ExitCode}\nstdout:\n{Encoding.UTF8.GetString(result.StandardOutput)}\nstderr:\n{Encoding.UTF8.GetString(result.StandardError)}");
        var invocations = File.ReadAllLines(log);
        Assert.Equal(2, invocations.Length);
        Assert.All(invocations, line => Assert.StartsWith(explicitReport + "|", line, StringComparison.Ordinal));
        Assert.DoesNotContain(invocations, line => line.Contains(ambientReport, StringComparison.Ordinal));
        Assert.Contains(
            invocations,
            static line => line.EndsWith(" describe-report --check", StringComparison.Ordinal));
        Assert.Contains(
            invocations,
            line => line.EndsWith(
                $" markdown-check --report {explicitReport} --paths-from -",
                StringComparison.Ordinal));
    }

    [Fact]
    public void ScribeContentChecksRejectMissingAndEmptyReportsBeforeRunningScribe()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertScribeContentChecksSubjectExists();

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var emptyReport = Path.Combine(fixture.Path, "empty-report.json");
        var missingReport = Path.Combine(fixture.Path, "missing-report.json");
        var scribe = Path.Combine(fixture.Path, "StrataLint.Scribe.dll");
        Directory.CreateDirectory(binDirectory);
        File.WriteAllText(emptyReport, string.Empty);
        File.WriteAllText(scribe, "fixture\n");
        WriteExecutable(Path.Combine(binDirectory, "dotnet"), "#!/usr/bin/env bash\nexit 0");

        foreach (var report in new[] { emptyReport, missingReport })
        {
            var result = TestProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "PATH=\"$1:/usr/bin:/bin\" exec /bin/bash \"$2\" \"$3\" \"$4\"",
                    "scribe-content-checks-invalid-report",
                    binDirectory,
                    Path.Combine(root, ScribeContentChecksScriptPath),
                    report,
                    scribe,
                ],
                root,
                BoundedProcessRunner.HangDetectionBudget,
                64 * 1024);

            Assert.NotEqual(0, result.ExitCode);
        }
    }

    private static void AssertScribeContentChecksSubjectExists() =>
        Assert.NotEmpty(TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/workflow/scribe-content-checks.sh")));

    [UnsupportedOSPlatform("windows")]
    private static void WriteExecutable(string path, string content)
    {
        File.WriteAllText(path, content + "\n");
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }

    [Fact]
    [UnsupportedOSPlatform("windows")]
    public void ScribeCoarseGateSkipsEmissionProcessesForAnUnrelatedDelta()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ScribeCoarseGateFixture();
        fixture.Change("docs/develop/notes.md");

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(fixture.Invocations());
    }

    [Fact]
    [UnsupportedOSPlatform("windows")]
    public void ScribeCoarseGateSkipsEmissionProcessesForTheHardcodeLedger()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ScribeCoarseGateFixture();
        fixture.Change("tools/Architecture/HARDCODE-LEDGER.md");

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(fixture.Invocations());
    }

    [Fact]
    [UnsupportedOSPlatform("windows")]
    public void ScribeCoarseGateSkipsEmissionProcessesForAnEmptyDelta()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ScribeCoarseGateFixture();

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(fixture.Invocations());
    }

    [Theory]
    [InlineData("D5/Probe.lean")]
    [InlineData("Trureturing.lean")]
    [InlineData("lean-toolchain")]
    [InlineData("lake-manifest.json")]
    [InlineData("lakefile.toml")]
    [InlineData("Library/notes/probe.md")]
    [InlineData("Meta/Digestion/backfill/probe.yaml")]
    [InlineData("Problems/probe.md")]
    [UnsupportedOSPlatform("windows")]
    public void R15DescribeReportRunsForAuthoritativeInputDelta(string changedPath)
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ScribeCoarseGateFixture();
        fixture.Change(changedPath);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            [
                $"{fixture.ScribeDll} describe-report --check",
            ],
            fixture.Invocations());
    }

    [Fact]
    [UnsupportedOSPlatform("windows")]
    public void R15StatementProjectionReplayRunsForGoldenFixtureDelta()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ScribeCoarseGateFixture();
        fixture.Change("Golden/Projection/statement-projection-pilot-v1.json");

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            [$"{fixture.ScribeDll} projections --check --report {fixture.Report}"],
            fixture.Invocations());
    }

    [Theory]
    [InlineData("Golden/values-kernels.toml")]
    [InlineData("Evidence/D5/values.json")]
    [InlineData("notes/r15-unrelated.txt")]
    [UnsupportedOSPlatform("windows")]
    public void R15ProjectionFreshnessDoesNotEnterTheContentGate(string changedPath)
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ScribeCoarseGateFixture();
        fixture.Change(changedPath);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(fixture.Invocations());
    }

    [Fact]
    [UnsupportedOSPlatform("windows")]
    public void MarkdownFormulaGateRunsForABlueprintProjectionDelta()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ScribeCoarseGateFixture();
        fixture.Change("Blueprint/D5/Probe.md");

        var result = fixture.Run();

        // Freshness still does not enter the gate; the formulas the projection carries do,
        // and nothing else about a markdown-only delta does.
        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            [$"{fixture.ScribeDll} markdown-check --report {fixture.Report} --paths-from -"],
            fixture.Invocations());
    }

    [Fact]
    [UnsupportedOSPlatform("windows")]
    public void BlueprintSourceDeltaRunsDescribeAndTheMarkdownFormulaGate()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ScribeCoarseGateFixture();
        fixture.Change("Blueprint/D5/Probe.scribe.cs");

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            [
                $"{fixture.ScribeDll} describe-report --check",
                $"{fixture.ScribeDll} markdown-check --report {fixture.Report} --paths-from -",
            ],
            fixture.Invocations());
    }

    [Fact]
    [UnsupportedOSPlatform("windows")]
    public void ScribeCoarseGateUsesTheDerivedProducerClosure()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ScribeCoarseGateFixture();
        fixture.Change(ScribeCoarseGateFixture.DerivedProducerPath);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.DoesNotContain(
            fixture.Invocations(),
            invocation => invocation == $"{fixture.ScribeDll} emit --check");
        Assert.Equal(
            [
                $"{fixture.ScribeDll} projections --check --report {fixture.Report}",
                $"{fixture.ScribeDll} describe-report --check",
            ],
            fixture.Invocations());
    }

    [Theory]
    [InlineData("HEAD")]
    [InlineData("0000000000000000000000000000000000000000")]
    [UnsupportedOSPlatform("windows")]
    public void ScribeCoarseGateRejectsANonExactOrUnavailableBase(string baseRevision)
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new ScribeCoarseGateFixture();

        var result = fixture.Run(baseRevision);

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(fixture.Invocations());
    }

    [UnsupportedOSPlatform("windows")]
    private sealed class ScribeCoarseGateFixture : IDisposable
    {
        internal const string DerivedProducerPath = "tools/custom/DerivedProducer.cs";

        private readonly TemporaryDirectory temporary = new();
        private readonly string binDirectory;
        private readonly string log;
        private readonly string script;
        private readonly string baseRevision;

        internal ScribeCoarseGateFixture()
        {
            Repository = Path.Combine(temporary.Path, "repository");
            binDirectory = Path.Combine(temporary.Path, "bin");
            log = Path.Combine(temporary.Path, "scribe.log");
            Report = Path.Combine(temporary.Path, "report.json");
            ScribeDll = Path.Combine(temporary.Path, "StrataLint.Scribe.dll");
            script = Path.Combine(
                Repository,
                "tools",
                "scripts",
                "workflow",
                "scribe-content-checks.sh");
            Directory.CreateDirectory(Path.GetDirectoryName(script)!);
            Directory.CreateDirectory(binDirectory);
            Directory.CreateDirectory(Path.Combine(Repository, "Blueprint"));
            File.WriteAllText(Report, "report\n", new UTF8Encoding(false));
            File.WriteAllText(ScribeDll, "fixture\n", new UTF8Encoding(false));

            var root = TestRepositoryLayout.FindRoot();
            File.Copy(
                Path.Combine(root, ScribeContentChecksScriptPath),
                script);
            File.SetUnixFileMode(
                script,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

            var inputHelper = Path.Combine(
                Repository,
                "tools",
                "scripts",
                "report",
                "lean-report-input.sh");
            Directory.CreateDirectory(Path.GetDirectoryName(inputHelper)!);
            WriteExecutable(
                inputHelper,
                $"#!/usr/bin/env bash\n[[ \"${{1:-}}\" == scribe-producer-paths ]] || exit 2\nprintf '%s\\n' '{DerivedProducerPath}'\n");
            WriteExecutable(
                Path.Combine(binDirectory, "dotnet"),
                "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >> \"$SCRIBE_LOG\"\n");
            File.WriteAllText(
                Path.Combine(Repository, "global.json"),
                "{}\n",
                new UTF8Encoding(false));

            RunGit(["init", "--quiet"]);
            RunGit(["add", "."]);
            RunGit(
                [
                    "-c", "user.name=Scribe Test",
                    "-c", "user.email=scribe@example.invalid",
                    "commit", "--quiet", "-m", "base",
                ]);
            baseRevision = RunGit(["rev-parse", "HEAD"]);
        }

        internal string Repository { get; }

        internal string Report { get; }

        internal string ScribeDll { get; }

        internal void Change(string relativePath)
        {
            var path = Path.Combine(
                Repository,
                relativePath.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.AppendAllText(path, "changed\n", new UTF8Encoding(false));
        }

        internal ProcessOutput Run(string? baseRevisionOverride = null) => TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:/usr/bin:/bin\" SCRIBE_LOG=\"$2\" "
                    + "exec /bin/bash \"$3\" \"$4\" \"$5\" \"$6\"",
                "scribe-coarse-gate",
                binDirectory,
                log,
                script,
                Report,
                ScribeDll,
                baseRevisionOverride ?? baseRevision,
            ],
            Repository,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        internal string[] Invocations() => File.Exists(log) ? File.ReadAllLines(log) : [];

        public void Dispose() => temporary.Dispose();

        private string RunGit(IReadOnlyList<string> arguments)
        {
            var result = TestProcessRunner.Run(
                "git",
                arguments,
                Repository,
                BoundedProcessRunner.HangDetectionBudget,
                64 * 1024);
            Assert.Equal(0, result.ExitCode);
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }
    }
}
