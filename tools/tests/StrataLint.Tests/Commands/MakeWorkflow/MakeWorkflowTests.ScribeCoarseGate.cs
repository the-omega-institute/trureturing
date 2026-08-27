using System.Text;
using System.Runtime.Versioning;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
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
    [InlineData("Blueprint/D5/Probe.scribe.cs")]
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
    [InlineData("Blueprint/D5/Probe.md")]
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
