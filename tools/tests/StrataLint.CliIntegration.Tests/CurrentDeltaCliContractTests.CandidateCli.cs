using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using Tomlyn;
using Tomlyn.Model;
using Trureturing.Truth;

namespace StrataLint.CliIntegration.Tests;

public sealed partial class CurrentDeltaCliContractTests
{
    // Each timestamp read advances one second, so every measured stage reaches the reporting threshold.
    private sealed class SecondPerReadTimeProvider : TimeProvider
    {
        private long timestamp;

        public override long TimestampFrequency => 1;

        public override long GetTimestamp() => Interlocked.Increment(ref timestamp);
    }

    // Stage timing is information-level telemetry on stderr; other tests may write there too.
    private static (ExplicitCommandResult Result, string[] Stages) CaptureStageTiming(Func<ExplicitCommandResult> run)
    {
        using var error = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        var original = Console.Error;
        ExplicitCommandResult result;
        try
        {
            Console.SetError(error);
            result = run();
        }
        finally
        {
            Console.SetError(original);
        }
        var stages = new List<string>();
        foreach (var line in error.ToString().Split('\n', StringSplitOptions.RemoveEmptyEntries))
        {
            if (!line.StartsWith('{')) continue;
            using var document = JsonDocument.Parse(line);
            if (document.RootElement.TryGetProperty("event", out var name) && name.GetString() == "gate_stage_timing")
                stages.Add(document.RootElement.GetProperty("stage").GetString()!);
        }
        return (result, stages.ToArray());
    }

    [Theory]
    [InlineData("missing", "raw-lean-report.json")]
    [InlineData("invalid", "Raw Lean report is not valid JSON")]
    [InlineData("stale", "Raw Lean report source hash does not match")]
    public void CommonCurrentRetainsCandidateCheckerReportFailure(string damage, string diagnostic)
    {
        using var ciEnvironment = new CiFixtureEnvironment();
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var fixture = new RuleFixture();
        fixture.Files[CommonExecutionEvidence.CheckManifestPath] =
            CommonCheckRegistrationFixture.Manifest("tools/StrataLint.Scribe/StrataLint.Scribe.csproj");
        fixture.Files["Makefile"] = "lean-report:\n\t@printf 'fixture producer completed\\n'\n";
        fixture.Files[".gitignore"] = ".lake/\nbuild/\ntools/**/bin/\n";
        foreach (var (path, contents) in fixture.Files)
        {
            var full = Path.Combine(root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(full)!);
            File.WriteAllText(full, contents);
        }
        Git(root, "init", "-q");
        Git(root, "add", ".");
        Git(root, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "parentless current");
        var runtime = Path.GetDirectoryName(Path.Combine(root, CommonExecutionEvidence.CliPath))!;
        Directory.CreateDirectory(runtime);
        var binaries = new List<string>();
        foreach (var file in Directory.GetFiles(Path.GetDirectoryName(typeof(StrataLint.Cli.Program).Assembly.Location)!))
        {
            var destination = Path.Combine(runtime, Path.GetFileName(file));
            File.Copy(file, destination);
            binaries.Add(Path.GetRelativePath(root, destination).Replace('\\', '/'));
        }
        // Only Lean production is synthetic; the bound candidate CLI validates
        // the actual report, and the stage must retain that consumer's failure.
        var producer = Path.Combine(root, CommonExecutionEvidence.LeanProducerPath);
        Directory.CreateDirectory(Path.GetDirectoryName(producer)!);
        File.WriteAllText(producer, "synthetic producer binary");
        binaries.Add(CommonExecutionEvidence.LeanProducerPath);
        var report = Path.Combine(root, CommonExecutionEvidence.ReportPath);
        RawLeanReportArtifact.WriteFile(report, CommonExecutionEvidence.Snapshot(root), LeanAxiomReport.Create(fixture.Reports));
        if (damage == "missing") File.Delete(report);
        if (damage == "invalid") File.WriteAllText(report, "not JSON");
        if (damage == "stale") File.AppendAllText(Path.Combine(root, RuleFixture.RingPath), "-- newer source\n");
        const string buildLog = "build/ci/fixture.log";
        Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(root, buildLog))!);
        File.WriteAllText(Path.Combine(root, buildLog), "synthetic build\n");
        CommonExecutionEvidence.SealBuild(root, CommonExecutionEvidence.Candidate(root), binaries.Append(buildLog),
            CommonExecutionEvidence.BuildSteps.Select(name => new StageStep(name, 0, 0, "executed", buildLog)).ToArray());

        using var output = new StringWriter();
        Assert.Equal(2, new CommonStages(root, output).Run("current", null));
        using var summary = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "build/ci/current-result.json")));
        var steps = summary.RootElement.GetProperty("steps").EnumerateArray().ToArray();
        Assert.Equal(new[] { "lean-report", "check-current" }, steps.Select(step => step.GetProperty("name").GetString()));
        Assert.Equal(0, steps[0].GetProperty("exit").GetInt32());
        Assert.Equal(2, steps[1].GetProperty("raw_exit").GetInt32());
        var failure = File.ReadAllText(Path.Combine(root, steps[1].GetProperty("log").GetString()!));
        Assert.Contains("INFRASTRUCTURE_FAILURE", failure, StringComparison.Ordinal);
        Assert.Contains(diagnostic, failure, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.CurrentPath)));
        Assert.False(File.Exists(Path.Combine(root, CommonExecutionEvidence.ChecksPath("current"))));
    }

    [Theory]
    [InlineData("valid", 0, "ADMITTED")]
    [InlineData("invalid-report", 2, "Raw Lean report is not valid JSON")]
    [InlineData("retired-option", 2, "harness-gate: unknown argument '--test-map-cache-root'")]
    public void HarnessGateUsesActualCandidateCheckCli(string scenario, int expectedExit, string diagnostic)
    {
        if (OperatingSystem.IsWindows()) throw new PlatformNotSupportedException();
        using var temporary = new TemporaryDirectory();
        var root = Encoding.UTF8.GetString(RequireSuccess(TestProcessRunner.Run("pwd", ["-P"],
            temporary.Path, TestBudgets.ScriptProcessHangGuard, 4096)).StandardOutput).Trim();
        var repository = TestRepositoryLayout.FindRoot();
        var bin = Path.Combine(root, "bin");
        Directory.CreateDirectory(bin);
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        foreach (var (path, content) in fixture.Files)
        {
            var destination = Path.Combine(root, path);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.WriteAllText(destination, content);
        }
        File.WriteAllText(Path.Combine(root, ".gitignore"), "bin/\n.lake/\ntools/StrataLint.Cli/bin/\n");
        Git("init", "-q");
        Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "base");
        var basis = Encoding.UTF8.GetString(Git("rev-parse", "HEAD").StandardOutput).Trim();
        var report = Path.Combine(root, ".lake/report.json");
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(GitRepositorySnapshotReader.ReadCurrent(root))).Snapshot;
        RawLeanReportArtifact.WriteFile(report, snapshot, LeanAxiomReport.Create(fixture.Reports));
        if (scenario == "invalid-report") File.WriteAllText(report, "not JSON\n");

        var runtime = Path.Combine(root, "tools/StrataLint.Cli/bin/Release/net10.0");
        Directory.CreateDirectory(Path.GetDirectoryName(runtime)!);
        Directory.CreateSymbolicLink(runtime, Path.GetDirectoryName(typeof(StrataLint.Cli.Program).Assembly.Location)!);
        // Reuse the candidate build. The native host calls the actual check consumer;
        // the separate filemap stage retains its process-normalization test boundary.
        WriteExecutable(Path.Combine(bin, "make"), """
            [[ $# == 3 && "$1" == -C && "$2" == "$GATE_TEST_ROOT/tools" && "$3" == dotnet ]]
            test -s "$GATE_TEST_ROOT/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"
            """);
        WriteExecutable(Path.Combine(bin, "dotnet"), """
            [[ "$1" == "$GATE_TEST_ROOT/tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll" ]]
            if [[ $# == 2 && "$2" == filemap-conform ]]; then exit 0; fi
            shift
            exec "$GATE_TEST_DOTNET" "$GATE_TEST_HOST" "$@"
            """);
        var dotnet = Encoding.UTF8.GetString(RequireSuccess(TestProcessRunner.Run("/bin/bash",
            ["-c", "command -v dotnet"], root, TestBudgets.ScriptProcessHangGuard, 4096)).StandardOutput).Trim();
        var arguments = new List<string>
        {
            $"PATH={bin}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
            $"GATE_TEST_ROOT={root}", $"GATE_TEST_DOTNET={dotnet}",
            $"GATE_TEST_HOST={typeof(CurrentDeltaCliContractTests).Assembly.Location}",
            Path.Combine(repository, ".github/scripts/harness-gate.sh"),
            "--candidate", root, "--base", basis, "--candidate-lean-report", report,
        };
        if (scenario == "retired-option") arguments.AddRange(["--test-map-cache-root", Path.Combine(root, "test-maps")]);
        var result = TestProcessRunner.Run("/usr/bin/env", arguments, root,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var output = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        log.WriteLine(JsonSerializer.Serialize(new { executable = "/usr/bin/env", arguments, result.ExitCode, output }));
        Assert.True(result.ExitCode == expectedExit, $"expected {expectedExit}, got {result.ExitCode}: {output}");
        Assert.True(output.Contains(diagnostic, StringComparison.Ordinal), $"missing {diagnostic}: {output}");
        Assert.False(Directory.Exists(Path.Combine(root, "test-maps")));

        ProcessOutput Git(params string[] args) => RequireSuccess(TestProcessRunner.Run("git", args,
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024));
    }

    [Fact]
    public void ActualCandidateCheckCliRejectsRetiredTestMapOption()
    {
        using var temporary = new TemporaryDirectory();
        var result = TestProcessRunner.Run("dotnet", [typeof(StrataLint.Cli.Program).Assembly.Location, "check",
            "--protected-base", new string('a', 40), "--candidate-lean-report", "missing.json",
            "--test-map-cache-root", "test-maps"], temporary.Path,
            TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        log.WriteLine(JsonSerializer.Serialize(new { assembly = typeof(StrataLint.Cli.Program).Assembly.Location, result.ExitCode, error = Encoding.UTF8.GetString(result.StandardError) }));
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("USAGE: StrataLint check", Encoding.UTF8.GetString(result.StandardError), StringComparison.Ordinal);
    }

    private static ProcessOutput RequireSuccess(ProcessOutput result)
    {
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        return result;
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteExecutable(string path, string body)
    {
        File.WriteAllText(path, "#!/usr/bin/env bash\nset -euo pipefail\n" + body + "\n");
        File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
