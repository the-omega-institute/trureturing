using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class NativePhaseEvidenceTests
{
    // Synthetic copies of the pinned native Init-only probe's status output.
    private const string Warm = "✔ [0/3] Ran job computation\n✔ [1/3] Ran native_probe:extraDep\n"
        + "✔ [2/3] Replayed Probe\n✔ [3/3] Ran native_probe/Probe:default\nBuild completed successfully (3 jobs).\n";

    [Theory]
    [InlineData(false, 0, 1)]
    [InlineData(true, 1, 0)]
    public void CompleteNativeStatusesCountJobsRatherThanCompilerInvocations(bool changed, int built, int replayed)
    {
        using var counts = Counts(changed ? Warm.Replace("Replayed Probe", "Built Probe (15ms)", StringComparison.Ordinal) : Warm);
        Assert.Equal("complete", counts.RootElement.GetProperty("status").GetString());
        Assert.Equal(built, counts.RootElement.GetProperty("built").GetInt32());
        Assert.Equal(replayed, counts.RootElement.GetProperty("replayed").GetInt32());
        Assert.Equal(3, counts.RootElement.GetProperty("registered_jobs").GetInt32());
        Assert.Equal(4, counts.RootElement.GetProperty("status_rows").GetInt32());
    }

    [Theory]
    [InlineData("", 0, true, "unknown")]
    [InlineData("Build completed successfully (3 jobs).\n", 0, true, "unknown")]
    [InlineData("✔ [2/3] Built Probe\n", 0, true, "partial")]
    [InlineData(Warm, 19, true, "partial")]
    [InlineData(Warm, 0, false, "partial")]
    [InlineData(Warm + "✔ [2/3] Built Duplicate\n", 0, true, "unknown")]
    public void MissingOrIncompleteOutputNeverSuppliesZeroTotals(string output, int exit, bool full, string status)
    {
        using var counts = Counts(output, exit, full);
        Assert.Equal(status, counts.RootElement.GetProperty("status").GetString());
        Assert.Equal(JsonValueKind.Null, counts.RootElement.GetProperty("built").ValueKind);
        Assert.Equal(JsonValueKind.Null, counts.RootElement.GetProperty("replayed").ValueKind);
    }

    [Theory]
    [InlineData(null)]
    [InlineData("Lake version future")]
    public void UnsupportedNativeVersionIsUnknown(string? version)
    {
        using var counts = JsonDocument.Parse(JsonSerializer.Serialize(LeanPhaseEvidence.CountJobs(
            new ProcessOutput(0, Encoding.UTF8.GetBytes(Warm), []), version, true)));
        Assert.Equal("unknown", counts.RootElement.GetProperty("status").GetString());
        Assert.Equal(JsonValueKind.Null, counts.RootElement.GetProperty("observed_built").ValueKind);
    }

    [Theory]
    [InlineData(false, 0)]
    [InlineData(false, 19)]
    [InlineData(true, 0)]
    [InlineData(true, 19)]
    public void ObservationUsesInjectedTimeAndCannotReplaceExecution(bool brokenClock, int exit)
    {
        var clock = new FixtureClock(brokenClock);
        var observer = new LeanPhaseEvidence(new NativeRunner(exit, () => clock.Tick = 25), "lake", clock)
            { Scope = "lake-build" };
        var result = observer.Run("lake", ["build"], "/synthetic", TestBudgets.WorkflowProcessHangGuard);
        Assert.Equal(exit, result.ExitCode);
        Assert.Equal("native stdout\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal("native stderr\n", Encoding.UTF8.GetString(result.StandardError));
        using var record = JsonDocument.Parse(observer.Records.ToString()["LEAN_NATIVE_PHASE ".Length..]);
        Assert.Equal(brokenClock ? "error" : "measured", record.RootElement.GetProperty("timing_status").GetString());
        if (brokenClock) Assert.Equal(JsonValueKind.Null, record.RootElement.GetProperty("elapsed_ms").ValueKind);
        else Assert.Equal(25, record.RootElement.GetProperty("elapsed_ms").GetDouble());
        Assert.Equal(exit, record.RootElement.GetProperty("exit_code").GetInt32());
    }

    private static JsonDocument Counts(string output, int exit = 0, bool full = true) =>
        JsonDocument.Parse(JsonSerializer.Serialize(LeanPhaseEvidence.CountJobs(
            new ProcessOutput(exit, Encoding.UTF8.GetBytes(output), []), LeanPhaseEvidence.SupportedVersion, full)));

    private sealed class FixtureClock(bool broken) : TimeProvider
    {
        internal long Tick { get; set; }
        public override long TimestampFrequency => 1000;
        public override long GetTimestamp() => broken ? throw new IOException("measurement unavailable") : Tick;
        public override DateTimeOffset GetUtcNow() => DateTimeOffset.UnixEpoch.AddMilliseconds(Tick);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(19)]
    public void WriterPublishesNativeEvidenceAndPreservesChildExit(int exit)
    {
        using var root = new TemporaryDirectory();
        File.WriteAllText(Path.Combine(root.Path, "lean-toolchain"), "leanprover/lean4:v4.33.0\n");
        File.WriteAllText(Path.Combine(root.Path, "lake-manifest.json"), LeanCacheFixtureFile.Manifest());
        var lake = Path.Combine(root.Path, ".lake");
        Directory.CreateDirectory(lake);
        LeanCacheStamp.Write(lake, LeanPinSet.TryReadWorktree(root.Path, out _)!);
        ProjectOleanFixture.Write(root.Path, "Warm");
        var result = LeanCacheEnsureCommand.RunWithWriter(root.Path, ["--", "lake", "build"],
            new NativeRunner(exit), new RecordingDirectoryCloner());
        if (exit != 0) Assert.Equal(exit, result.ExitCode);
        Assert.Equal(exit == 0, result.Success);
        Assert.Contains("native stdout", result.Output, StringComparison.Ordinal);
        Assert.Contains("native stderr", result.Error, StringComparison.Ordinal);
        var lines = result.Error.Split('\n').Where(line => line.StartsWith("LEAN_NATIVE_PHASE ", StringComparison.Ordinal));
        Assert.NotEmpty(lines);
        using var record = JsonDocument.Parse(lines.Last()["LEAN_NATIVE_PHASE ".Length..]);
        Assert.Equal(exit, record.RootElement.GetProperty("exit_code").GetInt32());
        Assert.Equal("lake-build", record.RootElement.GetProperty("scope").GetString());
        Assert.Equal(JsonValueKind.Null, record.RootElement.GetProperty("lean_compiler_invocations").ValueKind);
    }

    private sealed class NativeRunner(int exit, Action? execute = null) : IWorktreeProcessRunner
    {
        public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout)
        {
            Assert.Equal("lake", fileName);
            if (arguments.SequenceEqual(["--version"]))
                return new ProcessOutput(0, Encoding.UTF8.GetBytes("Lake version 5.0.0-src+d8b1897 (Lean version 4.33.0)\n"), []);
            Assert.Contains("build", arguments);
            execute?.Invoke();
            return new ProcessOutput(exit, Encoding.UTF8.GetBytes("native stdout\n"), Encoding.UTF8.GetBytes("native stderr\n"));
        }
    }
}
