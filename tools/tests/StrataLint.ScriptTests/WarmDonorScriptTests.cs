using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class WarmDonorScriptTests
{
    [Theory]
    [InlineData("harness/topic", "", "branch is not dev", 1)]
    [InlineData("dev", " M changed", "worktree is not clean", 2)]
    public void PreconditionsFailClosedWithSkippedReceipt(
        string branch,
        string status,
        string reason,
        int expectedCalls)
    {
        if (OperatingSystem.IsWindows()) return;

        using var run = Run(branch, status, pullExit: 0, leanExit: 0);

        Assert.Equal(0, run.Process.ExitCode);
        AssertReceipt(run.Process, "skipped", "precondition", reason);
        Assert.Equal(expectedCalls, run.CallLines.Length);
        Assert.DoesNotContain("pull", run.CallsText, StringComparison.Ordinal);
        Assert.DoesNotContain("make ", run.CallsText, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(41, 0, 41, "pull", "git pull --ff-only origin dev failed")]
    [InlineData(0, 42, 42, "lean", "make lean failed")]
    public void ActionFailuresProduceFailedReceipt(
        int pullExit,
        int leanExit,
        int expectedExit,
        string phase,
        string reason)
    {
        if (OperatingSystem.IsWindows()) return;

        using var run = Run("dev", "", pullExit, leanExit);

        Assert.Equal(expectedExit, run.Process.ExitCode);
        AssertReceipt(run.Process, "failed", phase, reason);
        var calls = ScriptHarnessScratch.ReadScratchLines(run.Calls);
        Assert.Equal("git pull --ff-only origin dev", calls[2]);
        Assert.Equal(phase == "pull" ? 3 : 4, calls.Length);
    }

    [Fact]
    public void CleanDevPullsThenBuildsAndProducesWarmedReceipt()
    {
        if (OperatingSystem.IsWindows()) return;

        using var run = Run("dev", "", pullExit: 0, leanExit: 0);

        Assert.Equal(0, run.Process.ExitCode);
        AssertReceipt(run.Process, "warmed", "complete", null);
        var calls = ScriptHarnessScratch.ReadScratchLines(run.Calls);
        Assert.Equal("git pull --ff-only origin dev", calls[2]);
        Assert.EndsWith(" lean", calls[3], StringComparison.Ordinal);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static ScriptRun Run(string branch, string status, int pullExit, int leanExit)
    {
        var fixture = new TemporaryDirectory();
        var repository = Path.Combine(fixture.Path, "repository");
        var script = Path.Combine(repository, "tools", "scripts", "worktree", "warm-donor.sh");
        var bin = Path.Combine(fixture.Path, "bin");
        var calls = Path.Combine(fixture.Path, "calls");
        ScriptHarnessScratch.EnsureDirectory(bin);
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/warm-donor.sh"),
            script);
        WriteExecutable(
            Path.Combine(bin, "git"),
            "printf 'git %s\\n' \"$*\" >> \"$WARM_CALLS\"\n"
            + "case \"$1\" in\n"
            + "  symbolic-ref) printf '%s\\n' \"$WARM_BRANCH\";;\n"
            + "  status) printf '%s' \"$WARM_STATUS\";;\n"
            + "  pull) exit \"$WARM_PULL_EXIT\";;\n"
            + "esac");
        WriteExecutable(
            Path.Combine(bin, "make"),
            "printf 'make %s\\n' \"$*\" >> \"$WARM_CALLS\"\nexit \"$WARM_LEAN_EXIT\"");
        var process = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:$PATH\" WARM_CALLS=\"$2\" WARM_BRANCH=\"$3\" WARM_STATUS=\"$4\" WARM_PULL_EXIT=\"$5\" WARM_LEAN_EXIT=\"$6\" exec /bin/bash \"$7\"",
                "warm-donor-test",
                bin,
                calls,
                branch,
                status,
                pullExit.ToString(System.Globalization.CultureInfo.InvariantCulture),
                leanExit.ToString(System.Globalization.CultureInfo.InvariantCulture),
                script,
            ],
            repository,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        return new ScriptRun(fixture, calls, process);
    }

    private static void AssertReceipt(ProcessOutput process, string status, string phase, string? reason)
    {
        var output = Encoding.UTF8.GetString(process.StandardOutput);
        Assert.StartsWith("LEAN_DONOR_WARM ", output, StringComparison.Ordinal);
        using var receipt = JsonDocument.Parse(output["LEAN_DONOR_WARM ".Length..]);
        Assert.Equal(status, receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal(phase, receipt.RootElement.GetProperty("phase").GetString());
        Assert.Equal(reason, receipt.RootElement.GetProperty("reason").GetString());
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteExecutable(string path, string content)
    {
        ScriptHarnessScratch.WriteExecutableStub(path, content);
    }

    private sealed record ScriptRun(
        TemporaryDirectory Fixture,
        string Calls,
        ProcessOutput Process) : IDisposable
    {
        internal string[] CallLines => ScriptHarnessScratch.ReadScratchLines(Calls);

        internal string CallsText => ScriptHarnessScratch.ReadScratchText(Calls);

        public void Dispose() => Fixture.Dispose();
    }
}
