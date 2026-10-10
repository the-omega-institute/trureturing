using System.Text;
using System.Text.Json;
using Xunit.Abstractions;
using StrataLint.Runtime;
using StrataLint.Engine;
using Xunit;

namespace StrataLint.WorktreeContract.Tests;

public sealed class WorktreeProtocolTests(ITestOutputHelper output)
{
    [Theory]
    [InlineData("spaced", "clean-lanes", "directory")]
    [InlineData("spaced", "clean-all", "directory")]
    [InlineData("spaced", "worktree-clean", "directory")]
    [InlineData("spaced", "clean-lanes", "file")]
    [InlineData("spaced", "clean-all", "file")]
    [InlineData("plain", "clean-lanes", "directory")]
    [InlineData("plain", "clean-all", "directory")]
    [InlineData("plain", "worktree-clean", "directory")]
    public void CleanupMakeEntrancesUseProductionQualification(string sourcePath, string entrance, string invocation)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, sourcePath, entrance, invocation, "CleanupMakeTests"],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("normal")]
    [InlineData("nonzero")]
    [InlineData("deadline")]
    [InlineData("launcher")]
    public void CleanupFixtureSettlesOwnedNativeCommands(string mode)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, "plain", "clean-lanes", "directory", "CommandLifetimeTests.test_" + mode],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void FixtureDisposalWaitsForCompleteOutcomeAndNativeSettlement()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, "plain", "clean-lanes", "directory", "FixtureDisposalTests"],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void OuterInterruptionRetainsFailedInputsAndPublishesOwnedGroupSettlement()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var captured = new List<string>();
        var failure = Assert.Throws<SkipException>(() => CaptureCleanupOutput((stdout, stderr) =>
            TestProcessRunner.Run("python3", ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/cleanup_make_tests.py"),
                root, "plain", "clean-lanes", "directory", "CommandLifetimeTests.test_deadline"],
                root, TimeSpan.FromSeconds(3), 1024 * 1024,
                standardOutput: stdout, standardError: stderr,
                interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), captured.Add));
        Assert.StartsWith(InfrastructureHangGuard.SkipReasonPrefix, failure.Message);
        foreach (var value in captured) output.WriteLine(value);
        var events = captured[0].Split('\n').Where(line => line.StartsWith('{'))
            .Select(line => JsonDocument.Parse(line).RootElement.Clone()).ToArray();
        var command = Assert.Single(events, item => item.GetProperty("event").GetString() == "fixture_command"
            && item.GetProperty("status").GetString() == "interrupted");
        Assert.True(command.GetProperty("settled").GetBoolean());
        Assert.Equal(120, command.GetProperty("guard_seconds").GetInt32());
        var completion = Assert.Single(events, item => item.GetProperty("event").GetString() == "fixture_completion");
        Assert.False(completion.GetProperty("successful").GetBoolean());
        Assert.True(completion.GetProperty("commands_settled").GetBoolean());
        Assert.True(completion.GetProperty("interrupted").GetBoolean());
        var inputs = completion.GetProperty("inputs").EnumerateArray().Select(item => item.GetString()!).ToArray();
        foreach (var path in inputs) Assert.True(Directory.Exists(path));
        var group = command.GetProperty("pid").GetInt32().ToString(System.Globalization.CultureInfo.InvariantCulture);
        var native = TestProcessRunner.Run("python3",
            ["-c", "import os,sys; os.killpg(int(sys.argv[1]),0)", group], root, TimeSpan.FromSeconds(10), 4096);
        Assert.NotEqual(0, native.ExitCode);
        Assert.Contains("ProcessLookupError", Encoding.UTF8.GetString(native.StandardError), StringComparison.Ordinal);
        foreach (var path in inputs) Directory.Delete(path, recursive: true);
    }

    private static ProcessOutput CaptureCleanupOutput(
        Func<Stream, Stream, ProcessOutput> run, Action<string> publish)
    {
        using var stdout = new MemoryStream();
        using var stderr = new MemoryStream();
        using var stdoutSink = Stream.Synchronized(stdout);
        using var stderrSink = Stream.Synchronized(stderr);
        try
        {
            return run(stdoutSink, stderrSink);
        }
        finally
        {
            // The runner can throw before returning its buffered ProcessOutput.
            // Its existing destinations preserve bytes already read on every exit path.
            lock (stdout) publish(Encoding.UTF8.GetString(stdout.ToArray()));
            lock (stderr) publish(Encoding.UTF8.GetString(stderr.ToArray()));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CleanupFixturePublishesEvidenceBeforeOuterGuardReturns(bool deadline)
    {
        if (OperatingSystem.IsWindows()) return;
        var captured = new List<string>();
        var root = TestRepositoryLayout.FindRoot();
        ProcessOutput Run(Stream stdout, Stream stderr) => TestProcessRunner.Run("/bin/sh",
            ["-c", "printf 'phase=owned-command partial-output\\n'; " +
                "printf 'partial-error\\n' >&2; " + (deadline ? "exec sleep 600" : "exit 7")],
            root, TimeSpan.FromSeconds(1), 1024 * 1024,
            standardOutput: stdout, standardError: stderr);
        if (deadline)
        {
            var failure = Assert.Throws<SkipException>(() => CaptureCleanupOutput(Run, captured.Add));
            Assert.StartsWith(InfrastructureHangGuard.SkipReasonPrefix, failure.Message);
        }
        else
        {
            Assert.Equal(7, CaptureCleanupOutput(Run, captured.Add).ExitCode);
        }
        Assert.Equal(["phase=owned-command partial-output\n", "partial-error\n"], captured);
        foreach (var item in captured) output.WriteLine(item);
    }

    [Theory]
    [InlineData("recovery_clean_index_with_resolved_conflict_is_preserved")]
    [InlineData("recovery_published_prior_commit_message_is_reconstructable")]
    [InlineData("recovery_local_repository_is_not_a_remote")]
    [InlineData("recovery_checkpoint_protects_input_reads")]
    public void RecoveryQualificationUsesActualIndexAndCommitObjects(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests." + probe], root, TimeSpan.FromSeconds(90), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("consumer_mirror_uses_real_git_with_stubbed_github")]
    [InlineData("consumer_land_attributes_paths_with_external_checks_stubbed")]
    [InlineData("consumer_land_cannot_build_during_native_destruction")]
    [InlineData("consumer_land_scopes_operating_children")]
    public void AgentConsumerUsesRealGitAndPreservesIndependentMaterial(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "ProtocolTests." + probe], root, TimeSpan.FromSeconds(90), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void CooperativeProtocolPreservesRealProcessAndGitState()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = CaptureCleanupOutput((stdout, stderr) => TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"), root],
            root, TimeSpan.FromSeconds(180), 1024 * 1024,
            standardOutput: stdout, standardError: stderr,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture), output.WriteLine);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
