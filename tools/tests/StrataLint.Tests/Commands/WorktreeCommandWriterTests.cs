using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    [Theory]
    [InlineData("miss", false)]
    [InlineData("corrupt", false)]
    [InlineData("timeout", false)]
    [InlineData("miss", true)]
    [InlineData("corrupt", true)]
    [InlineData("timeout", true)]
    public void OptionalArchiveFailureReachesBuildWithItsOwnBudget(string failure, bool buildFails)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var lake = Path.Combine(repository.Path, ".lake");
        var pins = LeanPinSet.TryReadWorktree(repository.Path, out _)!;
        LeanCacheStamp.Write(lake, pins);
        var script = LeanArchiveFetch.ScriptPath(repository.Path);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.WriteAllText(script, "#!/bin/sh\nexit 0\n");
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = $"LEAN_CACHE_FETCH {{\"status\":\"miss\",\"reason\":\"{failure}\"}}\n",
            ArchiveExitCode = 1,
            AfterArchiveFetch = _ =>
            {
                using var concurrent = LeanCacheWriterGuard.TryAcquire(lake);
                Assert.Null(concurrent);
                if (failure == "timeout") throw new TimeoutException("fixture archive deadline expired");
            },
            FailWrappedLake = buildFails,
        };

        var result = WorktreeCommand.Run(
            repository.Path, ["with-cache-writer", "--", "lake", "build"], runner);

        Assert.Equal(!buildFails, result.Success);
        Assert.Equal(1, runner.ArchiveInvocations);
        var archive = Assert.Single(runner.Invocations, static call => call.FileName == "/bin/bash");
        Assert.Contains("--writer-owned", archive.Arguments);
        Assert.Equal(
            LeanCacheBudgetPolicy.LeanInspectJobBudgetMinutes - LeanCacheBudgetPolicy.PostArchiveReserveMinutes,
            archive.Timeout.TotalMinutes);
        var build = Assert.Single(runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        Assert.Equal(LeanCacheProvisioner.LeanCommandBudget, build.Timeout);
        Assert.True(runner.Invocations.IndexOf(build) > runner.Invocations.IndexOf(archive));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(failure == "timeout" ? "failed" : "miss",
            receipt.RootElement.GetProperty("archive_status").GetString());
        Assert.Contains(failure == "timeout" ? "fixture archive deadline expired" : failure,
            receipt.RootElement.GetProperty("archive_reason").GetString()!, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(lake, "build")));
        if (buildFails) Assert.Contains("wrapped lake command failed", result.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RestoredProjectSeedBypassesArchiveAndStillRunsBuild(bool buildFails)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        _ = ProjectOleanFixture.Write(repository.Path, "ActionsSeed");
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "unused",
            FailWrappedLake = buildFails,
        };

        var result = WorktreeCommand.Run(
            repository.Path, ["with-cache-writer", "--", "lake", "build"], runner);

        Assert.Equal(!buildFails, result.Success);
        Assert.Equal(0, runner.ArchiveInvocations);
        Assert.Contains(runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("not_attempted", receipt.RootElement.GetProperty("archive_status").GetString());
        Assert.Equal("project olean state is warm",
            receipt.RootElement.GetProperty("archive_skip_reason").GetString());
    }

    [Fact]
    public void ArchiveProcessDeadlineIsReportedAsAnOptionalFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        var script = LeanArchiveFetch.ScriptPath(repository.Path);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        // A FIFO with no writer cannot finish; the injected deadline decides the outcome.
        File.WriteAllText(script, "#!/bin/sh\nmkfifo \"$0.fifo\"\nexec cat \"$0.fifo\"\n");
        using var guard = LeanCacheWriterGuard.TryAcquire(Path.Combine(repository.Path, ".lake"));
        Assert.NotNull(guard);

        var attempt = LeanArchiveFetch.Run(
            repository.Path, new ProductionWorktreeProcessRunner(), TestBudgets.ZeroDuration, guard);

        Assert.Equal(LeanArchiveOutcome.Failed, attempt.Outcome);
        Assert.Contains("timed out after 0 seconds", attempt.Reason!, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(repository.Path, ".lake")));
    }

    [Fact]
    public void WriterEntryContinuesToLakeBuildWhenCacheGetTimesOut()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        _ = ProjectOleanFixture.Write(repository.Path, "ExistingProject");
        var runner = new RecordingWorktreeProcessRunner { ThrowCacheGetTimeout = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["with-cache-writer", "--", "lake", "build"],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("degraded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Contains(
            "cache get timed out",
            receipt.RootElement.GetProperty("reason").GetString()!,
            StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void WriterEntryReturnsWrappedLakeFailure()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { FailWrappedLake = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["with-cache-writer", "--", "lake", "build"],
            runner);

        Assert.False(result.Success);
        Assert.Contains("wrapped lake command failed", result.Error, StringComparison.Ordinal);
        Assert.Contains(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
    }

    [Fact]
    public void WriterEntryHoldsTargetWriterGuardDuringWrappedLakeCommand()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        bool? concurrentWriterAcquired = null;
        var runner = new RecordingWorktreeProcessRunner
        {
            DuringWrappedLake = root =>
            {
                using var concurrent = LeanCacheWriterGuard.TryAcquire(Path.Combine(root, ".lake"));
                concurrentWriterAcquired = concurrent is not null;
            },
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["with-cache-writer", "--", "lake", "build"],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.False(concurrentWriterAcquired);
    }
}
