using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    private const string LinkedArchiveDisabled = "linked worktree: release archive disabled";

    [Fact]
    public void LinkedLaneWithAbsentLakeClonesOnlyTheWarmMainCheckout()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm main cache\n");
        _ = WriteProjectOlean(repository.Path, "WarmMain");
        var target = AddWorktree(repository.Path, "linked-absent-lake");
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            cloner);

        Assert.True(result.Success, result.Error);
        var clone = Assert.Single(cloner.Invocations);
        Assert.Equal(Path.Combine(LeanCacheGuard.PhysicalPath(repository.Path), ".lake"), clone.Source);
        Assert.StartsWith(Path.Combine(target, ".lake") + ".stage-", clone.Target, StringComparison.Ordinal);
        Assert.Equal(0, runner.ArchiveInvocations);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("seeded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("clonefile", receipt.RootElement.GetProperty("method").GetString());
        Assert.Equal(LinkedArchiveDisabled, receipt.RootElement.GetProperty("archive_skip_reason").GetString());
    }

    [Theory]
    [InlineData("stamp absent", "stamp-absent")]
    [InlineData("stamp mismatch", "stamp-mismatch")]
    [InlineData("project layer cold", "project-cold")]
    public void LinkedLaneWithAbsentLakeFailsClosedForEachColdMainState(
        string expectedColdState,
        string mainState)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(
            repository.Path,
            "main cache\n",
            stamp: mainState != "stamp-absent",
            projectWarm: mainState != "project-cold");
        if (mainState != "project-cold") _ = WriteProjectOlean(repository.Path, "MainProject");
        if (mainState == "stamp-mismatch") WriteMismatchedStamp(repository.Path);
        var target = AddWorktree(repository.Path, "linked-cold-main-" + mainState);
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            cloner);

        Assert.False(result.Success);
        Assert.Empty(cloner.Invocations);
        Assert.Equal(0, runner.ArchiveInvocations);
        AssertNoCacheGet(runner);
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal("failed", receipt.RootElement.GetProperty("status").GetString());
        var reason = receipt.RootElement.GetProperty("reason").GetString();
        Assert.Contains(expectedColdState, reason, StringComparison.Ordinal);
        Assert.Contains(MainWarmRemediation(repository.Path), reason, StringComparison.Ordinal);
        Assert.Equal(LinkedArchiveDisabled, receipt.RootElement.GetProperty("archive_skip_reason").GetString());
    }

    [Fact]
    public void LinkedLaneNeverUsesAWarmSiblingWhenMainCheckoutIsCold()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var sibling = AddWorktree(repository.Path, "warm-sibling");
        WriteCache(sibling, "warm sibling cache\n");
        _ = WriteProjectOlean(sibling, "WarmSibling");
        var target = AddWorktree(repository.Path, "main-only-target");
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            cloner);

        Assert.False(result.Success);
        Assert.Empty(cloner.Invocations);
        Assert.Equal(0, runner.ArchiveInvocations);
        using var receipt = ParseReceipt(result.Error);
        Assert.NotEqual(
            LeanCacheGuard.PhysicalPath(sibling),
            receipt.RootElement.GetProperty("donor").GetString());
        Assert.Contains("stamp absent", receipt.RootElement.GetProperty("reason").GetString(),
            StringComparison.Ordinal);
    }

    [Fact]
    public void LinkedLaneWithMatchingStampAndColdContentNamesLaneReseedRemediation()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm main cache\n");
        _ = WriteProjectOlean(repository.Path, "WarmMain");
        var target = AddWorktree(repository.Path, "cold-content-overlay");
        var targetLake = Path.Combine(target, ".lake");
        Directory.CreateDirectory(targetLake);
        LeanCacheStamp.Write(targetLake, ReadPins(target));
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            cloner);

        Assert.False(result.Success);
        Assert.Empty(cloner.Invocations);
        Assert.Equal(0, runner.ArchiveInvocations);
        AssertNoCacheGet(runner);
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal(
            LaneReseedRemediation(target),
            receipt.RootElement.GetProperty("reason").GetString());
        Assert.Equal(LinkedArchiveDisabled, receipt.RootElement.GetProperty("archive_skip_reason").GetString());
    }

    [Fact]
    public void LinkedRemediationsShellQuoteMainAndLanePathsContainingSpaces()
    {
        using var parent = new TemporaryDirectory();
        var mainCheckout = Path.Combine(parent.Path, "main checkout");
        Directory.CreateDirectory(mainCheckout);
        InitializeRepository(mainCheckout);
        var target = AddWorktree(mainCheckout, "lane-checkout");

        var coldMain = WorktreeCommand.Run(
            mainCheckout,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            new RecordingDirectoryCloner());

        Assert.False(coldMain.Success);
        Assert.Equal(
            $"main checkout stamp absent; {MainWarmRemediation(mainCheckout)}",
            ReceiptReason(coldMain.Error));

        WriteCache(mainCheckout, "warm main cache\n");
        _ = WriteProjectOlean(mainCheckout, "WarmMain");
        var targetLake = Path.Combine(target, ".lake");
        Directory.CreateDirectory(targetLake);
        LeanCacheStamp.Write(targetLake, ReadPins(target));

        var coldLane = WorktreeCommand.Run(
            mainCheckout,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            new RecordingDirectoryCloner());

        Assert.False(coldLane.Success);
        Assert.Equal(LaneReseedRemediation(target), ReceiptReason(coldLane.Error));
    }

    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void LinkedColdContentAndMissingBuildFailClosedWhenMainProjectLayerIsCold(
        bool matchingStamp)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "cold main project cache\n", projectWarm: false);
        var target = AddWorktree(repository.Path, matchingStamp ? "cold-content" : "missing-build");
        var targetLake = Path.Combine(target, ".lake");
        Directory.CreateDirectory(targetLake);
        if (matchingStamp) LeanCacheStamp.Write(targetLake, ReadPins(target));
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            cloner);

        Assert.False(result.Success);
        Assert.Empty(cloner.Invocations);
        Assert.Equal(0, runner.ArchiveInvocations);
        AssertNoCacheGet(runner);
        using var receipt = ParseReceipt(result.Error);
        Assert.Contains("project layer cold", receipt.RootElement.GetProperty("reason").GetString(),
            StringComparison.Ordinal);
        Assert.Contains(MainWarmRemediation(repository.Path), receipt.RootElement.GetProperty("reason").GetString(),
            StringComparison.Ordinal);
    }

    [Fact]
    public void LinkedLaneWithOwnWarmCacheSkipsMainProbeAndExpiredArchiveRefresh()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = AddWorktree(repository.Path, "own-warm-cache");
        WriteCache(target, "warm target cache\n");
        var targetOlean = WriteProjectOlean(target, "WarmTarget");
        File.SetLastWriteTimeUtc(targetOlean, TestEnvironmentBridge.UtcNow().AddHours(-7));
        var mainProjectRoot = Path.Combine(
            LeanCacheGuard.PhysicalPath(repository.Path),
            ".lake",
            "build",
            "lib",
            "lean");
        var probe = new DelegatingLeanCacheStateProbe(FileSystemLeanCacheStateProbe.Instance.ProbeOleans);
        var runner = new RecordingWorktreeProcessRunner { ArchiveReceipt = "unused" };

        var result = LeanCacheEnsureCommand.Run(
            repository.Path,
            ["--path", target],
            runner,
            new RecordingDirectoryCloner(),
            removePartial: null,
            probe);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, probe.Count(mainProjectRoot));
        Assert.Equal(0, runner.ArchiveInvocations);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("present", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal(LinkedArchiveDisabled, receipt.RootElement.GetProperty("archive_skip_reason").GetString());
    }

    [Fact]
    public void MainWorktreeEnsureStillUsesCacheGetWhenLakeIsAbsent()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(Path.Combine(repository.Path, ".lake", "cache-get.marker")));
        Assert.Contains(runner.Invocations, static call =>
            Path.GetFileName(call.FileName) == "lake"
            && call.Arguments.SequenceEqual(["exe", "cache", "get"]));
    }

    [Fact]
    public void MainWorktreeEnsureStillUsesArchiveForColdContent()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var lake = Path.Combine(repository.Path, ".lake");
        Directory.CreateDirectory(lake);
        LeanCacheStamp.Write(lake, ReadPins(repository.Path));
        WriteFetcher(repository.Path);
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"miss\",\"reason\":\"offline\"}\n",
            ArchiveExitCode = 1,
        };

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success, result.Error);
        Assert.Equal(1, runner.ArchiveInvocations);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("miss", receipt.RootElement.GetProperty("archive_status").GetString());
    }

    [Fact]
    public void MainWorktreeEnsureStillRefreshesAnExpiredWarmCache()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm main cache\n");
        var olean = WriteProjectOlean(repository.Path, "ExpiredMain");
        File.SetLastWriteTimeUtc(olean, TestEnvironmentBridge.UtcNow().AddHours(-7));
        WriteFetcher(repository.Path);
        var runner = new RecordingWorktreeProcessRunner
        {
            ArchiveReceipt = "LEAN_CACHE_FETCH {\"status\":\"miss\",\"reason\":\"offline\"}\n",
            ArchiveExitCode = 1,
        };

        var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

        Assert.True(result.Success, result.Error);
        Assert.Equal(1, runner.ArchiveInvocations);
        Assert.Contains("--refresh-stale", Assert.Single(runner.Invocations,
            static call => call.FileName == "/bin/bash").Arguments);
    }

    private static void WriteMismatchedStamp(string root)
    {
        var pins = LeanPinSet.Create(
            File.ReadAllBytes(Path.Combine(root, "lean-toolchain")),
            System.Text.Encoding.UTF8.GetBytes(LeanCacheFixtureFile.Manifest('b')));
        LeanCacheStamp.Write(Path.Combine(root, ".lake"), pins);
    }

    private static void AssertNoCacheGet(RecordingWorktreeProcessRunner runner) =>
        Assert.DoesNotContain(runner.Invocations, static call =>
            Path.GetFileName(call.FileName) == "lake"
            && call.Arguments.SequenceEqual(["exe", "cache", "get"]));

    private static string MainWarmRemediation(string mainCheckout) =>
        $"sync dev and warm the dev cache: make -C {ShellQuote(LeanCacheGuard.PhysicalPath(mainCheckout))} warm-donor";

    private static string Remediation(string mainCheckout) => MainWarmRemediation(mainCheckout);

    private static string LaneReseedRemediation(string lane) =>
        "the lane's content layer is cold while the main checkout is warm: remove "
        + $"{ShellQuote(Path.Combine(LeanCacheGuard.PhysicalPath(lane), ".lake"))} "
        + "and re-run so ensure seeds it from the main checkout";

    private static string ShellQuote(string value) => "'" + value.Replace("'", "'\"'\"'") + "'";

    private static string ReceiptReason(string text)
    {
        using var receipt = ParseReceipt(text);
        return receipt.RootElement.GetProperty("reason").GetString()!;
    }
}
