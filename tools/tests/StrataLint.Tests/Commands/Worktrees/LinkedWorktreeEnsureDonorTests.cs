using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    private const string LinkedArchiveDisabled = "linked worktree: release archive disabled";

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void LinkedPinMigrationWithColdConsentProducesItsOwnCurrentCache(
        bool existingCache,
        bool omitMathlibOleans)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "unchanged main cache\n", projectWarm: true);
        var mainStamp = File.ReadAllBytes(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake")));
        var target = AddWorktree(repository.Path, "pin-migration");
        if (existingCache) WriteCache(target, "obsolete lane cache\n", projectWarm: true);
        ChangeMathlibPartition(target);
        var pins = ReadPins(target);
        bool? concurrentWriterAcquired = null;
        var runner = new RecordingWorktreeProcessRunner
        {
            OmitMathlibOleans = omitMathlibOleans,
            DuringWrappedLake = root =>
            {
                Assert.Equal(LeanCacheStampState.Match,
                    LeanCacheStamp.Inspect(Path.Combine(root, ".lake"), pins).State);
                Assert.False(File.Exists(Path.Combine(root, ".lake", "build", "cache.bin")));
                Assert.False(File.Exists(Path.Combine(root, ".lake", "build", "lib", "lean", "FixtureWarm.olean")));
                using var concurrent = LeanCacheWriterGuard.TryAcquire(Path.Combine(root, ".lake"));
                concurrentWriterAcquired = concurrent is not null;
            },
        };
        var cloner = new RecordingDirectoryCloner();

        var result = LeanCacheEnsureCommand.RunWithWriter(
            repository.Path,
            ["--path", target, "--", "lake", "build"],
            runner,
            cloner,
            FileSystemLeanCacheStateProbe.Instance,
            variable => variable == "STRATALINT_ACCEPT_COLD_BUILD" ? "1" : null);

        Assert.True(result.Success, result.Error);
        Assert.False(concurrentWriterAcquired);
        Assert.Empty(cloner.Invocations);
        Assert.Equal(0, runner.ArchiveInvocations);
        Assert.False(runner.CacheGetSawExistingProjection);
        Assert.Equal(new[] { "exe cache get", "build" }, runner.Invocations
            .Where(static call => Path.GetFileName(call.FileName) == "lake")
            .Select(static call => string.Join(" ", call.Arguments)).ToArray());
        Assert.Equal(mainStamp,
            File.ReadAllBytes(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake"))));
        Assert.Equal("unchanged main cache\n", LeanCacheFixtureFile.ReadCacheText(repository.Path));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("fetched", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("donor").ValueKind);
        Assert.Equal("cache-get", receipt.RootElement.GetProperty("method").GetString());
        Assert.Equal(pins.Sha256, receipt.RootElement.GetProperty("pin_sha256").GetString());
        Assert.True(receipt.RootElement.GetProperty("cold_build_consent").GetBoolean());
        Assert.Equal("cold", receipt.RootElement.GetProperty("project_olean_state").GetString());
        Assert.Equal(LinkedArchiveDisabled, receipt.RootElement.GetProperty("archive_skip_reason").GetString());

        // A produced identity with an empty project layer must permit the first
        // compilation, including subsequent package phases in the same build.
        var repeated = LeanCacheEnsureCommand.RunWithWriter(
            repository.Path,
            ["--path", target, "--", "lake", "build"],
            runner,
            cloner,
            FileSystemLeanCacheStateProbe.Instance,
            _ => "1");
        Assert.True(repeated.Success, repeated.Error);
        Assert.Single(runner.Invocations, static call => call.Arguments.SequenceEqual(["exe", "cache", "get"]));
    }

    [Theory]
    [InlineData(null)]
    [InlineData("true")]
    public void LinkedPinMigrationWithoutExactConsentKeepsItsOldCache(string? consent)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "main cache\n", projectWarm: true);
        var target = AddWorktree(repository.Path, "migration-without-consent");
        WriteCache(target, "retained old cache\n", projectWarm: true);
        ChangeMathlibPartition(target);
        var runner = new RecordingWorktreeProcessRunner();

        var result = LeanCacheEnsureCommand.RunWithWriter(repository.Path,
            ["--path", target, "--", "lake", "build"], runner, new RecordingDirectoryCloner(),
            FileSystemLeanCacheStateProbe.Instance, _ => consent);

        Assert.False(result.Success);
        AssertNoCacheGet(runner);
        Assert.DoesNotContain(runner.Invocations, static call => call.Arguments.SequenceEqual(["build"]));
        Assert.Equal("retained old cache\n", LeanCacheFixtureFile.ReadCacheText(target));
        Assert.Equal(LeanCacheStampState.Mismatch,
            LeanCacheStamp.Inspect(Path.Combine(target, ".lake"), ReadPins(target)).State);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("corrupt")]
    [InlineData("same-partition")]
    [InlineData("invalid-pins")]
    public void ColdConsentDoesNotAuthorizeUnknownIdentityOrNonMigration(string scenario)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "main cache\n", projectWarm: true);
        var target = AddWorktree(repository.Path, "invalid-migration-" + scenario);
        WriteCache(target, "preserved cache\n", projectWarm: true);
        if (scenario != "same-partition") ChangeMathlibPartition(target);
        var stamp = LeanCacheStamp.PathFor(Path.Combine(target, ".lake"));
        if (scenario == "missing") File.Delete(stamp);
        if (scenario == "corrupt") File.WriteAllText(stamp, "invalid stamp\n");
        if (scenario == "same-partition")
        {
            WriteMismatchedStamp(target);
            File.Delete(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake")));
        }
        if (scenario == "invalid-pins")
            File.WriteAllText(Path.Combine(target, "lake-manifest.json"), LeanCacheFixtureFile.Manifest('c'));
        var runner = new RecordingWorktreeProcessRunner();

        var result = LeanCacheEnsureCommand.RunWithWriter(repository.Path,
            ["--path", target, "--", "lake", "build"], runner, new RecordingDirectoryCloner(),
            FileSystemLeanCacheStateProbe.Instance, _ => "1");

        Assert.False(result.Success);
        AssertNoCacheGet(runner);
        Assert.DoesNotContain(runner.Invocations, static call => call.Arguments.SequenceEqual(["build"]));
        Assert.Equal("preserved cache\n", LeanCacheFixtureFile.ReadCacheText(target));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LinkedPinMigrationProducerFailurePublishesNoIdentityOrBuild(bool stampFailure)
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var target = AddWorktree(repository.Path, "migration-producer-failure");
        WriteCache(target, "obsolete cache\n", projectWarm: true);
        ChangeMathlibPartition(target);
        var runner = new RecordingWorktreeProcessRunner
        {
            FailLake = !stampFailure,
            BlockStampAfterCacheGet = stampFailure,
        };

        var result = LeanCacheEnsureCommand.RunWithWriter(repository.Path,
            ["--path", target, "--", "lake", "build"], runner, new RecordingDirectoryCloner(),
            FileSystemLeanCacheStateProbe.Instance, _ => "1");

        Assert.False(result.Success);
        Assert.Single(runner.Invocations, static call => call.Arguments.SequenceEqual(["exe", "cache", "get"]));
        Assert.DoesNotContain(runner.Invocations, static call => call.Arguments.SequenceEqual(["build"]));
        Assert.False(Directory.Exists(Path.Combine(target, ".lake")));
    }

    private static void ChangeMathlibPartition(string target)
    {
        File.WriteAllText(Path.Combine(target, "lean-toolchain"), "leanprover/lean4:v4.34.1\n");
        File.WriteAllText(Path.Combine(target, "lake-manifest.json"), LeanCacheFixtureFile.Manifest('b'));
        StrataLint.TestSupport.RegPackageFixture.Write(target);
    }

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
    public void LinkedLaneUsesExplicitCurrentPinDonorWhenMainPartitionIsDifferent()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "dev partition cache\n");

        var producer = AddWorktree(repository.Path, "current-pin-producer");
        ChangeMathlibPartition(producer);
        Git(producer, "add", "lean-toolchain", "lake-manifest.json", "Reg", "tools/lean-inspector-reg");
        Git(producer, "commit", "-m", "current partition producer");
        WriteCache(producer, "current pin producer cache\n", projectWarm: true);

        var target = AddWorktree(producer, "current-pin-target");
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();
        using (var inventory = GitWorktreeInventory.SelectDonor(
            target,
            ReadPins(target),
            runner,
            FileSystemLeanCacheStateProbe.Instance,
            requireProjectWarm: true,
            donorRepository: producer))
        {
            Assert.True(
                string.Equals(
                    LeanCacheGuard.PhysicalPath(producer),
                    inventory.Donor,
                    StringComparison.Ordinal),
                inventory.Notice);
        }

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "ensure-cache",
                "--path", target,
                "--donor-repository", producer,
            ],
            runner,
            cloner);

        Assert.True(result.Success, result.Error);
        var clone = Assert.Single(cloner.Invocations);
        Assert.Equal(
            Path.Combine(LeanCacheGuard.PhysicalPath(producer), ".lake"),
            clone.Source);
        Assert.DoesNotContain(runner.Invocations, static call =>
            Path.GetFileName(call.FileName) == "lake");
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("seeded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal(
            LeanCacheGuard.PhysicalPath(producer),
            receipt.RootElement.GetProperty("donor").GetString());
        Assert.Equal(ReadPins(target).Sha256, receipt.RootElement.GetProperty("pin_sha256").GetString());
        Assert.Equal(LinkedArchiveDisabled, receipt.RootElement.GetProperty("archive_skip_reason").GetString());
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
