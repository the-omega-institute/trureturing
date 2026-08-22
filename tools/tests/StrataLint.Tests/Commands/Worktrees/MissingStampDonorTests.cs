using StrataLint.Cli;
using System.Text.Json;

namespace StrataLint.Tests;

public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void MissingColdClearCacheClonesOnlyWarmDonorBuildWithoutOverwritingLake()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        var donorOlean = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "missing-build-donor-target"));
        fixture.CreateLake();
        fixture.WriteTargetOwned("preserve me\n");
        bool? concurrentWriterAcquired = null;
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) =>
            {
                concurrentWriterAcquired = fixture.TryAcquireWriter();
            },
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.False(concurrentWriterAcquired);
        var clone = Assert.Single(cloner.Invocations);
        Assert.Equal(fixture.DonorBuild, clone.Source);
        Assert.StartsWith(
            fixture.BuildStagePrefix,
            clone.Target,
            StringComparison.Ordinal);
        Assert.Equal("preserve me\n", fixture.TargetOwnedText);
        Assert.True(fixture.HasClonedDonorOlean(donorOlean));
        Assert.False(fixture.TargetPackagesExist);
        Assert.True(fixture.StampMatches);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("seeded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("missing", receipt.RootElement.GetProperty("stamp_miss").GetString());
        Assert.Equal(
            LeanCacheGuard.PhysicalPath(repository.Path),
            receipt.RootElement.GetProperty("donor").GetString());
    }

    [Fact]
    public void MissingColdRecursivelyEmptyBuildClonesWarmDonor()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        var donorOlean = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "recursively-empty-build-target"));
        fixture.CreateNestedEmptyBuild();
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.NotEmpty(cloner.Invocations);
        Assert.True(fixture.HasClonedDonorOlean(donorOlean));
        Assert.True(fixture.StampMatches);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("seeded", receipt.RootElement.GetProperty("status").GetString());
    }

    [Fact]
    public void CorruptColdClearCacheStillReproducesInPlaceInsteadOfUsingWarmDonor()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var target = AddWorktree(repository.Path, "corrupt-build-donor-target");
        var targetLake = Path.Combine(target, ".lake");
        Directory.CreateDirectory(targetLake);
        File.WriteAllText(LeanCacheStamp.PathFor(targetLake), "not json\n");
        var cloner = new RecordingDirectoryCloner();
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.True(File.Exists(Path.Combine(targetLake, "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(targetLake, "build", "cache.bin")));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("corrupt", receipt.RootElement.GetProperty("stamp_miss").GetString());
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("donor").ValueKind);
    }

    [Fact]
    public void MissingProjectWarmCacheStillReproducesInPlace()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var target = AddWorktree(repository.Path, "project-warm-target");
        var targetOlean = WriteProjectOlean(target, "TargetOwned");
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.True(File.Exists(targetOlean));
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
    }

    [Fact]
    public void MissingCacheWithNonOleanBuildContentStillReproducesWithoutPublishing()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "unclear-build-target"));
        fixture.WritePartialReport("partial\n");
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.Equal("partial\n", fixture.PartialReportText);
        Assert.False(fixture.BuildCacheExists);
    }

    [Fact]
    public void MissingCacheDoesNotUseAColdDonorBuild()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "donor without project oleans\n");
        var target = AddWorktree(repository.Path, "cold-donor-build-target");
        Directory.CreateDirectory(Path.Combine(target, ".lake"));
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
    }

    [Fact]
    public void MissingCacheDoesNotUseAPinMismatchedDonor()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var target = AddWorktree(repository.Path, "pin-mismatched-missing-target");
        Directory.CreateDirectory(Path.Combine(target, ".lake"));
        File.WriteAllText(Path.Combine(repository.Path, "lean-toolchain"), "leanprover/lean4:v4.30.0\n");
        WriteCache(repository.Path, "wrong pin donor\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.Contains("pin bytes", result.Output, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void MissingCacheDoesNotUseAnUnstampedDonor()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "unstamped donor\n", stamp: false);
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var target = AddWorktree(repository.Path, "unstamped-missing-target");
        Directory.CreateDirectory(Path.Combine(target, ".lake"));
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.Contains("stamp", result.Output, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void MissingCacheDoesNotUseABusyDonor()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "busy donor\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var target = AddWorktree(repository.Path, "busy-missing-target");
        Directory.CreateDirectory(Path.Combine(target, ".lake"));
        using var busy = LeanCacheGuard.TryAcquireExclusive(Path.Combine(repository.Path, ".lake"));
        Assert.NotNull(busy);
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.Contains("busy", result.Output, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void MissingCacheDoesNotTreatProjectProbeFailureAsColdDonorEligibility()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var target = AddWorktree(repository.Path, "project-probe-failure-target");
        Directory.CreateDirectory(Path.Combine(target, ".lake"));
        var targetProjectRoot = Path.Combine(target, ".lake", "build", "lib", "lean");
        var probe = new DelegatingLeanCacheStateProbe(
            path => path == targetProjectRoot
                ? new OleanWarmthInspection(OleanWarmth.ProbeFailed, "injected enumeration failure")
                : FileSystemLeanCacheStateProbe.Instance.ProbeOleans(path));
        var cloner = new RecordingDirectoryCloner();

        var result = LeanCacheEnsureCommand.Run(
            repository.Path,
            ["--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner,
            removePartial: null,
            probe);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.Equal(1, probe.Count(targetProjectRoot));
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
    }

    [Fact]
    public void BuildPublicationRacePreservesNewTargetContentAndFallsBackInPlace()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "build-publication-race-target"));
        fixture.CreateLake();
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) => fixture.WriteRacedBuild("arrived during staging\n"),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Single(cloner.Invocations);
        Assert.Equal("arrived during staging\n", fixture.RacedBuildText);
        Assert.False(fixture.BuildCacheExists);
        Assert.True(fixture.CacheGetMarkerExists);
        Assert.Empty(fixture.BuildStageDirectories);
    }

    [Fact]
    public void EmptyBuildBecomingNonEmptyBeforeRmdirIsPreservedAndFallsBack()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "empty-build-rmdir-race-target"));
        fixture.CreateNestedEmptyBuild();
        var probe = new DelegatingLeanCacheStateProbe(
            FileSystemLeanCacheStateProbe.Instance.ProbeOleans,
            fixture.InspectContentRootAndPopulateBeforeRmdir);
        var cloner = new RecordingDirectoryCloner();

        var result = LeanCacheEnsureCommand.Run(
            repository.Path,
            ["--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner,
            removePartial: null,
            probe);

        Assert.True(result.Success, result.Error);
        Assert.Single(cloner.Invocations);
        Assert.Equal("arrived before rmdir\n", fixture.RacedBuildText);
        Assert.True(fixture.NestedEmptyDirectoryExists);
        Assert.False(fixture.BuildCacheExists);
        Assert.True(fixture.CacheGetMarkerExists);
    }

    [Fact]
    public void DonorStampChangingAfterMissingBuildStagingFallsBackWithoutPublishing()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var target = AddWorktree(repository.Path, "missing-build-stamp-race-target");
        Directory.CreateDirectory(Path.Combine(target, ".lake"));
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = static (source, _) =>
                File.Delete(LeanCacheStamp.PathFor(Path.GetDirectoryName(source)!)),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Single(cloner.Invocations);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.Empty(Directory.EnumerateDirectories(Path.Combine(target, ".lake"), "build.stage-*"));
    }

    [Fact]
    public void DonorLakeBecomingSymlinkAfterMissingBuildStagingFallsBackWithoutPublishing()
    {
        if (OperatingSystem.IsWindows()) return;

        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "missing-build-donor-symlink-race"));
        fixture.CreateLake();
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) => fixture.ReplaceDonorLakeWithSymlink(),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Single(cloner.Invocations);
        Assert.True(fixture.DonorLakeIsSymlink);
        Assert.False(fixture.BuildCacheExists);
        Assert.True(fixture.CacheGetMarkerExists);
        Assert.Contains("symlink", result.Output, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void FailedMissingDonorAttemptPreservesClonefileReceiptThroughFallback()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "missing-build-clone-receipt-target"));
        fixture.CreateLake();
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
                [new DirectoryCloneResult(false, false, 18, 1, "cross-device clone")]),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner { FailCopy = true },
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Single(cloner.Invocations);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(1, receipt.RootElement.GetProperty("clonefile_attempts").GetInt32());
        Assert.Equal(
            [18],
            receipt.RootElement.GetProperty("clonefile_errnos")
                .EnumerateArray()
                .Select(static value => value.GetInt32())
                .ToArray());
    }

    [Fact]
    public void StampWriteFailureRollsBackPublishedBuildAndNextEnsureCanCloneDonor()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "missing-build-stamp-write-failure"));
        fixture.CreateLake();

        var exception = Assert.Throws<LeanCacheProvisionException>(
            () => fixture.ProvisionWithFailingStampWrite(
                new RecordingWorktreeProcessRunner(),
                new RecordingDirectoryCloner()));

        Assert.Contains("injected stamp write failure", exception.Message, StringComparison.Ordinal);
        Assert.False(fixture.BuildDirectoryExists);
        Assert.False(fixture.TargetStampExists);

        var retryCloner = new RecordingDirectoryCloner();
        var retry = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            retryCloner);

        Assert.True(retry.Success, retry.Error);
        Assert.Single(retryCloner.Invocations);
        Assert.True(fixture.BuildCacheExists);
        Assert.True(fixture.StampMatches);
    }

    [Fact]
    public void DonorBecomingBusyAfterMissingBuildStagingFallsBackWithoutPublishing()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var target = AddWorktree(repository.Path, "missing-build-busy-race-target");
        Directory.CreateDirectory(Path.Combine(target, ".lake"));
        var runner = new RecordingWorktreeProcessRunner
        {
            BusyRoot = repository.Path,
            BusyOnlyAfterCopy = true,
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            new RecordingDirectoryCloner { FailureReason = "clonefile unavailable" });

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.Empty(Directory.EnumerateDirectories(Path.Combine(target, ".lake"), "build.stage-*"));
    }

    [Fact]
    public void TargetStampAppearingDuringStagingIsPreservedAndFailsClosed()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "missing-build-target-stamp-race"));
        fixture.CreateLake();
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) => fixture.WriteTargetStamp("raced stamp\n"),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.False(result.Success);
        Assert.Equal("raced stamp\n", fixture.TargetStampText);
        Assert.False(fixture.BuildDirectoryExists);
        Assert.False(fixture.CacheGetMarkerExists);
        Assert.Empty(fixture.BuildStageDirectories);
    }

    [Fact]
    public void ContentRootEnumerationFailureDoesNotEnterMissingDonorBranch()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var target = AddWorktree(repository.Path, "content-root-probe-failure-target");
        Directory.CreateDirectory(Path.Combine(target, ".lake"));
        var targetBuild = Path.Combine(target, ".lake", "build");
        var probe = new DelegatingLeanCacheStateProbe(
            FileSystemLeanCacheStateProbe.Instance.ProbeOleans,
            path => path == targetBuild
                ? new ContentRootInspection(false, "injected content enumeration failure")
                : FileSystemLeanCacheStateProbe.Instance.InspectContentRoot(path));
        var cloner = new RecordingDirectoryCloner();

        var result = LeanCacheEnsureCommand.Run(
            repository.Path,
            ["--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner,
            removePartial: null,
            probe);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        using var receipt = ParseReceipt(result.Output);
        Assert.Contains(
            "injected content enumeration failure",
            receipt.RootElement.GetProperty("reason").GetString()!,
            StringComparison.Ordinal);
    }

    [Fact]
    public void SymlinkTargetNeverEntersMissingDonorBranch()
    {
        if (OperatingSystem.IsWindows()) return;

        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var target = AddWorktree(repository.Path, "symlink-missing-target");
        var realLake = Path.Combine(target, "real-lake");
        Directory.CreateDirectory(realLake);
        Directory.CreateSymbolicLink(Path.Combine(target, ".lake"), realLake);
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.False(result.Success);
        Assert.Empty(cloner.Invocations);
        Assert.Contains("symlink", result.Error, StringComparison.OrdinalIgnoreCase);
    }

    private static string WriteProjectOlean(string root, string name)
    {
        var path = Path.Combine(root, ".lake", "build", "lib", "lean", name + ".olean");
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, name + "\n");
        return path;
    }

    private sealed class MissingStampDonorTargetFixture
    {
        private readonly string donorLake;
        private readonly string donorLakeBackup;
        private readonly string donorBuildRelativeRoot;
        private readonly string build;
        private readonly string nestedEmptyDirectory;
        private readonly string targetOwned;
        private readonly string partialReport;
        private readonly string racedBuild;
        private readonly string targetStamp;
        private int contentRootInspections;

        internal MissingStampDonorTargetFixture(string donorRepository, string target)
        {
            Target = target;
            Lake = Path.Combine(target, ".lake");
            DonorBuild = Path.Combine(
                LeanCacheGuard.PhysicalPath(donorRepository),
                ".lake",
                "build");
            donorLake = Path.GetDirectoryName(DonorBuild)!;
            donorLakeBackup = Path.Combine(donorRepository, "donor-lake-before-symlink");
            donorBuildRelativeRoot = Path.Combine(donorRepository, ".lake", "build");
            BuildStagePrefix = Path.Combine(Lake, "build.stage-");
            build = Path.Combine(Lake, "build");
            nestedEmptyDirectory = Path.Combine(build, "empty", "nested");
            targetOwned = Path.Combine(Lake, "target-owned.txt");
            partialReport = Path.Combine(build, "reports", "partial.json");
            racedBuild = Path.Combine(build, "raced.txt");
            targetStamp = LeanCacheStamp.PathFor(Lake);
        }

        internal string Target { get; }

        internal string Lake { get; }

        internal string DonorBuild { get; }

        internal string BuildStagePrefix { get; }

        internal string TargetOwnedText => File.ReadAllText(targetOwned);

        internal string PartialReportText => File.ReadAllText(partialReport);

        internal string RacedBuildText => File.ReadAllText(racedBuild);

        internal string TargetStampText => File.ReadAllText(targetStamp);

        internal bool TargetPackagesExist => Directory.Exists(Path.Combine(Lake, "packages"));

        internal bool BuildCacheExists => File.Exists(Path.Combine(Lake, "build", "cache.bin"));

        internal bool CacheGetMarkerExists => File.Exists(Path.Combine(Lake, "cache-get.marker"));

        internal bool BuildDirectoryExists => Directory.Exists(build);

        internal bool NestedEmptyDirectoryExists => Directory.Exists(nestedEmptyDirectory);

        internal bool TargetStampExists => File.Exists(targetStamp) || Directory.Exists(targetStamp);

        internal bool DonorLakeIsSymlink => File.GetAttributes(donorLake)
            .HasFlag(FileAttributes.ReparsePoint);

        internal IEnumerable<string> BuildStageDirectories =>
            Directory.EnumerateDirectories(Lake, "build.stage-*");

        internal bool StampMatches => LeanCacheStamp.Matches(Lake, ReadPins(Target), out _);

        internal void CreateLake() => Directory.CreateDirectory(Lake);

        internal void CreateNestedEmptyBuild() => Directory.CreateDirectory(nestedEmptyDirectory);

        internal void WriteTargetOwned(string contents) => File.WriteAllText(targetOwned, contents);

        internal void WritePartialReport(string contents)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(partialReport)!);
            File.WriteAllText(partialReport, contents);
        }

        internal void WriteRacedBuild(string contents)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(racedBuild)!);
            File.WriteAllText(racedBuild, contents);
        }

        internal void WriteTargetStamp(string contents) => File.WriteAllText(targetStamp, contents);

        internal ContentRootInspection InspectContentRootAndPopulateBeforeRmdir(string path)
        {
            if (string.Equals(path, build, StringComparison.Ordinal)
                && ++contentRootInspections == 2)
            {
                WriteRacedBuild("arrived before rmdir\n");
            }
            return FileSystemLeanCacheStateProbe.Instance.InspectContentRoot(path);
        }

        internal void ReplaceDonorLakeWithSymlink()
        {
            Directory.Move(donorLake, donorLakeBackup);
            Directory.CreateSymbolicLink(donorLake, donorLakeBackup);
        }

        internal LeanBuildProvisionAttempt ProvisionWithFailingStampWrite(
            IWorktreeProcessRunner runner,
            IDirectoryCloner cloner)
        {
            var pins = ReadPins(Target);
            using var selection = GitWorktreeInventory.SelectDonor(
                Target,
                pins,
                runner,
                FileSystemLeanCacheStateProbe.Instance,
                requireProjectWarm: true);
            using var writerGuard = LeanCacheWriterGuard.TryAcquire(Lake)
                ?? throw new InvalidOperationException("fixture could not acquire target writer guard");
            return LeanMissingBuildProvisioner.TryProvision(
                selection,
                Target,
                pins,
                runner,
                writerGuard,
                cloner,
                FileSystemLeanCacheStateProbe.Instance,
                wait: _ => { },
                writeStamp: static (_, _) => throw new IOException("injected stamp write failure"));
        }

        internal bool TryAcquireWriter()
        {
            using var concurrent = LeanCacheWriterGuard.TryAcquire(Lake);
            return concurrent is not null;
        }

        internal bool HasClonedDonorOlean(string donorOlean) =>
            File.Exists(Path.Combine(
                Lake,
                "build",
                Path.GetRelativePath(donorBuildRelativeRoot, donorOlean)));
    }
}

internal sealed class DelegatingLeanCacheStateProbe : ILeanCacheStateProbe
{
    private readonly Func<string, OleanWarmthInspection> probeOleans;
    private readonly Func<string, ContentRootInspection> inspectContentRoot;
    private readonly Dictionary<string, int> counts = new(StringComparer.Ordinal);

    internal DelegatingLeanCacheStateProbe(
        Func<string, OleanWarmthInspection> probeOleans,
        Func<string, ContentRootInspection>? inspectContentRoot = null)
    {
        this.probeOleans = probeOleans;
        this.inspectContentRoot = inspectContentRoot
            ?? FileSystemLeanCacheStateProbe.Instance.InspectContentRoot;
    }

    public OleanWarmthInspection ProbeOleans(string root)
    {
        counts[root] = Count(root) + 1;
        return probeOleans(root);
    }

    public ContentRootInspection InspectContentRoot(string root) =>
        inspectContentRoot(root);

    internal int Count(string root) => counts.GetValueOrDefault(root);
}
