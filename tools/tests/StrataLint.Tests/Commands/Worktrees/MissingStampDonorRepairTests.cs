using StrataLint.Cli;

namespace StrataLint.Tests;

// Repair-path coverage for the missing-build donor branch: what must not re-enter that
// branch, and what happens when a published build fails to get its stamp. Split out of
// MissingStampDonorTests.cs, which had reached the SL-003 line limit.
public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void MissingStampWithEmptyBuildRootAddsBuildAndPackagesWithoutReplacingLake()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "warm donor build\n");
        _ = WriteProjectOlean(repository.Path, "DonorWarm");
        var fixture = new MissingStampDonorTargetFixture(
            repository.Path,
            AddWorktree(repository.Path, "empty-build-root-target"));
        fixture.CreateLake();
        fixture.CreateEmptyBuildRoot();
        fixture.WriteTargetOwned("retained empty-build lane\n");
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Equal(2, cloner.Invocations.Count);
        Assert.Equal("retained empty-build lane\n", fixture.TargetOwnedText);
        Assert.True(fixture.TargetPackagesExist);
        Assert.Empty(fixture.BuildStageDirectories);
        Assert.True(fixture.BuildCacheExists);
        Assert.True(fixture.BuildDirectoryExists);
    }

    [Fact]
    public void StampWriteFailurePreservesPublishedBuildAndNextEnsureReplacesFromWarmMain()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
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

        // The overlay provisioner leaves a published-but-unstamped tree when stamp writing fails.
        Assert.True(fixture.BuildDirectoryExists);
        Assert.True(fixture.BuildCacheExists);
        Assert.False(fixture.TargetStampExists);

        var retryCloner = new RecordingDirectoryCloner();
        var retry = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            retryCloner);

        // A linked lane with a missing stamp provisions only from the warm main checkout.
        Assert.True(retry.Success, retry.Error);
        Assert.Single(retryCloner.Invocations);
        Assert.True(fixture.BuildCacheExists);
        Assert.True(fixture.StampMatches);
    }
}
