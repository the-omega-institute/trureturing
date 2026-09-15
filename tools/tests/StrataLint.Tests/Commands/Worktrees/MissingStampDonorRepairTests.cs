using StrataLint.Cli;

namespace StrataLint.Tests;

// Repair-path coverage for the missing-build donor branch: what must not re-enter that
// branch, and what happens when a published build fails to get its stamp. Split out of
// MissingStampDonorTests.cs, which had reached the SL-003 line limit.
public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void MissingCacheWithEmptyBuildRootReproducesWithoutEnteringDonorPath()
    {
        // Pins the downgraded content-root predicate. "Clear" means the build root is absent,
        // not "absent or empty": an existing but empty build root is still someone else's
        // directory, and treating it as clear re-opens a publish window this path must not
        // have. Widening the predicate back to "absent or empty" must turn this test red.
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
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(cloner.Invocations);
        Assert.Empty(fixture.BuildStageDirectories);
        Assert.False(fixture.BuildCacheExists);
        Assert.True(fixture.BuildDirectoryExists);
    }

    [Fact]
    public void StampWriteFailurePreservesPublishedBuildAndNextEnsureRepairsStampInPlace()
    {
        using var repository = new TemporaryDirectory();
        // The repair path runs the producer in place rather than cloning the donor again,
        // so this test now needs the shared mathlib cache the producer consumes.
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

        // The published build stays. This provisioner has no ability to delete the target
        // build root, so a stamp write failure leaves a published-but-unstamped tree.
        Assert.True(fixture.BuildDirectoryExists);
        Assert.True(fixture.BuildCacheExists);
        Assert.False(fixture.TargetStampExists);

        var retryCloner = new RecordingDirectoryCloner();
        var retry = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", fixture.Target],
            new RecordingWorktreeProcessRunner(),
            retryCloner);

        // That state is self-healing without re-entering the donor path: the content root is
        // no longer clear, so ensure falls through to ReproduceExisting, which runs the
        // producer in place and publishes the stamp over the preserved build.
        Assert.True(retry.Success, retry.Error);
        Assert.Empty(retryCloner.Invocations);
        Assert.True(fixture.BuildCacheExists);
        Assert.True(fixture.StampMatches);
    }
}
