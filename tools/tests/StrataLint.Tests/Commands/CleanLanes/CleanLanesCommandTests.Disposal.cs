namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void DisposeReleasesRemainingOwnedDirectoriesWhenOneWasAlreadyDeleted()
    {
        var fixture = new CleanLanesFixture();
        var repository = fixture.OwnedWorkingDirectory(
            CleanLanesFixture.OwnedDirectory.Repository);
        var ownedDirectories = fixture.OwnedWorkingDirectories;
        Directory.Delete(repository, recursive: true);
        Assert.False(Directory.Exists(repository));

        fixture.Dispose();

        Assert.All(ownedDirectories, path => Assert.False(Directory.Exists(path)));
    }

    [Theory]
    [InlineData((int)CleanLanesFixture.OwnedDirectory.Temporary)]
    [InlineData((int)CleanLanesFixture.OwnedDirectory.Worktrees)]
    [InlineData((int)CleanLanesFixture.OwnedDirectory.Repository)]
    public void DisposeContinuesAfterAnyOwnedDirectoryReleaseFails(int failingDirectoryValue)
    {
        var failingDirectory = (CleanLanesFixture.OwnedDirectory)failingDirectoryValue;
        var fixture = new CleanLanesFixture();
        var failure = new InvalidOperationException($"cannot release {failingDirectory}");
        fixture.SetOwnedDirectoryDisposer(failingDirectory, () => throw failure);

        try
        {
            var thrown = Assert.Throws<InvalidOperationException>(() => fixture.Dispose());

            Assert.Same(failure, thrown);
            foreach (var directory in Enum.GetValues<CleanLanesFixture.OwnedDirectory>())
            {
                Assert.Equal(
                    directory == failingDirectory,
                    Directory.Exists(fixture.OwnedWorkingDirectory(directory)));
            }
        }
        finally
        {
            fixture.RestoreOwnedDirectoryDisposer(failingDirectory);
            fixture.Dispose();
        }
    }

    [Fact]
    public void DisposeAggregatesAllOwnedDirectoryFailuresInReleaseOrder()
    {
        var fixture = new CleanLanesFixture();
        var releaseOrder = new List<CleanLanesFixture.OwnedDirectory>();
        var temporaryFailure = new IOException("temporary directory release failed");
        var worktreesFailure = new UnauthorizedAccessException("worktree directory release failed");
        var repositoryFailure = new InvalidOperationException("repository directory release failed");
        fixture.SetOwnedDirectoryDisposer(
            CleanLanesFixture.OwnedDirectory.Temporary,
            () =>
            {
                releaseOrder.Add(CleanLanesFixture.OwnedDirectory.Temporary);
                throw temporaryFailure;
            });
        fixture.SetOwnedDirectoryDisposer(
            CleanLanesFixture.OwnedDirectory.Worktrees,
            () =>
            {
                releaseOrder.Add(CleanLanesFixture.OwnedDirectory.Worktrees);
                throw worktreesFailure;
            });
        fixture.SetOwnedDirectoryDisposer(
            CleanLanesFixture.OwnedDirectory.Repository,
            () =>
            {
                releaseOrder.Add(CleanLanesFixture.OwnedDirectory.Repository);
                throw repositoryFailure;
            });

        try
        {
            var aggregate = Assert.Throws<AggregateException>(() => fixture.Dispose());

            Assert.Equal(
                [
                    CleanLanesFixture.OwnedDirectory.Temporary,
                    CleanLanesFixture.OwnedDirectory.Worktrees,
                    CleanLanesFixture.OwnedDirectory.Repository,
                ],
                releaseOrder);
            Assert.Equal(
                [temporaryFailure, worktreesFailure, repositoryFailure],
                aggregate.InnerExceptions);
        }
        finally
        {
            fixture.RestoreOwnedDirectoryDisposer(CleanLanesFixture.OwnedDirectory.Temporary);
            fixture.RestoreOwnedDirectoryDisposer(CleanLanesFixture.OwnedDirectory.Worktrees);
            fixture.RestoreOwnedDirectoryDisposer(CleanLanesFixture.OwnedDirectory.Repository);
            fixture.Dispose();
        }
    }

    [Fact]
    public void DisposeRethrowsSingleOwnedDirectoryFailureFromOriginalThrowSite()
    {
        var fixture = new CleanLanesFixture();
        var failure = new InvalidOperationException("temporary directory release failed");
        fixture.SetOwnedDirectoryDisposer(
            CleanLanesFixture.OwnedDirectory.Temporary,
            () => ThrowOwnedDirectoryReleaseFailure(failure));

        try
        {
            var thrown = Assert.Throws<InvalidOperationException>(() => fixture.Dispose());

            Assert.Same(failure, thrown);
            Assert.Contains(
                nameof(ThrowOwnedDirectoryReleaseFailure),
                thrown.ToString(),
                StringComparison.Ordinal);
        }
        finally
        {
            fixture.RestoreOwnedDirectoryDisposer(CleanLanesFixture.OwnedDirectory.Temporary);
            fixture.Dispose();
        }
    }

    [Fact]
    public void DisposeAttemptsOwnedRepositoryReleaseWithoutTouchingRepositoryParkedBehindBrokenParentSymlink()
    {
        if (OperatingSystem.IsWindows()) return;

        using var scratchRoot = new TestScratchRoot();
        var fixture = new CleanLanesFixture(scratchRoot);
        var repository = fixture.OwnedWorkingDirectory(
            CleanLanesFixture.OwnedDirectory.Repository);
        var parkedRoot = scratchRoot.Path + ".parked";
        var missingTarget = scratchRoot.Path + ".missing";
        var parkedRepository = Path.Combine(
            parkedRoot,
            Path.GetRelativePath(scratchRoot.Path, repository));
        var repositoryReleaseAttempts = 0;
        fixture.SetOwnedDirectoryDisposer(
            CleanLanesFixture.OwnedDirectory.Repository,
            () =>
            {
                repositoryReleaseAttempts++;
                TestDirectoryCleanup.DeleteRecursively(repository);
            });
        Directory.Move(scratchRoot.Path, parkedRoot);
        Directory.CreateSymbolicLink(scratchRoot.Path, missingTarget);

        try
        {
            fixture.Dispose();

            Assert.Equal(1, repositoryReleaseAttempts);
            Assert.True(Directory.Exists(parkedRepository));
        }
        finally
        {
            File.Delete(scratchRoot.Path);
            Directory.Move(parkedRoot, scratchRoot.Path);
            fixture.RestoreOwnedDirectoryDisposer(CleanLanesFixture.OwnedDirectory.Repository);
            fixture.Dispose();
        }
    }

    [Fact]
    public void DisposeAttemptsOwnedRepositoryReleaseWithoutTouchingRenamedRepositoryLeaf()
    {
        var fixture = new CleanLanesFixture();
        var repository = fixture.OwnedWorkingDirectory(
            CleanLanesFixture.OwnedDirectory.Repository);
        var parkedRepository = repository + ".parked";
        var repositoryReleaseAttempts = 0;
        fixture.SetOwnedDirectoryDisposer(
            CleanLanesFixture.OwnedDirectory.Repository,
            () =>
            {
                repositoryReleaseAttempts++;
                TestDirectoryCleanup.DeleteRecursively(repository);
            });
        Directory.Move(repository, parkedRepository);

        try
        {
            fixture.Dispose();

            Assert.Equal(1, repositoryReleaseAttempts);
            Assert.True(Directory.Exists(parkedRepository));
        }
        finally
        {
            Directory.Move(parkedRepository, repository);
            fixture.RestoreOwnedDirectoryDisposer(CleanLanesFixture.OwnedDirectory.Repository);
            fixture.Dispose();
        }
    }

    [System.Runtime.CompilerServices.MethodImpl(
        System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static void ThrowOwnedDirectoryReleaseFailure(Exception failure) => throw failure;
}
