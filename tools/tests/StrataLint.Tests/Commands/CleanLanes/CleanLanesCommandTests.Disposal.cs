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
    public void DisposeAggregatesOwnedDirectoryFailuresWithoutMaskingTheFirst()
    {
        var fixture = new CleanLanesFixture();
        var first = new IOException("temporary directory release failed");
        var second = new UnauthorizedAccessException("worktree directory release failed");
        fixture.SetOwnedDirectoryDisposer(
            CleanLanesFixture.OwnedDirectory.Temporary,
            () => throw first);
        fixture.SetOwnedDirectoryDisposer(
            CleanLanesFixture.OwnedDirectory.Worktrees,
            () => throw second);

        try
        {
            var aggregate = Assert.Throws<AggregateException>(() => fixture.Dispose());

            Assert.Equal([first, second], aggregate.InnerExceptions);
            Assert.False(Directory.Exists(fixture.OwnedWorkingDirectory(
                CleanLanesFixture.OwnedDirectory.Repository)));
        }
        finally
        {
            fixture.RestoreOwnedDirectoryDisposer(CleanLanesFixture.OwnedDirectory.Temporary);
            fixture.RestoreOwnedDirectoryDisposer(CleanLanesFixture.OwnedDirectory.Worktrees);
            fixture.Dispose();
        }
    }
}
