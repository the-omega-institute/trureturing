namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void DisposeSkipsGitInventoryWhenRepositoryDirectoryIsConfirmedAbsent()
    {
        var fixture = new CleanLanesFixture();
        var repository = fixture.RepositoryWorkingDirectory;
        var ownedDirectories = fixture.OwnedWorkingDirectories;
        Directory.Delete(repository, recursive: true);

        Assert.Equal(
            CleanLanesFixture.RepositoryDirectoryState.Absent,
            fixture.ProbeRepositoryDirectory().State);

        fixture.Dispose();

        Assert.All(ownedDirectories, path => Assert.False(Directory.Exists(path)));
    }

    [Fact]
    public void DisposeCharacterizesGitStartFailureWhenRepositoryDirectoryExists()
    {
        if (OperatingSystem.IsWindows()) return;

        var fixture = new CleanLanesFixture();
        var repository = fixture.RepositoryWorkingDirectory;
        var originalMode = File.GetUnixFileMode(repository);
        Assert.Equal(
            CleanLanesFixture.RepositoryDirectoryState.Present,
            fixture.ProbeRepositoryDirectory().State);
        try
        {
            File.SetUnixFileMode(repository, UnixFileMode.None);
            Assert.True(Directory.Exists(repository));

            Assert.Throws<System.ComponentModel.Win32Exception>(() => fixture.Dispose());
        }
        finally
        {
            File.SetUnixFileMode(repository, originalMode);
            fixture.Dispose();
        }
    }

    [Fact]
    public void DisposeDoesNotTreatIndeterminateRepositoryDirectoryProbeAsAbsent()
    {
        var fixture = new CleanLanesFixture();
        var failure = new UnauthorizedAccessException("repository parent is not traversable");
        fixture.SetRepositoryAttributesReader(_ => throw failure);
        var probe = fixture.ProbeRepositoryDirectory();

        Assert.Equal(CleanLanesFixture.RepositoryDirectoryState.Indeterminate, probe.State);
        Assert.Same(failure, probe.Failure!.SourceException);

        try
        {
            var thrown = Assert.Throws<UnauthorizedAccessException>(() => fixture.Dispose());

            Assert.Same(failure, thrown);
        }
        finally
        {
            fixture.RestoreRepositoryAttributesReader();
            fixture.Dispose();
        }
    }
}
