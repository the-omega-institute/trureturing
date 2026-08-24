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
        var repository = fixture.RepositoryWorkingDirectory;
        var otherOwnedDirectories = fixture.OwnedWorkingDirectories
            .Where(path => !string.Equals(path, repository, StringComparison.Ordinal))
            .ToArray();
        var failure = new UnauthorizedAccessException("repository parent is not traversable");
        fixture.SetRepositoryAttributesReader(_ => throw failure);
        var probe = fixture.ProbeRepositoryDirectory();

        Assert.Equal(CleanLanesFixture.RepositoryDirectoryState.Indeterminate, probe.State);
        Assert.Same(failure, probe.Failure!.SourceException);

        try
        {
            var thrown = Assert.Throws<UnauthorizedAccessException>(() => fixture.Dispose());

            Assert.Same(failure, thrown);
            Assert.All(otherOwnedDirectories, path => Assert.False(Directory.Exists(path)));
            Assert.True(Directory.Exists(repository));
        }
        finally
        {
            fixture.RestoreRepositoryAttributesReader();
            fixture.Dispose();
        }
    }

    [Fact]
    public void DisposeDoesNotTreatRepositoryBelowBrokenParentSymlinkAsAbsent()
    {
        if (OperatingSystem.IsWindows()) return;

        using var scratchRoot = new TestScratchRoot();
        var fixture = new CleanLanesFixture(scratchRoot);
        var repository = fixture.RepositoryWorkingDirectory;
        var parkedRoot = scratchRoot.Path + ".parked";
        var missingTarget = scratchRoot.Path + ".missing";
        Directory.Move(scratchRoot.Path, parkedRoot);
        Directory.CreateSymbolicLink(scratchRoot.Path, missingTarget);

        try
        {
            var probe = fixture.ProbeRepositoryDirectory();

            Assert.Equal(CleanLanesFixture.RepositoryDirectoryState.Indeterminate, probe.State);
            var failure = Assert.IsType<DirectoryNotFoundException>(probe.Failure!.SourceException);
            var thrown = Assert.Throws<DirectoryNotFoundException>(() => fixture.Dispose());
            Assert.Equal(failure.Message, thrown.Message);

            var parkedRepository = Path.Combine(
                parkedRoot,
                Path.GetRelativePath(scratchRoot.Path, repository));
            Assert.True(Directory.Exists(parkedRepository));
        }
        finally
        {
            File.Delete(scratchRoot.Path);
            Directory.Move(parkedRoot, scratchRoot.Path);
            fixture.Dispose();
        }
    }

    [Fact]
    public void RepositoryDirectoryProbeTreatsBrokenRepositorySymlinkAsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;

        using var scratchRoot = new TestScratchRoot();
        var fixture = new CleanLanesFixture(scratchRoot);
        var repository = fixture.RepositoryWorkingDirectory;
        var parkedRepository = repository + ".parked";
        var missingTarget = repository + ".missing";
        Directory.Move(repository, parkedRepository);
        Directory.CreateSymbolicLink(repository, missingTarget);

        try
        {
            var probe = fixture.ProbeRepositoryDirectory();

            Assert.Equal(CleanLanesFixture.RepositoryDirectoryState.Indeterminate, probe.State);
            Assert.IsType<IOException>(probe.Failure!.SourceException);
        }
        finally
        {
            File.Delete(repository);
            Directory.Move(parkedRepository, repository);
            fixture.Dispose();
        }
    }

    [Fact]
    public void RepositoryDirectoryProbeTreatsPathTooLongAsIndeterminate()
    {
        var fixture = new CleanLanesFixture();
        var pathTooLong = Path.Combine(
            fixture.RepositoryWorkingDirectory,
            new string('a', 8192));
        fixture.SetRepositoryAttributesReader(_ => File.GetAttributes(pathTooLong));

        try
        {
            var probe = fixture.ProbeRepositoryDirectory();

            Assert.Equal(CleanLanesFixture.RepositoryDirectoryState.Indeterminate, probe.State);
            Assert.IsType<PathTooLongException>(probe.Failure!.SourceException);
        }
        finally
        {
            fixture.RestoreRepositoryAttributesReader();
            fixture.Dispose();
        }
    }
}
