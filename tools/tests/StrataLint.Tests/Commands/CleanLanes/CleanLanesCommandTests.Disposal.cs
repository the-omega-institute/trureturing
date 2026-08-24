namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void DisposeSkipsGitInventoryWhenRepositoryWorkingDirectoryNoLongerExists()
    {
        var fixture = new CleanLanesFixture();
        var repository = fixture.RepositoryWorkingDirectory;
        Directory.Delete(repository, recursive: true);

        fixture.Dispose();

        Assert.False(Directory.Exists(repository));
    }

    [Fact]
    public void DisposeStillSurfacesGitStartFailureWhenRepositoryDirectoryExists()
    {
        if (OperatingSystem.IsWindows()) return;

        var fixture = new CleanLanesFixture();
        var repository = fixture.RepositoryWorkingDirectory;
        var originalMode = File.GetUnixFileMode(repository);
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
}
