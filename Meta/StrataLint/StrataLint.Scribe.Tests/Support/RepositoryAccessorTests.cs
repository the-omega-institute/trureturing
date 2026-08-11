namespace StrataLint.Scribe.Tests;

public sealed class RepositoryAccessorTests
{
    private const string RootMarkerPath = "CLAUDE.md";
    [Theory]
    [InlineData("/absolute")]
    [InlineData("../escape")]
    [InlineData("nested/../../escape")]
    public void RepositoryRelativePathRejectsPathsOutsideTheRepository(string value)
    {
        Assert.Throws<ArgumentException>(() => RepositoryRelativePath.Create(value));
    }

    [Fact]
    public void ReadsRecordTypedRepositoryRelativePaths()
    {
        var repository = RepositoryAccessor.Discover();
        var path = RepositoryRelativePath.Create(RootMarkerPath);

        Assert.NotEmpty(repository.ReadAllText(path));
        Assert.Contains(path, repository.AccessedPaths);
    }

    [Fact]
    public void GitIndexEnumerationRecordsTheEnumeratedDirectory()
    {
        var repository = RepositoryAccessor.Discover();
        var directory = RepositoryRelativePath.Create("Blueprint");

        Assert.NotEmpty(repository.EnumerateFiles(directory, "*.scribe.cs"));
        Assert.Contains(directory, repository.AccessedPaths);
    }
}
