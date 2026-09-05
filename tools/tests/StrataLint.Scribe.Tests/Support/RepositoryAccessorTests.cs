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
    public void DiscoversTheNearestRootUsingTheRequestedMarkerCondition()
    {
        var root = TemporaryFileSystem.Directory.CreateTempSubdirectory("repository-marker-");
        var nested = TemporaryFileSystem.Directory.CreateDirectory(
            Path.Combine(root.FullName, "one", "two"));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root.FullName, "global.json"), "{}");
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(root.FullName, "Blueprint"));

        try
        {
            var repository = RepositoryAccessor.DiscoverFromDirectory(
                nested.FullName,
                RepositoryRootCriterion.GlobalJsonAndBlueprintDirectoryNotFound);

            Assert.Equal(root.FullName, repository.Root.FullPath);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root.FullName, recursive: true);
        }
    }

    [Fact]
    public void DiscoveryPreservesTheRequestedFailureExceptionType()
    {
        var root = TemporaryFileSystem.Directory.CreateTempSubdirectory("repository-missing-");

        try
        {
            Assert.Throws<InvalidOperationException>(() => RepositoryAccessor.DiscoverFromDirectory(
                root.FullName,
                RepositoryRootCriterion.LakefileInvalidOperation));
            Assert.Throws<DirectoryNotFoundException>(() => RepositoryAccessor.DiscoverFromDirectory(
                root.FullName,
                RepositoryRootCriterion.ClaudeDirectoryNotFound));
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root.FullName, recursive: true);
        }
    }

    [Fact]
    public void RecursiveEnumerationIncludesUntrackedFiles()
    {
        var root = TemporaryFileSystem.Directory.CreateTempSubdirectory("repository-files-");
        var nested = TemporaryFileSystem.Directory.CreateDirectory(
            Path.Combine(root.FullName, "Blueprint", "Nested"));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(root.FullName, RootMarkerPath), "root");
        TemporaryFileSystem.File.WriteAllText(Path.Combine(nested.FullName, "untracked.scribe.cs"), "fixture");

        try
        {
            var repository = RepositoryAccessor.DiscoverFromDirectory(
                nested.FullName,
                RepositoryRootCriterion.ClaudeDirectoryNotFound);
            var paths = repository.EnumerateFiles(
                RepositoryRelativePath.Create("Blueprint"),
                "*.scribe.cs");

            Assert.Contains(
                RepositoryRelativePath.Create("Blueprint/Nested/untracked.scribe.cs"),
                paths);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(root.FullName, recursive: true);
        }
    }

    [Fact]
    public void ReadsTypedRepositoryRelativePaths()
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound);
        var path = RepositoryRelativePath.Create(RootMarkerPath);

        Assert.NotEmpty(repository.ReadAllText(path));
    }

    [Fact]
    public void TemporaryFileSystemRejectsRepositoryPaths()
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound);
        var repositoryPath = repository.GetFullPath(RepositoryRelativePath.Create(RootMarkerPath));

        Assert.Throws<ArgumentException>(() => TemporaryFileSystem.File.ReadAllText(repositoryPath));
    }
}
