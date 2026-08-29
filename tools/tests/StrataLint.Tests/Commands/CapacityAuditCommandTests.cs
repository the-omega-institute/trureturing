using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CapacityAuditCommandTests
{
    [Fact]
    public void CapacityAuditAllowsAtRepositoryTolerance()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryToleranceLimit)
            .Select(static index => ($"Synthetic/Bucket/File{index}.cs", "x"))
            .ToArray();

        var findings = RepositoryCapacityAudit.InspectFiles(files);

        Assert.Empty(findings);
    }

    [Fact]
    public void CapacityAuditRejectsPastRepositoryTolerance()
    {
        var files = Enumerable.Range(0, RepositoryRules.DirectoryToleranceLimit + 1)
            .Select(static index => ($"Synthetic/Bucket/File{index}.cs", "x"))
            .ToArray();

        var finding = Assert.Single(RepositoryCapacityAudit.InspectFiles(files));

        Assert.Equal("Synthetic/Bucket", finding.Path);
        Assert.Contains("tolerance", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CapacityAuditRunWithNoArgumentsReturnsZeroForTrackedRepositoryWithinTolerance()
    {
        using var repository = RepositoryWithTrackedFiles(RepositoryRules.DirectoryToleranceLimit);

        var result = CapacityAuditCommand.Run([], repository.Path);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.Output);
        Assert.Empty(result.Error);
    }

    [Fact]
    public void CapacityAuditRunWithNoArgumentsReturnsOneForTrackedRepositoryPastTolerance()
    {
        using var repository = RepositoryWithTrackedFiles(
            RepositoryRules.DirectoryToleranceLimit + 1);

        var result = CapacityAuditCommand.Run([], repository.Path);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains("CAPACITY_AUDIT Synthetic/Bucket", result.Output, StringComparison.Ordinal);
        Assert.Empty(result.Error);
    }

    [Fact]
    public void CapacityAuditRunReturnsTwoWhenIndexEnumerationFails()
    {
        var access = new StubCapacityAuditFileAccess(
            enumerate: _ => throw new InvalidOperationException("synthetic index failure"),
            readAllText: _ => throw new InvalidOperationException("unexpected read"));

        var result = CapacityAuditCommand.Run([], "/synthetic", access);

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.Output);
        Assert.Contains("synthetic index failure", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void CapacityAuditRunReturnsTwoWhenTrackedFileReadFails()
    {
        var access = new StubCapacityAuditFileAccess(
            enumerate: _ => [("Synthetic/Bucket/File.cs", "/synthetic/File.cs")],
            readAllText: _ => throw new IOException("synthetic read failure"));

        var result = CapacityAuditCommand.Run([], "/synthetic", access);

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.Output);
        Assert.Contains("synthetic read failure", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void CapacityAuditRejectsEveryAuthoritativeContextArgument()
    {
        using var repository = RepositoryWithTrackedFiles(0);
        string[] arguments =
        [
            "--event=push",
            "--tier=repository",
            "--branch=dev",
            "--revision=HEAD",
            "--base=HEAD^1",
        ];

        foreach (var argument in arguments)
        {
            var result = CapacityAuditCommand.Run([argument], repository.Path);

            Assert.Equal(2, result.ExitCode);
            Assert.Empty(result.Output);
            Assert.Equal("USAGE: StrataLint capacity-audit\n", result.Error);
        }
    }

    private static TemporaryDirectory RepositoryWithTrackedFiles(int count)
    {
        var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init");
        for (var index = 0; index < count; index++)
        {
            var path = Path.Combine(repository.Path, "Synthetic", "Bucket", $"File{index}.cs");
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, "x\n");
        }

        ReviewRegressionTests.RunGit(repository.Path, "add", "--all");
        return repository;
    }

    private sealed class StubCapacityAuditFileAccess(
        Func<string, IReadOnlyList<(string RelativePath, string FullPath)>> enumerate,
        Func<string, string> readAllText) : ICapacityAuditFileAccess
    {
        public IReadOnlyList<(string RelativePath, string FullPath)> Enumerate(string repositoryRoot) =>
            enumerate(repositoryRoot);

        public string ReadAllText(string fullPath) => readAllText(fullPath);
    }
}
