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
    public void CapacityAuditRunUsesIndexedPathWhenTrackedWorkingTreeFileIsMissing()
    {
        using var repository = RepositoryWithTrackedFiles(
            RepositoryRules.DirectoryToleranceLimit + 1);
        File.Delete(Path.Combine(repository.Path, "Synthetic", "Bucket", "File0.cs"));

        var result = CapacityAuditCommand.Run([], repository.Path);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(
            $"CAPACITY_AUDIT Synthetic/Bucket: directory contains "
            + $"{RepositoryRules.DirectoryToleranceLimit + 1} files (admission limit "
            + $"{RepositoryRules.DirectoryFileLimit}, repository tolerance "
            + $"{RepositoryRules.DirectoryToleranceLimit}; split per CLAUDE.md 8)\n",
            result.Output);
        Assert.Empty(result.Error);
    }

    [Fact]
    public void CapacityAuditRunUsesIndexedBlobWhenWorkingTreeFileIsShortened()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init");
        var path = Path.Combine(repository.Path, "Synthetic", "Oversize.cs");
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, string.Join(
            '\n',
            Enumerable.Range(0, RepositoryRules.ArtifactHardLineLimit + 1)
                .Select(static index => $"line {index}")));
        ReviewRegressionTests.RunGit(repository.Path, "add", "--all");
        File.WriteAllText(path, "short\n");

        var result = CapacityAuditCommand.Run([], repository.Path);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(
            $"CAPACITY_AUDIT Synthetic/Oversize.cs: artifact spans "
            + $"{RepositoryRules.ArtifactHardLineLimit + 1} lines (hard limit "
            + $"{RepositoryRules.ArtifactHardLineLimit})\n",
            result.Output);
        Assert.Empty(result.Error);
    }

    [Fact]
    public void CliApplicationDispatchesCapacityAuditCleanIndexThroughProductionEnvironment()
    {
        using var repository = RepositoryWithTrackedFiles(RepositoryRules.DirectoryToleranceLimit);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["capacity-audit"],
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(0, exitCode);
        Assert.Empty(console.Output);
        Assert.Empty(console.Error);
    }

    [Fact]
    public void CliApplicationDispatchesCapacityAuditViolationThroughProductionEnvironment()
    {
        using var repository = RepositoryWithTrackedFiles(
            RepositoryRules.DirectoryToleranceLimit + 1);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["capacity-audit"],
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(1, exitCode);
        Assert.Equal(
            $"CAPACITY_AUDIT Synthetic/Bucket: directory contains "
            + $"{RepositoryRules.DirectoryToleranceLimit + 1} files (admission limit "
            + $"{RepositoryRules.DirectoryFileLimit}, repository tolerance "
            + $"{RepositoryRules.DirectoryToleranceLimit}; split per CLAUDE.md 8)\n",
            console.Output);
        Assert.Empty(console.Error);
    }

    [Fact]
    public void CapacityAuditRunReturnsTwoWhenIndexEnumerationFails()
    {
        var access = new StubCapacityAuditFileAccess(
            enumerate: _ => throw new InvalidOperationException("synthetic index failure"),
            readFiles: (_, _) => throw new InvalidOperationException("unexpected read"));

        var result = CapacityAuditCommand.Run([], "/synthetic", access);

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.Output);
        Assert.Equal(
            "INFRASTRUCTURE_FAILURE capacity-audit: stage=index-enumeration "
            + "synthetic index failure\n",
            result.Error);
    }

    [Fact]
    public void CapacityAuditRunReturnsTwoWhenTrackedFileReadFails()
    {
        var access = new StubCapacityAuditFileAccess(
            enumerate: _ => [new CapacityAuditIndexEntry("Synthetic/Bucket/File.cs", "object-id")],
            readFiles: (_, _) => throw new IOException("synthetic read failure"));

        var result = CapacityAuditCommand.Run([], "/synthetic", access);

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.Output);
        Assert.Equal(
            "INFRASTRUCTURE_FAILURE capacity-audit: stage=file-read synthetic read failure\n",
            result.Error);
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
        Func<string, IReadOnlyList<CapacityAuditIndexEntry>> enumerate,
        Func<
            string,
            IReadOnlyList<CapacityAuditIndexEntry>,
            IReadOnlyList<(string RelativePath, string Text)>> readFiles) : ICapacityAuditFileAccess
    {
        public IReadOnlyList<CapacityAuditIndexEntry> Enumerate(string repositoryRoot) =>
            enumerate(repositoryRoot);

        public IReadOnlyList<(string RelativePath, string Text)> ReadFiles(
            string repositoryRoot,
            IReadOnlyList<CapacityAuditIndexEntry> indexedFiles) =>
            readFiles(repositoryRoot, indexedFiles);
    }
}
