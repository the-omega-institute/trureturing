using System.Text;
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
    public void CapacityAuditReadsCompleteIndexAcrossBoundedBatches()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init");
        var contents = new[]
        {
            string.Concat(Enumerable.Repeat("alpha\n", 80)),
            string.Concat(Enumerable.Repeat("alpha\n", 80)),
            string.Concat(Enumerable.Repeat("omega\n", 80)),
        };
        for (var index = 0; index < contents.Length; index++)
        {
            File.WriteAllText(Path.Combine(repository.Path, $"file{index}.cs"), contents[index]);
        }
        ReviewRegressionTests.RunGit(repository.Path, "add", "--all");
        File.Delete(Path.Combine(repository.Path, "file0.cs"));
        File.WriteAllText(Path.Combine(repository.Path, "file1.cs"), "unstaged replacement");
        var indexed = ProductionCapacityAuditFileAccess.Instance.Enumerate(repository.Path);
        Assert.Equal(indexed[0].ObjectId, indexed[1].ObjectId);
        var batches = 0;
        var totalOutputBytes = 0;

        var files = ProductionCapacityAuditFileAccess.ReadFiles(indexed, (arguments, limit, input) =>
        {
            var result = BoundedProcessRunner.Run("git", arguments, repository.Path,
                TimeSpan.FromSeconds(120), limit, input);
            if (arguments.Contains("--batch"))
            {
                Assert.Equal(700, limit);
                Assert.InRange(result.StandardOutput.Length, 1, limit);
                batches++;
                totalOutputBytes += result.StandardOutput.Length;
            }
            return result;
        }, maximumBatchBytes: 700);

        Assert.Equal(3, batches);
        Assert.True(totalOutputBytes > 700);
        Assert.Equal(indexed.Select(static file => file.RelativePath), files.Select(static file => file.RelativePath));
        Assert.Equal(contents, files.Select(static file => file.Text));
    }

    [Fact]
    public void CapacityAuditRejectsAnOversizedIndexedBlobBeforeReadingItsBody()
    {
        var file = new CapacityAuditIndexEntry("oversize.cs", new string('a', 40));
        var calls = 0;

        var error = Assert.Throws<InvalidOperationException>(() =>
            ProductionCapacityAuditFileAccess.ReadFiles([file], (arguments, _, _) =>
            {
                Assert.Contains("--batch-check", arguments);
                calls++;
                return new ProcessOutput(0, Encoding.ASCII.GetBytes($"{file.ObjectId} blob 100\n"), []);
            }, maximumBatchBytes: 100));

        Assert.Equal(1, calls);
        Assert.Contains("indexed blob exceeds", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("extra")]
    [InlineData("wrong-object")]
    [InlineData("wrong-type")]
    [InlineData("negative-size")]
    public void CapacityAuditRejectsInvalidSizeInventory(string fault)
    {
        var file = new CapacityAuditIndexEntry("input.cs", new string('a', 40));
        var line = $"{file.ObjectId} blob 1\n";
        var output = fault switch
        {
            "missing" => string.Empty,
            "extra" => line + line,
            "wrong-object" => new string('b', 40) + " blob 1\n",
            "wrong-type" => $"{file.ObjectId} tree 1\n",
            "negative-size" => $"{file.ObjectId} blob -1\n",
            _ => throw new InvalidOperationException(fault),
        };

        Assert.Throws<InvalidOperationException>(() =>
            ProductionCapacityAuditFileAccess.ReadFiles([file], (arguments, _, _) =>
            {
                Assert.Contains("--batch-check", arguments);
                return new ProcessOutput(0, Encoding.ASCII.GetBytes(output), []);
            }, maximumBatchBytes: 100));
    }

    [Fact]
    public void CapacityAuditRejectsCorruptionInALaterBatch()
    {
        CapacityAuditIndexEntry[] indexed =
        [new("first.cs", new string('a', 40)), new("second.cs", new string('b', 40))];
        var bodyCalls = 0;

        var error = Assert.Throws<InvalidOperationException>(() =>
            ProductionCapacityAuditFileAccess.ReadFiles(indexed, (arguments, _, input) =>
            {
                if (arguments.Contains("--batch-check"))
                {
                    return new ProcessOutput(0, Encoding.ASCII.GetBytes(string.Concat(
                        indexed.Select(static file => $"{file.ObjectId} blob 50\n"))), []);
                }
                bodyCalls++;
                var objectId = Encoding.ASCII.GetString(input.Span).TrimEnd('\n');
                if (bodyCalls == 2) objectId = new string('c', 40);
                return new ProcessOutput(0,
                    Encoding.ASCII.GetBytes($"{objectId} blob 50\n" + new string('x', 50) + "\n"), []);
            }, maximumBatchBytes: 100));

        Assert.Equal(2, bodyCalls);
        Assert.Contains("invalid metadata for second.cs", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(2)]
    public void CapacityAuditRejectsChangedSizeForTheSameIndexedObject(int bodySize)
    {
        var file = new CapacityAuditIndexEntry("input.cs", new string('a', 40));

        var error = Assert.Throws<InvalidOperationException>(() =>
            ProductionCapacityAuditFileAccess.ReadFiles([file], (arguments, _, _) =>
            {
                var output = arguments.Contains("--batch-check")
                    ? $"{file.ObjectId} blob 1\n"
                    : $"{file.ObjectId} blob {bodySize}\n" + new string('x', bodySize) + "\n";
                return new ProcessOutput(0, Encoding.ASCII.GetBytes(output), []);
            }, maximumBatchBytes: 100));

        Assert.Contains("indexed blob size changed for input.cs", error.Message, StringComparison.Ordinal);
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
