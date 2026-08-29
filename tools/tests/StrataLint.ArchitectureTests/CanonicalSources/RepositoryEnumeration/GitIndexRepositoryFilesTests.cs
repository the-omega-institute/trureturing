using StrataLint.Engine;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class GitIndexRepositoryFilesTests
{
    private const string TailBoundsPath =
        "D5/S0/Asymptotics/Bonferroni/TailBounds.lean";

    [Fact]
    public void EnumerateReturnsEveryKnownTrackedRegularFile()
    {
        using var repository = new TemporaryDirectory();
        string[] expected =
        [
            TailBoundsPath,
            "tools/StrataLint.Engine/Snapshot/GitIndexRepositoryFiles.cs",
        ];
        foreach (var relativePath in expected)
        {
            WriteFile(repository.Path, relativePath);
        }

        Assert.Equal(0, RunGit(repository.Path, "init").ExitCode);
        Assert.Equal(0, RunGit(repository.Path, "add", "--all").ExitCode);
        WriteFile(repository.Path, "untracked.txt");

        var actual = StrataLint.Engine.GitIndexRepositoryFiles.Enumerate(repository.Path)
            .Select(static file => file.RelativePath)
            .ToArray();

        Assert.Equal(expected, actual);
    }

    private static void WriteFile(string repositoryRoot, string relativePath)
    {
        var fullPath = Path.Combine(
            repositoryRoot,
            relativePath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        File.WriteAllText(fullPath, "fixture\n");
    }

    private static ProcessOutput RunGit(string repositoryRoot, params string[] arguments) =>
        TestProcessRunner.Run(
            "git",
            arguments,
            repositoryRoot,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);
}
