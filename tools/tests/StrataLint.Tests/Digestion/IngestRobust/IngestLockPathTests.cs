using StrataLint.Cli;

namespace StrataLint.Tests;

[Collection("Ingest lock environment")]
public sealed class IngestLockPathTests
{
    [Fact]
    public void IngestLockPath_DirectoryAndFileFormsResolveToSameWorktreeDirectory()
    {
        using var primary = new TemporaryDirectory();
        using var linked = new TemporaryDirectory();
        var gitDirectory = Path.Combine(primary.Path, ".git");
        var directoryPath = IngestCommand.ReportFreeCommitLockPath(
            GitWorktreeDirectory.ResolvePath(primary.Path, null));
        foreach (var pointer in new[] { gitDirectory, Path.GetRelativePath(linked.Path, gitDirectory) })
        {
            var filePath = IngestCommand.ReportFreeCommitLockPath(
                GitWorktreeDirectory.ResolvePath(linked.Path, "gitdir: " + pointer + "\n"));
            Assert.Equal(directoryPath, filePath);
        }
        Assert.Equal(Path.Combine(gitDirectory, "stratalint-ingest.lock"), directoryPath);
    }

    [Fact]
    public void IngestLockPath_IsIndependentOfTmpdirTempAndTmp()
    {
        using var repository = new TemporaryDirectory();
        using var first = new TemporaryDirectory();
        using var second = new TemporaryDirectory();
        string[] variables = ["TMPDIR", "TEMP", "TMP"];
        var original = variables.ToDictionary(name => name, Environment.GetEnvironmentVariable);
        try
        {
            foreach (var name in variables) Environment.SetEnvironmentVariable(name, first.Path);
            var expected = IngestCommand.ReportFreeCommitLockPath(
                GitWorktreeDirectory.ResolvePath(repository.Path, null));
            foreach (var value in new string?[] { second.Path, string.Empty, null })
            {
                foreach (var name in variables) Environment.SetEnvironmentVariable(name, value);
                Assert.Equal(expected, IngestCommand.ReportFreeCommitLockPath(
                    GitWorktreeDirectory.ResolvePath(repository.Path, null)));
                Assert.Equal(expected, IngestCommand.ReportFreeCommitLockPath(
                    GitWorktreeDirectory.ResolvePath(repository.Path,
                        "gitdir: " + Path.Combine(repository.Path, ".git") + "\n")));
            }
        }
        finally
        {
            foreach (var (name, value) in original) Environment.SetEnvironmentVariable(name, value);
        }
    }

    [Fact]
    public void IngestLockPath_ReadsGitFileWithoutFollowingCommonDirectory()
    {
        using var repository = new TemporaryDirectory();
        using var common = new TemporaryDirectory();
        var directories = new[] { Path.Combine(common.Path, "first"), Path.Combine(common.Path, "second") };
        foreach (var directory in directories)
        {
            Directory.CreateDirectory(directory);
            File.WriteAllText(Path.Combine(directory, "commondir"), "..\n");
            File.WriteAllText(Path.Combine(repository.Path, ".git"),
                "gitdir: " + Path.GetRelativePath(repository.Path, directory) + "\n");
            Assert.Equal(directory, GitWorktreeDirectory.Read(repository.Path));
            Assert.Equal(Path.Combine(directory, "stratalint-ingest.lock"),
                IngestCommand.ReportFreeCommitLockPath(GitWorktreeDirectory.Read(repository.Path)!));
            Assert.False(File.Exists(Path.Combine(directory, "stratalint-ingest.lock")));
        }
    }
}

[CollectionDefinition("Ingest lock environment", DisableParallelization = true)]
public sealed class IngestLockEnvironmentCollection;
