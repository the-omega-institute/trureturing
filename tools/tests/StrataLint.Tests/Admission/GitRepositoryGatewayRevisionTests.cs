using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class GitRepositoryGatewayRevisionTests
{
    private const string FirstOid = "1111111111111111111111111111111111111111";
    private const string SecondOid = "2222222222222222222222222222222222222222";

    [Fact]
    public void ReadRevisionBatchesAllBlobReadsIntoOneGitProcess()
    {
        using var repository = new TemporaryDirectory();
        var runner = new RecordingGitProcessRunner();
        var gateway = new GitRepositoryGateway(
            repository.Path,
            runner,
            "git");

        var snapshot = gateway.ReadRevision("synthetic-base");

        Assert.Collection(
            snapshot.Entries,
            entry => AssertEntry(entry, "alpha.txt", "alpha\n"),
            entry => AssertEntry(entry, "duplicate.txt", "alpha\n"),
            entry => AssertEntry(entry, "empty.txt", string.Empty));
        Assert.Collection(
            runner.Calls,
            arguments => Assert.Equal(["ls-tree", "-r", "-l", "-z", "synthetic-base"], arguments),
            arguments => Assert.Equal(["cat-file", "--batch"], arguments));
    }

    [Fact]
    public void ReadRevisionRoundTripsCommittedBlobBytes()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init");
        ReviewRegressionTests.RunGit(
            repository.Path,
            "config",
            "user.email",
            "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(
            repository.Path,
            "config",
            "user.name",
            "StrataLint Tests");
        var binary = new byte[] { 0, 10, 128, 255 };
        File.WriteAllBytes(Path.Combine(repository.Path, "binary.dat"), binary);
        File.WriteAllBytes(Path.Combine(repository.Path, "empty.dat"), []);
        File.WriteAllText(
            Path.Combine(repository.Path, "first.txt"),
            "shared\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "second.txt"),
            "shared\n",
            new UTF8Encoding(false));
        File.WriteAllText(
            Path.Combine(repository.Path, "script.sh"),
            "#!/bin/sh\nexit 0\n",
            new UTF8Encoding(false));
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "update-index", "--chmod=+x", "script.sh");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "batch fixture");
        var revision = ReviewRegressionTests.RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        File.WriteAllText(
            Path.Combine(repository.Path, "first.txt"),
            "working tree change\n",
            new UTF8Encoding(false));

        var snapshot = new GitRepositoryGateway(repository.Path).ReadRevision(revision);

        var entries = snapshot.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        Assert.Equal(binary, entries["binary.dat"].Bytes);
        Assert.Empty(entries["empty.dat"].Bytes);
        Assert.Equal(Encoding.UTF8.GetBytes("shared\n"), entries["first.txt"].Bytes);
        Assert.Equal(entries["first.txt"].Bytes, entries["second.txt"].Bytes);
        Assert.Equal(
            Encoding.UTF8.GetBytes("#!/bin/sh\nexit 0\n"),
            entries["script.sh"].Bytes);
    }

    [Fact]
    public void ReadCurrentChangesReportsOnlyWorkingTreeDeltaFromHead()
    {
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(Path.Combine(repository.Path, "tracked.txt"), "baseline\n", new UTF8Encoding(false));
        ReviewRegressionTests.RunGit(repository.Path, "add", "tracked.txt");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "working changes fixture");
        var gateway = new GitRepositoryGateway(repository.Path);

        Assert.Empty(gateway.ReadCurrentChanges().Entries);

        File.WriteAllText(Path.Combine(repository.Path, "tracked.txt"), "changed\n", new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(repository.Path, "untracked.txt"), "new\n", new UTF8Encoding(false));

        Assert.Equal(
            new[]
            {
                ("tracked.txt", RawChangeKind.Modified),
                ("untracked.txt", RawChangeKind.Added),
            },
            gateway.ReadCurrentChanges().Entries
                .Select(static change => (change.Path.Value, change.Kind)));
    }

    [Fact]
    public void PreparePrefersModifiedOverCopySourceForTheSamePath()
    {
        using var repository = new TemporaryDirectory();
        var runner = new PrepareGitProcessRunner(
            "M\0source.txt\0C069\0source.txt\0copy.txt\0");
        var gateway = new GitRepositoryGateway(
            repository.Path,
            runner,
            "git");

        var prepared = gateway.Prepare("synthetic-base");

        Assert.Equal(2, prepared.Changes.Entries.Length);
        var source = Assert.Single(
            prepared.Changes.Entries,
            change => change.Path.Value == "source.txt");
        Assert.Equal(RawChangeKind.Modified, source.Kind);
        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "copy.txt" && change.Kind == RawChangeKind.Added);
    }

    [Fact]
    public void PreparePrefersDeletedOverRenameSourceCollisionForTheSamePath()
    {
        using var repository = new TemporaryDirectory();
        var runner = new PrepareGitProcessRunner(
            "M\0source.txt\0R100\0source.txt\0renamed.txt\0");
        var gateway = new GitRepositoryGateway(
            repository.Path,
            runner,
            "git");

        var prepared = gateway.Prepare("synthetic-base");

        Assert.Equal(2, prepared.Changes.Entries.Length);
        var source = Assert.Single(
            prepared.Changes.Entries,
            change => change.Path.Value == "source.txt");
        Assert.Equal(RawChangeKind.Deleted, source.Kind);
        Assert.Contains(prepared.Changes.Entries, change =>
            change.Path.Value == "renamed.txt" && change.Kind == RawChangeKind.Added);
    }

    private static void AssertEntry(RawRepositoryEntry entry, string path, string expected)
    {
        Assert.Equal(path, entry.Path);
        Assert.Equal(Encoding.UTF8.GetBytes(expected), entry.Bytes);
    }

    private sealed class RecordingGitProcessRunner : IGitProcessRunner
    {
        internal List<string[]> Calls { get; } = [];

        public ProcessOutput Run(
            string fileName,
            IReadOnlyList<string> arguments,
            string workingDirectory,
            TimeSpan timeout,
            int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
            ReadOnlyMemory<byte> standardInput = default)
        {
            Calls.Add(arguments.ToArray());
            return arguments[0] switch
            {
                "ls-tree" => Output(
                    $"100644 blob {FirstOid} 6\talpha.txt\0"
                    + $"100644 blob {FirstOid} 6\tduplicate.txt\0"
                    + $"100644 blob {SecondOid} 0\tempty.txt\0"),
                "cat-file" when Encoding.UTF8.GetString(standardInput.Span)
                    == $"{FirstOid}\n{SecondOid}\n" => Output(
                        $"{FirstOid} blob 6\nalpha\n\n"
                        + $"{SecondOid} blob 0\n\n"),
                "show" when arguments[1] == "synthetic-base:alpha.txt" => Output("alpha\n"),
                "show" when arguments[1] == "synthetic-base:duplicate.txt" => Output("alpha\n"),
                "show" when arguments[1] == "synthetic-base:empty.txt" => Output(string.Empty),
                _ => throw new InvalidOperationException("unexpected Git command"),
            };
        }

        private static ProcessOutput Output(string output) =>
            new(0, Encoding.UTF8.GetBytes(output), []);
    }

    private sealed class PrepareGitProcessRunner(string diffNameStatus) : IGitProcessRunner
    {
        public ProcessOutput Run(
            string fileName,
            IReadOnlyList<string> arguments,
            string workingDirectory,
            TimeSpan timeout,
            int maximumOutputBytes = GitRepositoryGateway.DefaultGitOutputBytes,
            ReadOnlyMemory<byte> standardInput = default) =>
            arguments[0] switch
            {
                "rev-parse" when arguments[1] == "HEAD" => Output(SecondOid + "\n"),
                "status" => Output(string.Empty),
                "rev-parse" when arguments[1] == "--verify" => Output(FirstOid + "\n"),
                "merge-base" when arguments[1] == "--is-ancestor" => Output(string.Empty),
                "diff" => Output(diffNameStatus),
                "ls-files" => Output(string.Empty),
                _ => throw new InvalidOperationException("unexpected Git command"),
            };

        private static ProcessOutput Output(string output) =>
            new(0, Encoding.UTF8.GetBytes(output), []);
    }
}
