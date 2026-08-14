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
            "git",
            TimeSpan.FromSeconds(1));

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
}
