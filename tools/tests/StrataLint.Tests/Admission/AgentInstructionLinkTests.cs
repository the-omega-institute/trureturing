using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AgentInstructionLinkTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CurrentAndRevisionPreserveTheLinkBytesAndBothPaths(bool stageBeforeRead)
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "CLAUDE.md", "# Local instructions\n");
        File.CreateSymbolicLink(Path.Combine(repository.Path, "AGENTS.md"), "CLAUDE.md");
        if (stageBeforeRead) Git(repository.Path, "add", ".");

        var gateway = new GitRepositoryGateway(repository.Path);
        var current = gateway.ReadCurrent();
        Commit(repository.Path);
        var revision = gateway.ReadRevision("HEAD");

        Assert.Equal(new[] { "AGENTS.md", "CLAUDE.md", "Meta/FILEMAP.toml" }, current.Entries.Select(entry => entry.Path));
        Assert.Equal("CLAUDE.md", Text(current, "AGENTS.md"));
        Assert.Equal("# Local instructions\n", Text(current, "CLAUDE.md"));
        foreach (var entry in current.Entries)
            Assert.Equal<byte>(entry.Bytes, revision.Entries.Single(other => other.Path == entry.Path).Bytes);
        Assert.Equal(
            "git-sha1:" + Git(repository.Path, "rev-parse", "HEAD:AGENTS.md").Trim(),
            revision.Entries.Single(entry => entry.Path == "AGENTS.md").GitBlobOid);
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(current));
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(revision));
    }

    [Fact]
    public void RevisionReadsItsOwnTargetWithoutDependingOnTheCheckout()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "CLAUDE.md", "# Committed instructions\n");
        File.CreateSymbolicLink(Path.Combine(repository.Path, "AGENTS.md"), "CLAUDE.md");
        Commit(repository.Path);
        File.Delete(Path.Combine(repository.Path, "CLAUDE.md"));

        var snapshot = new GitRepositoryGateway(repository.Path).ReadRevision("HEAD");

        Assert.Equal("CLAUDE.md", Text(snapshot, "AGENTS.md"));
        Assert.Equal("# Committed instructions\n", Text(snapshot, "CLAUDE.md"));
    }

    [Fact]
    public void RelativeLinkEditsOnlyItsOwnWorktreeAndRemainInTheDelta()
    {
        using var repository = new TemporaryDirectory();
        using var second = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "CLAUDE.md", "# Original instructions\n");
        File.CreateSymbolicLink(Path.Combine(repository.Path, "AGENTS.md"), "CLAUDE.md");
        Commit(repository.Path);
        Git(repository.Path, "worktree", "add", "--detach", second.Path, "HEAD");

        Write(second.Path, "AGENTS.md", "# Second worktree instructions\n");
        var original = new GitRepositoryGateway(repository.Path).ReadCurrent();
        var secondGateway = new GitRepositoryGateway(second.Path);
        var changed = secondGateway.ReadCurrent();

        Assert.Equal("# Original instructions\n", Text(original, "CLAUDE.md"));
        Assert.Equal("# Second worktree instructions\n", Text(changed, "CLAUDE.md"));
        Assert.Equal("CLAUDE.md", Text(changed, "AGENTS.md"));
        var change = Assert.Single(secondGateway.ReadCurrentChanges().Entries);
        Assert.Equal("CLAUDE.md", change.Path.Value);
        Assert.Equal(RawChangeKind.Modified, change.Kind);
    }

    [Fact]
    public void UnstagedConversionFromRegularPointerIsAcceptedAndReported()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "AGENTS.md", "Read CLAUDE.md.\n");
        Write(repository.Path, "CLAUDE.md", "# Instructions\n");
        Commit(repository.Path);
        File.Delete(Path.Combine(repository.Path, "AGENTS.md"));
        File.CreateSymbolicLink(Path.Combine(repository.Path, "AGENTS.md"), "CLAUDE.md");
        var gateway = new GitRepositoryGateway(repository.Path);

        Assert.Equal("CLAUDE.md", Text(gateway.ReadCurrent(), "AGENTS.md"));
        var change = Assert.Single(gateway.ReadCurrentChanges().Entries);
        Assert.Equal("AGENTS.md", change.Path.Value);
        Assert.Equal(RawChangeKind.Modified, change.Kind);
    }

    [Theory]
    [InlineData("OTHER.md")]
    [InlineData("./CLAUDE.md")]
    [InlineData("../CLAUDE.md")]
    [InlineData("AGENTS.md")]
    public void OtherRelativeTargetsAreRejectedInBothSnapshots(string target)
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "CLAUDE.md", "# Instructions\n");
        Write(repository.Path, "OTHER.md", "# Other instructions\n");
        File.CreateSymbolicLink(Path.Combine(repository.Path, "AGENTS.md"), target);

        AssertBothReject(repository.Path);
    }

    [Fact]
    public void AbsoluteTargetIsRejectedEvenWhenItNamesTheLocalInstructions()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "CLAUDE.md", "# Instructions\n");
        File.CreateSymbolicLink(
            Path.Combine(repository.Path, "AGENTS.md"), Path.Combine(repository.Path, "CLAUDE.md"));

        AssertBothReject(repository.Path);
    }

    [Theory]
    [InlineData("other.md")]
    [InlineData("agents.md")]
    [InlineData("nested/AGENTS.md")]
    public void OtherLinkPathsAreStillRejected(string path)
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "CLAUDE.md", "# Instructions\n");
        Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(repository.Path, path))!);
        File.CreateSymbolicLink(Path.Combine(repository.Path, path), "CLAUDE.md");

        AssertBothReject(repository.Path);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("ignored")]
    [InlineData("directory")]
    [InlineData("symlink")]
    public void TargetMustBeAPresentPlainFileInTheSnapshot(string targetKind)
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        switch (targetKind)
        {
            case "ignored":
                Write(repository.Path, ".gitignore", "CLAUDE.md\n");
                Write(repository.Path, "CLAUDE.md", "# Ignored instructions\n");
                break;
            case "directory":
                Directory.CreateDirectory(Path.Combine(repository.Path, "CLAUDE.md"));
                Write(repository.Path, "CLAUDE.md/child.txt", "child\n");
                break;
            case "symlink":
                Write(repository.Path, "OTHER.md", "# Other instructions\n");
                File.CreateSymbolicLink(Path.Combine(repository.Path, "CLAUDE.md"), "OTHER.md");
                break;
        }
        File.CreateSymbolicLink(Path.Combine(repository.Path, "AGENTS.md"), "CLAUDE.md");

        AssertBothReject(repository.Path);
    }

    private static void AssertBothReject(string root)
    {
        var gateway = new GitRepositoryGateway(root);
        Assert.Throws<InvalidOperationException>(() => gateway.ReadCurrent());
        Commit(root);
        Assert.Throws<InvalidOperationException>(() => gateway.ReadRevision("HEAD"));
    }

    private static string Text(RawRepositorySnapshot snapshot, string path) =>
        Encoding.UTF8.GetString(snapshot.Entries.Single(entry => entry.Path == path).Bytes.AsSpan());

    private static void Write(string root, string path, string value) =>
        File.WriteAllText(Path.Combine(root, path), value, new UTF8Encoding(false));

    private static void Initialize(string root)
    {
        Git(root, "init", "--initial-branch=fixture");
        Git(root, "config", "user.email", "stratalint@example.invalid");
        Git(root, "config", "user.name", "StrataLint Tests");
        Git(root, "config", "core.symlinks", "true");
        RepositorySymlinkTests.Declare(root, ("AGENTS.md", "CLAUDE.md", "file"));
    }

    private static void Commit(string root)
    {
        Git(root, "add", ".");
        Git(root, "commit", "-m", "instruction link fixture");
    }

    private static string Git(string root, params string[] arguments) =>
        ReviewRegressionTests.RunGit(root, arguments);
}
