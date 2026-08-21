using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// The snapshot is a (path -> bytes) map, so a symlink has no representation in it: reading the
// link itself stores a path string as if it were content, and following it either aliases one
// byte sequence under two paths or escapes the repository altogether. Agent runtime config
// directories hold links that belong to the local tool, not to the truth graph, so the reader
// skips them outright instead of deciding how to encode them.
public sealed class UngovernedAgentConfigSnapshotTests
{
    private static readonly UTF8Encoding Utf8 = new(false);

    [Theory]
    [InlineData(".claude")]
    [InlineData(".codex")]
    public void TrackedSymlinkInsideAnUngovernedAgentConfigDirectoryLeavesTheSnapshot(
        string directory)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteFile(repository.Path, "skills/codex-formalize/SKILL.md", "skill\n");
        Directory.CreateDirectory(Path.Combine(repository.Path, directory));
        Directory.CreateSymbolicLink(
            Path.Combine(repository.Path, directory, "skills"),
            Path.Combine("..", "skills"));
        ReviewRegressionTests.RunGit(repository.Path, "add", "-A");
        Assert.Equal("120000", TrackedMode(repository.Path, $"{directory}/skills"));

        var snapshot = GitRepositorySnapshotReader.ReadCurrent(repository.Path);

        Assert.DoesNotContain(snapshot.Entries, entry => entry.Path == $"{directory}/skills");
        Assert.Contains(snapshot.Entries, entry => entry.Path == "skills/codex-formalize/SKILL.md");
    }

    [Theory]
    [InlineData(".claude/settings.json")]
    [InlineData(".codex/config.toml")]
    public void TrackedPlainFileInsideAnUngovernedAgentConfigDirectoryLeavesTheSnapshot(string path)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteFile(repository.Path, path, "local agent configuration\n");
        WriteFile(repository.Path, "README.md", "governed\n");
        ReviewRegressionTests.RunGit(repository.Path, "add", "-A");

        var snapshot = GitRepositorySnapshotReader.ReadCurrent(repository.Path);

        Assert.DoesNotContain(snapshot.Entries, entry => entry.Path == path);
        Assert.Contains(snapshot.Entries, entry => entry.Path == "README.md");
    }

    [Theory]
    [InlineData(".claude")]
    [InlineData(".codex")]
    public void UntrackedFileSymlinkInsideAnUngovernedAgentConfigDirectoryLeavesTheSnapshot(
        string directory)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteFile(repository.Path, "README.md", "governed\n");
        ReviewRegressionTests.RunGit(repository.Path, "add", "-A");
        Directory.CreateDirectory(Path.Combine(repository.Path, directory));
        File.CreateSymbolicLink(
            Path.Combine(repository.Path, directory, "link"),
            Path.Combine("..", "README.md"));

        var snapshot = GitRepositorySnapshotReader.ReadCurrent(repository.Path);

        Assert.DoesNotContain(snapshot.Entries, entry => entry.Path == $"{directory}/link");
    }

    // The exclusion is a named list, not a "leading dot" wildcard: .github is a dot directory too
    // and it carries the required-check definition, CODEOWNERS and the harness gate script, all of
    // which must stay under machine governance.
    [Theory]
    [InlineData(".github/workflows/ci.yml")]
    [InlineData(".github/CODEOWNERS")]
    [InlineData(".vscode/settings.json")]
    [InlineData(".editorconfig")]
    public void DotPathsOutsideTheNamedListStayInsideTheSnapshot(string path)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteFile(repository.Path, path, "governed\n");
        ReviewRegressionTests.RunGit(repository.Path, "add", "-A");

        var snapshot = GitRepositorySnapshotReader.ReadCurrent(repository.Path);

        Assert.Contains(snapshot.Entries, entry => entry.Path == path);
    }

    [Fact]
    public void TrackedSymlinkOutsideTheNamedListIsStillRejected()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteFile(repository.Path, "README.md", "governed\n");
        Directory.CreateDirectory(Path.Combine(repository.Path, "docs"));
        File.CreateSymbolicLink(
            Path.Combine(repository.Path, "docs", "link"),
            Path.Combine("..", "README.md"));
        ReviewRegressionTests.RunGit(repository.Path, "add", "-A");
        Assert.Equal("120000", TrackedMode(repository.Path, "docs/link"));

        var error = Assert.Throws<InvalidOperationException>(
            () => GitRepositorySnapshotReader.ReadCurrent(repository.Path));

        Assert.Equal(
            "non-regular repository entry docs/link has git mode 120000",
            error.Message);
    }

    [Fact]
    public void UntrackedFileSymlinkOutsideTheNamedListIsStillRejected()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteFile(repository.Path, "README.md", "governed\n");
        ReviewRegressionTests.RunGit(repository.Path, "add", "-A");
        Directory.CreateDirectory(Path.Combine(repository.Path, "docs"));
        File.CreateSymbolicLink(
            Path.Combine(repository.Path, "docs", "link"),
            Path.Combine("..", "README.md"));

        var error = Assert.Throws<InvalidOperationException>(
            () => GitRepositorySnapshotReader.ReadCurrent(repository.Path));

        Assert.Equal(
            "non-regular repository entry docs/link is not a plain file",
            error.Message);
    }

    [Theory]
    [InlineData(".claude/settings.json")]
    [InlineData(".codex/config.toml")]
    public void ChangesInsideAnUngovernedAgentConfigDirectoryLeaveTheChangeSet(string path)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteFile(repository.Path, "README.md", "governed\n");
        ReviewRegressionTests.RunGit(repository.Path, "add", "-A");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "baseline");
        WriteFile(repository.Path, path, "local agent configuration\n");
        WriteFile(repository.Path, "README.md", "governed and edited\n");

        var changes = new GitRepositoryGateway(repository.Path).ReadCurrentChanges();

        Assert.DoesNotContain(changes.Paths, candidate => candidate.Value == path);
        Assert.Contains(changes.Paths, candidate => candidate.Value == "README.md");
    }

    private static void InitializeRepository(string root)
    {
        ReviewRegressionTests.RunGit(root, "init", "--initial-branch=dev");
        ReviewRegressionTests.RunGit(root, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(root, "config", "user.name", "StrataLint Tests");
    }

    private static void WriteFile(string root, string relativePath, string content)
    {
        var absolute = Path.Combine(root, relativePath.Replace('/', Path.DirectorySeparatorChar));
        Directory.CreateDirectory(
            Path.GetDirectoryName(absolute)
                ?? throw new InvalidOperationException("fixture path has no parent"));
        File.WriteAllText(absolute, content, Utf8);
    }

    private static string TrackedMode(string root, string relativePath) =>
        ReviewRegressionTests.RunGit(root, "ls-files", "--stage", "--", relativePath)
            .Split(' ', StringSplitOptions.RemoveEmptyEntries)[0];
}
