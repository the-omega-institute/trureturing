using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class RepositorySymlinkTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DirectoryAliasRejectsAPresentGitlinkEvenWhenFiltered(bool filtered)
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        AddSkillAliases(repository.Path);
        Commit(repository.Path);
        var objectId = Git(repository.Path, "rev-parse", "HEAD").Trim();
        Directory.CreateDirectory(Path.Combine(repository.Path, "skills/vendor"));
        Git(repository.Path, "update-index", "--add", "--cacheinfo", "160000", objectId, "skills/vendor");
        Git(repository.Path, "commit", "-m", "present gitlink fixture");

        Assert.Throws<InvalidOperationException>(() => GitRepositorySnapshotReader.ReadCurrent(
            repository.Path, path => !filtered || path != "skills/vendor"));
        Assert.Throws<InvalidOperationException>(() => GitRepositorySnapshotReader.ReadRevision(repository.Path, "HEAD"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DirectoryAliasRejectsATrackedFileReplacedByADirectory(bool filtered)
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        AddSkillAliases(repository.Path);
        Write(repository.Path, "skills/replaced.md", "original file\n");
        Commit(repository.Path);
        File.Delete(Path.Combine(repository.Path, "skills/replaced.md"));
        Directory.CreateDirectory(Path.Combine(repository.Path, "skills/replaced.md"));

        Assert.Throws<InvalidOperationException>(() => GitRepositorySnapshotReader.ReadCurrent(
            repository.Path, path => !filtered || path != "skills/replaced.md"));
        Assert.Equal("original file\n", Text(GitRepositorySnapshotReader.ReadRevision(repository.Path, "HEAD"), "skills/replaced.md"));
    }

    [Fact]
    public void MalformedUtf8LinkTargetCannotMasqueradeAsAReplacementCharacter()
    {
        if (OperatingSystem.IsWindows()) return; // Windows link targets are UTF-16, not arbitrary Unix bytes.
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "skills/\uFFFD.md", "real Unicode filename\n");
        Declare(repository.Path, ("AGENTS.md", "skills/\uFFFD.md", "file"));
        Write(repository.Path, "Meta/FILEMAP.toml", File.ReadAllText(Path.Combine(repository.Path, "Meta/FILEMAP.toml"))
            .Replace("\uFFFD", "\\uFFFD", StringComparison.Ordinal));
        var created = TestProcessRunner.Run("python3",
            ["-c", "import os,sys; os.symlink(b'skills/\\xff.md', os.fsencode(sys.argv[1]))",
                Path.Combine(repository.Path, "AGENTS.md")],
            repository.Path, BoundedProcessRunner.HangDetectionBudget, 4096);
        Assert.Equal(0, created.ExitCode);

        AssertBothReject(repository.Path);
    }

    [Fact]
    public void ValidUnicodeReplacementCharacterInATargetIsPreservedExactly()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "skills/\uFFFD.md", "real Unicode filename\n");
        Declare(repository.Path, ("AGENTS.md", "skills/\uFFFD.md", "file"));
        Write(repository.Path, "Meta/FILEMAP.toml", File.ReadAllText(Path.Combine(repository.Path, "Meta/FILEMAP.toml"))
            .Replace("\uFFFD", "\\uFFFD", StringComparison.Ordinal));
        Link(repository.Path, "AGENTS.md", "skills/\uFFFD.md");
        Assert.Equal("skills/\uFFFD.md", Text(GitRepositorySnapshotReader.ReadCurrent(repository.Path), "AGENTS.md"));
        Commit(repository.Path);
        Assert.Equal("skills/\uFFFD.md", Text(GitRepositorySnapshotReader.ReadRevision(repository.Path, "HEAD"), "AGENTS.md"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DirectoryAliasesPreserveLinkBlobsWithoutDuplicatingTheTarget(bool staged)
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        AddSkillAliases(repository.Path);
        if (staged) Git(repository.Path, "add", ".");

        var current = GitRepositorySnapshotReader.ReadCurrent(repository.Path);
        Commit(repository.Path);
        var revision = GitRepositorySnapshotReader.ReadRevision(repository.Path, "HEAD");

        Assert.Equal(new[] { ".claude/skills", ".codex/skills", "Meta/FILEMAP.toml", "skills/example/SKILL.md" },
            current.Entries.Select(entry => entry.Path));
        foreach (var snapshot in new[] { current, revision })
        {
            Assert.Equal("../skills", Text(snapshot, ".claude/skills"));
            Assert.Equal("../skills", Text(snapshot, ".codex/skills"));
            Assert.Equal("# Original skill\n", Text(snapshot, "skills/example/SKILL.md"));
            Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(snapshot));
        }
        foreach (var entry in current.Entries)
            Assert.Equal<byte>(entry.Bytes, revision.Entries.Single(other => other.Path == entry.Path).Bytes);
    }

    [Fact]
    public void DirectoryAliasWritesAreConfinedToTheOwningWorktree()
    {
        using var repository = new TemporaryDirectory();
        using var second = new TemporaryDirectory();
        Initialize(repository.Path);
        AddSkillAliases(repository.Path);
        Commit(repository.Path);
        Git(repository.Path, "worktree", "add", "--detach", second.Path, "HEAD");

        Write(second.Path, ".codex/skills/example/SKILL.md", "# Changed skill\n");

        Assert.Equal("# Original skill\n", File.ReadAllText(Path.Combine(repository.Path, ".claude/skills/example/SKILL.md")));
        Assert.Equal("# Changed skill\n", File.ReadAllText(Path.Combine(second.Path, ".claude/skills/example/SKILL.md")));
        var change = Assert.Single(new GitRepositoryGateway(second.Path).ReadCurrentChanges().Entries);
        Assert.Equal("skills/example/SKILL.md", change.Path.Value);
        Assert.Equal(RawChangeKind.Modified, change.Kind);
        Assert.Equal("../skills", Text(GitRepositorySnapshotReader.ReadCurrent(second.Path), ".codex/skills"));
    }

    [Fact]
    public void RevisionUsesItsOwnDeclarationAndTargets()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        AddSkillAliases(repository.Path);
        Commit(repository.Path);
        Write(repository.Path, "Meta/FILEMAP.toml", "invalid TOML [\n");
        File.Delete(Path.Combine(repository.Path, "skills/example/SKILL.md"));

        Assert.Equal("../skills", Text(GitRepositorySnapshotReader.ReadRevision(repository.Path, "HEAD"), ".codex/skills"));
    }

    [Fact]
    public void UndeclaredAgentLinkHasNoHardcodedExemption()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "CLAUDE.md", "# Instructions\n");
        Link(repository.Path, "AGENTS.md", "CLAUDE.md");
        AssertBothReject(repository.Path);
    }

    [Theory]
    [InlineData("file")]
    [InlineData("directory")]
    public void RetainedLinkRequiresItsTargetInTheFilteredSnapshot(string kind)
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        var targetPath = kind == "file" ? "skills" : "skills/example/SKILL.md";
        Write(repository.Path, targetPath, "target\n");
        Declare(repository.Path, ("alias", "skills", kind));
        Link(repository.Path, "alias", "skills");

        Assert.Throws<InvalidOperationException>(() => GitRepositorySnapshotReader.ReadCurrent(
            repository.Path, path => path != targetPath));
        Assert.Equal("skills", Text(GitRepositorySnapshotReader.ReadCurrent(repository.Path,
            path => path != "unrelated.md"), "alias"));
        Assert.DoesNotContain(GitRepositorySnapshotReader.ReadCurrent(repository.Path,
            path => path != "alias").Entries, entry => entry.Path == "alias");
    }

    [Fact]
    public void DirectoryAliasRequiresAllDiscoveredTargetFilesAfterFiltering()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        AddSkillAliases(repository.Path);
        Write(repository.Path, "skills/second/SKILL.md", "second\n");
        Assert.Throws<InvalidOperationException>(() => GitRepositorySnapshotReader.ReadCurrent(
            repository.Path, path => path != "skills/second/SKILL.md"));
    }

    [Fact]
    public void RemovingOneTargetFileDoesNotInvalidateANonemptyDirectoryAlias()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        AddSkillAliases(repository.Path);
        Write(repository.Path, "skills/removed.md", "remove me\n");
        Commit(repository.Path);
        File.Delete(Path.Combine(repository.Path, "skills/removed.md"));

        foreach (var snapshot in new[] { GitRepositorySnapshotReader.ReadCurrent(repository.Path),
            GitRepositorySnapshotReader.ReadCurrent(repository.Path, path => path != "skills/removed.md") })
        {
            Assert.Equal("../skills", Text(snapshot, ".codex/skills"));
            Assert.DoesNotContain(snapshot.Entries, entry => entry.Path == "skills/removed.md");
        }
    }

    [Fact]
    public void RetainedLinkRequiresTheDeclarationInTheFilteredSnapshot()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        AddSkillAliases(repository.Path);
        Assert.Throws<InvalidOperationException>(() => GitRepositorySnapshotReader.ReadCurrent(
            repository.Path, path => path != "Meta/FILEMAP.toml"));
    }

    [Theory]
    [InlineData("../skills", "file")]
    [InlineData("../absent", "directory")]
    [InlineData("../skills/example/SKILL.md", "directory")]
    [InlineData("../../outside", "directory")]
    [InlineData("/tmp/outside", "directory")]
    [InlineData("../.lake", "directory")]
    [InlineData("../.git", "directory")]
    public void InvalidDeclaredTargetsFailClosed(string target, string kind)
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "skills/example/SKILL.md", "skill\n");
        Declare(repository.Path, (".codex/skills", target, kind));
        Link(repository.Path, ".codex/skills", target);
        AssertBothReject(repository.Path);
    }

    [Fact]
    public void ActualLinkMustMatchTheDeclaredTargetExactly()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        AddSkillAliases(repository.Path);
        File.Delete(Path.Combine(repository.Path, ".codex/skills"));
        Link(repository.Path, ".codex/skills", "../skills/example");
        AssertBothReject(repository.Path);
    }

    [Theory]
    [InlineData("alias", "next", "file")]
    [InlineData("skills/alias", "..", "directory")]
    [InlineData(".lake", "skills", "directory")]
    public void LinkChainsAndRecursiveOrCacheAliasesAreRejected(string path, string target, string kind)
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "skills/example/SKILL.md", "skill\n");
        Write(repository.Path, "plain.md", "plain\n");
        Link(repository.Path, "next", "plain.md");
        Declare(repository.Path, (path, target, kind), ("next", "plain.md", "file"));
        Link(repository.Path, path, target);
        AssertBothReject(repository.Path);
    }

    [Fact]
    public void CurrentRejectsSymlinkedAncestorBeforeReadingTrackedDescendants()
    {
        using var repository = new TemporaryDirectory();
        using var outside = new TemporaryDirectory();
        Initialize(repository.Path);
        AddSkillAliases(repository.Path);
        Commit(repository.Path);
        Directory.Delete(Path.Combine(repository.Path, "skills"), recursive: true);
        Write(outside.Path, "example/SKILL.md", "outside\n");
        Directory.CreateSymbolicLink(Path.Combine(repository.Path, "skills"), outside.Path);

        Assert.Throws<InvalidOperationException>(() => GitRepositorySnapshotReader.ReadCurrent(repository.Path));
    }

    [Fact]
    public void OrdinaryFilesDoNotRequireASymlinkManifest()
    {
        using var repository = new TemporaryDirectory();
        Initialize(repository.Path);
        Write(repository.Path, "AGENTS.md", "Read CLAUDE.md\n");
        Assert.Equal("Read CLAUDE.md\n", Text(GitRepositorySnapshotReader.ReadCurrent(repository.Path), "AGENTS.md"));
        Commit(repository.Path);
        Assert.Equal("Read CLAUDE.md\n", Text(GitRepositorySnapshotReader.ReadRevision(repository.Path, "HEAD"), "AGENTS.md"));
    }

    internal static void Declare(string root, params (string Path, string Target, string Kind)[] links)
    {
        var text = """
            schema_version = 2
            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-tools"
            known_violation_count = 0
            status = "closed"
            """ + "\n";
        foreach (var link in links.OrderBy(item => item.Path, StringComparer.Ordinal))
            text += $$"""
                [[files]]
                pattern = "{{link.Path}}"
                kind = "program"
                admission_plane = "judge"
                produced_by = "none"
                consumed_by = ["agent"]
                verified_by = ["repository-policy"]
                artifact_id = "none"
                runtime_disposition = "committed-source"
                symlink = { target = "{{link.Target}}", kind = "{{link.Kind}}" }
                """ + "\n";
        Write(root, "Meta/FILEMAP.toml", text);
    }

    private static void AddSkillAliases(string root)
    {
        Write(root, "skills/example/SKILL.md", "# Original skill\n");
        Declare(root, (".claude/skills", "../skills", "directory"), (".codex/skills", "../skills", "directory"));
        Link(root, ".claude/skills", "../skills");
        Link(root, ".codex/skills", "../skills");
    }

    private static void Initialize(string root)
    {
        Git(root, "init", "--initial-branch=fixture");
        Git(root, "config", "user.email", "stratalint@example.invalid");
        Git(root, "config", "user.name", "StrataLint Tests");
        Git(root, "config", "core.symlinks", "true");
    }

    private static void Link(string root, string path, string target)
    {
        Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(root, path))!);
        File.CreateSymbolicLink(Path.Combine(root, path), target);
    }

    private static void AssertBothReject(string root)
    {
        Assert.Throws<InvalidOperationException>(() => GitRepositorySnapshotReader.ReadCurrent(root));
        Commit(root);
        Assert.Throws<InvalidOperationException>(() => GitRepositorySnapshotReader.ReadRevision(root, "HEAD"));
    }

    private static string Text(RawRepositorySnapshot snapshot, string path) =>
        Encoding.UTF8.GetString(snapshot.Entries.Single(entry => entry.Path == path).Bytes.AsSpan());

    private static void Write(string root, string path, string value)
    {
        Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(root, path))!);
        File.WriteAllText(Path.Combine(root, path), value, new UTF8Encoding(false));
    }

    private static void Commit(string root)
    {
        Git(root, "add", ".");
        Git(root, "commit", "-m", "link fixture");
    }

    private static string Git(string root, params string[] arguments) => ReviewRegressionTests.RunGit(root, arguments);
}
