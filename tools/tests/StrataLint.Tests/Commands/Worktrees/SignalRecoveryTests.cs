using StrataLint.Runtime;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    [Fact]
    public void NativeInitializerRetainsScopeAfterCliParentIsKilled()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "--initializer", typeof(StrataLint.Cli.Program).Assembly.Location],
            root, TimeSpan.FromSeconds(90), 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void InitializationUsesCanonicalRepositoryDespiteAmbientGitOverrides()
    {
        using var repository = new TemporaryDirectory();
        using var foreign = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        InitializeRepository(foreign.Path);
        var target = Path.Combine(repository.Path, "canonical-environment");
        var variables = new Dictionary<string, string>
        {
            ["GIT_DIR"] = Path.Combine(foreign.Path, ".git"),
            ["GIT_WORK_TREE"] = foreign.Path,
            ["GIT_INDEX_FILE"] = Path.Combine(foreign.Path, ".git", "index"),
            ["GIT_NAMESPACE"] = "redirected",
        };
        var previous = variables.Keys.ToDictionary(name => name, Environment.GetEnvironmentVariable);
        CommandResult result;
        try
        {
            foreach (var (name, value) in variables) Environment.SetEnvironmentVariable(name, value);
            result = WorktreeCommand.Run(repository.Path,
                ["--kind", "governance", "--name", "canonical-environment", "--path", target,
                    "--base", "HEAD", "--source", repository.Path, "--skip-restore"]);
        }
        finally
        {
            foreach (var (name, value) in previous) Environment.SetEnvironmentVariable(name, value);
        }
        Assert.True(result.Success, result.Error);
        AssertRegisteredAndUsable(repository.Path, target, "lane/governance/canonical-environment");
        Assert.DoesNotContain("canonical-environment", TestGit.Run(foreign.Path, "worktree", "list"), StringComparison.Ordinal);
        Assert.Equal(string.Empty, TestGit.Run(foreign.Path, "status", "--porcelain"));
    }

    [Fact]
    public void HalfBuiltWorktreeIsPreservedForAlternateContinuation()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var branch = $"{WorktreeCommand.CreationNamespace}/math/signal-retry";
        var target = Path.Combine(repository.Path, "signal-retry");
        var missingMetadata = WorktreeMetadataPath(repository.Path, target);
        TestGit.Run(repository.Path, "branch", branch, "HEAD");
        Directory.CreateDirectory(target);
        File.WriteAllText(
            Path.Combine(target, ".git"),
            $"gitdir: {missingMetadata}\n",
            new UTF8Encoding(encoderShouldEmitUTF8Identifier: false));
        File.WriteAllText(Path.Combine(target, "README.md"), "partial checkout\n");

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "signal-retry",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ]);

        Assert.False(result.Success);
        Assert.Contains("repository_identity", result.Error, StringComparison.Ordinal);
        WorktreeFixtureFile.AssertContent(Path.Combine(target, "README.md"), "partial checkout\n");
        Assert.Equal(0, GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{branch}"));
    }

    [Fact]
    public void SuccessfulGitExitWithoutRegisteredWorktreeFailsClosed()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var branch = $"{WorktreeCommand.CreationNamespace}/math/postcondition-failure";
        var target = Path.Combine(repository.Path, "postcondition-failure");
        var missingMetadata = WorktreeMetadataPath(repository.Path, target);
        var runner = new RecordingWorktreeProcessRunner
        {
            AfterWorktreeAdd = _ => Directory.Delete(missingMetadata, recursive: true),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "postcondition-failure",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner);

        Assert.False(result.Success);
        Assert.Contains("not registered", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.True(Directory.Exists(target));
        Assert.Equal(0, GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{branch}"));
    }

    [Fact]
    public void RegisteredWorktreeThatCannotRevParseFailsClosed()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var branch = $"{WorktreeCommand.CreationNamespace}/math/unusable-postcondition";
        var target = Path.Combine(repository.Path, "unusable-postcondition");
        var other = Path.Combine(repository.Path, "other", "unusable-postcondition");
        WorktreeHookFixture.RunGit(repository.Path, "worktree", "add", "--detach", "--lock", "--reason", "keep", other, "HEAD");
        var otherMetadata = GitWorktreeDirectory.Read(other)!;
        var stale = Path.Combine(repository.Path, "stale-registration");
        WorktreeHookFixture.RunGit(repository.Path, "worktree", "add", "--detach", stale, "HEAD");
        var staleMetadata = GitWorktreeDirectory.Read(stale)!;
        Directory.Delete(stale, recursive: true);
        string? ownedMetadata = null;
        var runner = new RecordingWorktreeProcessRunner
        {
            AfterWorktreeAdd = path =>
            {
                ownedMetadata = GitWorktreeDirectory.Read(path)!;
                File.WriteAllText(Path.Combine(path, ".git"),
                    $"gitdir: {Path.Combine(repository.Path, ".git", "worktrees", "missing")}\n");
            },
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "unusable-postcondition",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner);

        Assert.False(result.Success);
        Assert.Contains("not a git repository", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.True(Directory.Exists(target));
        Assert.NotNull(ownedMetadata);
        Assert.NotEqual(otherMetadata, ownedMetadata);
        Assert.True(Directory.Exists(ownedMetadata));
        using var receipt = JsonDocument.Parse(result.Error["WORKTREE_FAILED ".Length..]);
        Assert.Contains("retained", receipt.RootElement.GetProperty("cleanup_error").GetString(), StringComparison.Ordinal);
        var inventory = WorktreeHookFixture.RunGit(repository.Path, "worktree", "list", "--porcelain");
        Assert.Contains($"worktree {LeanCacheGuard.PhysicalPath(target)}\n", inventory, StringComparison.Ordinal);
        Assert.Equal(0, GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{branch}"));
        WorktreeFixtureFile.AssertContent(Path.Combine(otherMetadata, "locked"), "keep\n");
        WorktreeFixtureFile.AssertContent(Path.Combine(other, "README.md"), "# worktree fixture\n");
        Assert.True(Directory.Exists(staleMetadata));

        var retry = WorktreeCommand.Run(repository.Path,
            ["--kind", "math", "--name", "unusable-postcondition", "--path", target, "--base", "HEAD", "--skip-restore"]);
        Assert.False(retry.Success);
        Assert.True(Directory.Exists(ownedMetadata));

    }

    [Fact]
    public void NormalCreationSatisfiesRegisteredAndUsablePostconditions()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var branch = $"{WorktreeCommand.CreationNamespace}/math/postcondition-success";
        var target = Path.Combine(repository.Path, "postcondition-success");

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "postcondition-success",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ]);

        Assert.True(result.Success, result.Error);
        AssertRegisteredAndUsable(repository.Path, target, branch);
    }

    [Fact]
    public void ExistingDirectoryWithForeignMissingGitMetadataIsNotDeleted()
    {
        using var repository = new TemporaryDirectory();
        using var foreign = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "foreign-metadata");
        var marker = Path.Combine(target, "keep.txt");
        Directory.CreateDirectory(target);
        File.WriteAllText(
            Path.Combine(target, ".git"),
            $"gitdir: {Path.Combine(foreign.Path, "missing")}\n");
        File.WriteAllText(marker, "keep\n");

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "foreign-metadata",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ]);

        Assert.False(result.Success);
        Assert.Contains("repository_identity", result.Error, StringComparison.Ordinal);
        WorktreeFixtureFile.AssertContent(marker, "keep\n");
    }

    private static string WorktreeMetadataPath(string repository, string target)
    {
        var commonDirectory = TestGit.Run(
            repository,
            "rev-parse",
            "--git-common-dir").Trim();
        if (!Path.IsPathFullyQualified(commonDirectory))
        {
            commonDirectory = Path.Combine(repository, commonDirectory);
        }

        return Path.Combine(
            LeanCacheGuard.PhysicalPath(commonDirectory),
            "worktrees",
            Path.GetFileName(target));
    }

    private static void AssertRegisteredAndUsable(string repository, string target, string branch)
    {
        var inventory = TestGit.Run(repository, "worktree", "list", "--porcelain");
        Assert.Contains(
            $"worktree {LeanCacheGuard.PhysicalPath(target)}\n",
            inventory,
            StringComparison.Ordinal);
        Assert.Equal("true\n", TestGit.Run(target, "rev-parse", "--is-inside-work-tree"));
        Assert.Equal(
            $"refs/heads/{branch}\n",
            TestGit.Run(target, "symbolic-ref", "HEAD"));
    }

    private static int GitExit(string workingDirectory, params string[] arguments) =>
        TestProcessRunner.Run(
            "git",
            arguments,
            workingDirectory,
            BoundedProcessRunner.HangDetectionBudget,
            4096).ExitCode;
}

internal static class WorktreeFixtureFile
{
    internal static void AssertContent(string path, string expected)
    {
        // Git can return the physical /private/var spelling of the macOS temporary root.
        var temporaryRoot = Path.GetTempPath();
        var relative = Path.GetRelativePath(LeanCacheGuard.PhysicalPath(temporaryRoot), LeanCacheGuard.PhysicalPath(path));
        var temporaryPath = Path.Combine(temporaryRoot, relative);
        Assert.Equal(expected, StrataLint.TestSupport.TemporaryFileSystem.File.ReadAllText(temporaryPath));
    }
}
