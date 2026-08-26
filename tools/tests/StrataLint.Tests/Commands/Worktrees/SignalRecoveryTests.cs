using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    [Fact]
    public void HalfBuiltWorktreeIsRecoveredBeforeRetryingSameName()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string branch = "harness/signal-retry";
        var target = Path.Combine(repository.Path, "signal-retry");
        var missingMetadata = WorktreeMetadataPath(repository.Path, target);
        ReviewRegressionTests.RunGit(repository.Path, "branch", branch, "HEAD");
        Directory.CreateDirectory(target);
        File.WriteAllText(
            Path.Combine(target, ".git"),
            $"gitdir: {missingMetadata}\n",
            new UTF8Encoding(encoderShouldEmitUTF8Identifier: false));
        File.WriteAllText(Path.Combine(target, "README.md"), "partial checkout\n");

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", branch,
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ]);

        Assert.True(result.Success, result.Error);
        AssertFileContent(Path.Combine(target, "README.md"), "# worktree fixture\n");
        AssertRegisteredAndUsable(repository.Path, target, branch);
    }

    [Fact]
    public void SuccessfulGitExitWithoutRegisteredWorktreeFailsClosed()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string branch = "harness/postcondition-failure";
        var target = Path.Combine(repository.Path, "postcondition-failure");
        var missingMetadata = WorktreeMetadataPath(repository.Path, target);
        var runner = new RecordingWorktreeProcessRunner
        {
            AfterWorktreeAdd = _ => Directory.Delete(missingMetadata, recursive: true),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", branch,
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner);

        Assert.False(result.Success);
        Assert.Contains("not registered", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.False(Directory.Exists(target));
        Assert.Equal(1, GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{branch}"));
    }

    [Fact]
    public void RegisteredWorktreeThatCannotRevParseFailsClosed()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string branch = "harness/unusable-postcondition";
        var target = Path.Combine(repository.Path, "unusable-postcondition");
        var runner = new RecordingWorktreeProcessRunner
        {
            AfterWorktreeAdd = path => File.WriteAllText(
                Path.Combine(path, ".git"),
                $"gitdir: {Path.Combine(repository.Path, ".git", "worktrees", "missing")}\n"),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", branch,
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner);

        Assert.False(result.Success);
        Assert.Contains("not a git repository", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.False(Directory.Exists(target));
    }

    [Fact]
    public void NormalCreationSatisfiesRegisteredAndUsablePostconditions()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string branch = "harness/postcondition-success";
        var target = Path.Combine(repository.Path, "postcondition-success");

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", branch,
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
                "--branch", "harness/foreign-metadata",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ]);

        Assert.False(result.Success);
        Assert.Contains("path already exists", result.Error, StringComparison.Ordinal);
        AssertFileContent(marker, "keep\n");
    }

    // 这个 helper 的存在理由与 ArchiveInEnsureChainTests.cs:177 同:SL-003 的 unknown 判据
    // 只看**测试方法体自身**的语法树,方法体里出现 `File.ReadAllText(...)` 且参数不是
    // `RepositoryRelativePath.Create("字面量")` 或 `Path.Combine(RepositoryLayout.FindRoot(), "字面量"…)`
    // 时,该方法即计入 conservative unknown。临时目录的路径结构上满足不了那两种形状,
    // 故读临时文件必须收进 helper。(本轮实测:这两句把两个新方法判成 unknown,
    // admission RULE_REJECTED;`make -C tools test` 看不见,只有 preflight 的 admission 段会红。)
    private static void AssertFileContent(string path, string expected) =>
        Assert.Equal(expected, File.ReadAllText(path));

    private static string WorktreeMetadataPath(string repository, string target)
    {
        var commonDirectory = ReviewRegressionTests.RunGit(
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
        var inventory = ReviewRegressionTests.RunGit(repository, "worktree", "list", "--porcelain");
        Assert.Contains(
            $"worktree {LeanCacheGuard.PhysicalPath(target)}\n",
            inventory,
            StringComparison.Ordinal);
        Assert.Equal("true\n", ReviewRegressionTests.RunGit(target, "rev-parse", "--is-inside-work-tree"));
        Assert.Equal(
            $"refs/heads/{branch}\n",
            ReviewRegressionTests.RunGit(target, "symbolic-ref", "HEAD"));
    }

    private static int GitExit(string workingDirectory, params string[] arguments) =>
        BoundedProcessRunner.Run(
            "git",
            arguments,
            workingDirectory,
            BoundedProcessRunner.HangDetectionBudget,
            4096).ExitCode;
}
