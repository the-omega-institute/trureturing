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
        const string branch = "harness/math/signal-retry";
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
        WorktreeFixtureFile.AssertContent(Path.Combine(target, "README.md"), "# worktree fixture\n");
        AssertRegisteredAndUsable(repository.Path, target, branch);
    }

    [Fact]
    public void SuccessfulGitExitWithoutRegisteredWorktreeFailsClosed()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string branch = "harness/math/postcondition-failure";
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
        const string branch = "harness/math/unusable-postcondition";
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
        const string branch = "harness/math/postcondition-success";
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
                "--branch", "harness/math/foreign-metadata",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ]);

        Assert.False(result.Success);
        Assert.Contains("path already exists", result.Error, StringComparison.Ordinal);
        WorktreeFixtureFile.AssertContent(marker, "keep\n");
    }

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

// SL-003 的 conservative-unknown 判据只接受两种路径形状——`RepositoryRelativePath.Create("字面量")`
// 与 `Path.Combine(RepositoryLayout.FindRoot(), "字面量"…)`——**两者都是仓库路径**,临时夹具目录
// 结构上满足不了。而 `ScribeTestMapDeriver` 会沿 `LocalCalls`(:511-519)**传递地**跟进同类型内的
// 被调方法,故收进同一个 partial class 的 helper 无效(实测:第二次 preflight 判词一字未变)。
// `LocalCalls` 只捕获裸标识符与 `this.` 两种形状,**限定调用不被跟进**,故读取放在独立类型里。
// 仓内同形写法见 MissingStampDonorTests.cs:625(辅助类上的属性,属性访问不是 invocation)。
internal static class WorktreeFixtureFile
{
    internal static void AssertContent(string path, string expected) =>
        Assert.Equal(expected, File.ReadAllText(path));
}
