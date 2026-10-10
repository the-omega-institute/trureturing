using StrataLint.Runtime;
using System.Text;
using Xunit.Abstractions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class WorktreeCacheStrategyTests(ITestOutputHelper output)
{
    [Fact]
    public void RestoreRunsLockedAndFailureRollsBack()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        using var remote = new TemporaryDirectory();
        Git(remote.Path, "init", "--bare");
        Git(repository.Path, "remote", "add", "origin", remote.Path);
        Git(repository.Path, "push", "origin", "dev");
        var target = Path.Combine(repository.Path, "failed-restore");
        var runner = new RecordingWorktreeProcessRunner { FailDotnet = true };
        var branch = $"{WorktreeCommand.CreationNamespace}/math/failed-restore";

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "failed-restore",
                "--path", target,
                "--base", "HEAD",
            ],
            runner);

        output.WriteLine(result.Error);
        Assert.False(result.Success);
        Assert.Contains("dotnet restore failed", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Contains(
            runner.Invocations,
                static call => call.FileName == "dotnet"
                && call.Arguments.SequenceEqual(
                    ["restore", WorktreeCommand.SolutionPath, "--locked-mode"]));
        Assert.False(Directory.Exists(target));
        AssertBranchMissing(repository.Path, branch);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, true)]
    public void RestoreFailureRetainsUnconfirmedOrNewMaterial(bool published, bool newMaterial)
    {
        using var repository = new TemporaryDirectory();
        using var remote = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        if (published)
        {
            Git(remote.Path, "init", "--bare");
            Git(repository.Path, "remote", "add", "origin", remote.Path);
            Git(repository.Path, "push", "origin", "dev");
        }
        var target = Path.Combine(repository.Path, "failed-restore");
        var runner = new RecordingWorktreeProcessRunner
        {
            FailDotnet = true,
            AfterWorktreeAdd = newMaterial ? path => File.WriteAllText(Path.Combine(path, "recovery"), "owned bytes") : null,
        };
        var result = WorktreeCommand.Run(repository.Path,
            ["--kind", "math", "--name", "failed-restore", "--path", target, "--base", "HEAD"], runner);
        output.WriteLine(result.Error);
        Assert.False(result.Success);
        Assert.Contains("dotnet restore failed", result.Error, StringComparison.Ordinal);
        Assert.True(Directory.Exists(target));
        Assert.Contains(published ? "untracked_or_ignored_material" : "remote_preservation_unknown", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, TestProcessRunner.Run("git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{WorktreeCommand.CreationNamespace}/math/failed-restore"],
            repository.Path, BoundedProcessRunner.HangDetectionBudget, 4096).ExitCode);
        if (newMaterial) Assert.Equal("owned bytes", File.ReadAllText(Path.Combine(target, "recovery")));
    }

    [Fact]
    public void FailedWorktreeAddDoesNotCleanUpStateItDidNotCreate()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "concurrent-add");
        var runner = new RecordingWorktreeProcessRunner { FailWorktreeAdd = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "concurrent-add",
                "--path", target,
                "--base", "HEAD",
                "--skip-restore",
            ],
            runner);

        output.WriteLine(result.Error);
        Assert.False(result.Success);
        Assert.Contains("simulated concurrent worktree", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "git"
                && call.Arguments.Take(2).SequenceEqual(["worktree", "remove"]));
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "git"
                && call.Arguments.Take(2).SequenceEqual(["branch", "-D"]));
    }

    [Fact]
    public void DefaultRemoteBaseFetchesBeforeAddingWorktree()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        Git(repository.Path, "remote", "add", "origin", repository.Path);
        Git(repository.Path, "fetch", "origin");
        var target = Path.Combine(repository.Path, "fetched-default");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--kind", "math",
                "--name", "fetched-default",
                "--path", target,
                "--skip-restore",
            ],
            runner);

        Assert.True(result.Success, result.Error);
        var fetchIndex = runner.Invocations.FindIndex(
            static call => call.FileName == "git" && call.Arguments.FirstOrDefault() == "fetch");
        var addIndex = runner.Invocations.FindIndex(
            static call => call.FileName == "git" && call.Arguments.Take(2).SequenceEqual(["worktree", "add"]));
        Assert.True(fetchIndex >= 0, "expected git fetch");
        Assert.True(addIndex > fetchIndex, "git fetch must precede git worktree add");
    }

    private static void InitializeRepository(string root)
    {
        Git(root, "init", "--initial-branch=dev");
        Git(root, "config", "user.email", "stratalint@example.invalid");
        Git(root, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(Path.Combine(root, "README.md"), "# worktree fixture\n");
        File.WriteAllText(Path.Combine(root, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(root, "lake-manifest.json"), LeanCacheFixtureFile.Manifest());
        Git(root, "add", "README.md", "lean-toolchain", "lake-manifest.json");
        Git(root, "commit", "-m", "fixture baseline");
    }

    private static string Git(string root, params string[] arguments) =>
        TestGit.Run(root, arguments);

    private static void AssertBranchMissing(string root, string branch)
    {
        var lookup = TestProcessRunner.Run(
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{branch}"],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            4096);
        Assert.Equal(1, lookup.ExitCode);
    }
}
