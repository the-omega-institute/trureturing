using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class WorktreeCacheStrategyTests
{
    [Fact]
    public void RestoreRunsLockedAndFailureRollsBack()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
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

    [Fact]
    public void WorktreeToolingKeepsItsPathContractAndNeverWalksTheCacheTreePerFile()
    {
        var root = TestRepositoryLayout.FindRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));
        var init = File.ReadAllText(Path.Combine(root, "tools", "scripts", "worktree-init.sh"));
        var clean = File.ReadAllText(Path.Combine(root, "tools", "scripts", "clean-lanes.sh"));

        Assert.Contains("WORKTREE_DEST = $(if $(DEST)", makefile, StringComparison.Ordinal);
        Assert.Contains("[DEST=DIR]", makefile, StringComparison.Ordinal);
        Assert.Contains("\"$(KIND)\" \"$(NAME)\"", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("$(origin PATH)", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("BRANCH=", init, StringComparison.Ordinal);
        Assert.Contains("--kind \"$KIND\"", init, StringComparison.Ordinal);
        Assert.Contains("--name \"$NAME\"", init, StringComparison.Ordinal);
        Assert.Contains("exec dotnet run", init, StringComparison.Ordinal);
        Assert.DoesNotContain("case \"$KIND\" in", init, StringComparison.Ordinal);
        Assert.DoesNotContain("NAME must be", init, StringComparison.Ordinal);
        Assert.DoesNotContain("harness/$NAME", init, StringComparison.Ordinal);
        Assert.DoesNotContain("export PATH=", init, StringComparison.Ordinal);
        Assert.DoesNotContain("export PATH=", clean, StringComparison.Ordinal);

        // A per-file clone walk costs one system call per entry. Build the rejected forms
        // dynamically so the repository-wide guard does not match its own source.
        var cloneFlag = string.Concat('-', 'c');
        var recursiveFlag = string.Concat('-', 'R');
        var shellForm = $"cp {cloneFlag}";
        var argumentForm = $"\"{cloneFlag}\", \"{recursiveFlag}\"";
        var scan = TestProcessRunner.Run(
            "git",
            ["grep", "-n", "-I", "-e", shellForm, "-e", argumentForm, "--", "."],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);

        Assert.Equal(
            1,
            scan.ExitCode);
    }

    private static void InitializeRepository(string root)
    {
        Git(root, "init", "--initial-branch=dev");
        Git(root, "config", "user.email", "stratalint@example.invalid");
        Git(root, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(Path.Combine(root, "README.md"), "# worktree fixture\n");
        File.WriteAllText(Path.Combine(root, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(root, "lake-manifest.json"), "{\"version\": \"1.1.0\"}\n");
        Git(root, "add", "README.md", "lean-toolchain", "lake-manifest.json");
        Git(root, "commit", "-m", "fixture baseline");
    }

    private static string Git(string root, params string[] arguments) =>
        ReviewRegressionTests.RunGit(root, arguments);

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
