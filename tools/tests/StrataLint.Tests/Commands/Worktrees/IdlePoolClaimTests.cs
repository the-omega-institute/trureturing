using System.Text.Json;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    [Fact]
    public void IdleUnusedFreshCreationReturnsWithoutPr()
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        using var remote = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        File.WriteAllText(Path.Combine(repository.Path, ".gitignore"),
            ".caller-review-prompt.md\n.echo-review.md\n.sshx-*\n.lake/\n");
        TestGit.Run(repository.Path, "add", ".gitignore");
        TestGit.Run(repository.Path, "commit", "-m", "Scaffold ignores");
        TestGit.Run(remote.Path, "init", "--bare");
        TestGit.Run(repository.Path, "remote", "add", "origin", remote.Path);
        TestGit.Run(repository.Path, "push", "origin", "dev");
        var target = Path.Combine(repository.Path, "unused");
        var created = WorktreeCommand.Run(repository.Path,
            ["--kind", "governance", "--name", "unused", "--path", target, "--base", "dev", "--skip-restore"]);
        Assert.True(created.Success, created.Error);
        Assert.Equal("", WorktreeHookFixture.RunGit(target, "status", "--porcelain"));
        Directory.CreateDirectory(Path.Combine(target, ".lake"));
        File.WriteAllText(Path.Combine(target, ".lake", "sentinel"), "cache bytes");

        var returned = WorktreeCommand.Run(target, ["return", "--writers-joined"]);

        Assert.True(returned.Success, returned.Error);
        using var receipt = JsonDocument.Parse(returned.Output);
        Assert.Equal("returned", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal(WorktreeHookFixture.RunGit(repository.Path, "rev-parse", "dev").Trim(),
            receipt.RootElement.GetProperty("allocation_base").GetString());
        Assert.Equal("cache bytes", File.ReadAllText(Path.Combine(target, ".lake", "sentinel")));
        Assert.StartsWith("lane/governance/idle-", WorktreeHookFixture.RunGit(target, "branch", "--show-current"));
        Assert.Equal("", WorktreeHookFixture.RunGit(target, "status", "--porcelain"));
    }

    [Theory]
    [InlineData("busy")]
    [InlineData("available")]
    public void IdleConcurrentImplicitRequestsAllocateDistinctTrees(string poolState)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/worktree_protocol_tests.py"),
                root, "--implicit-claims", typeof(WorktreeCommand).Assembly.Location, poolState],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void IdlePoolBypassesAutomaticAgeButAllowsNamedRemoval()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        TestGit.Run(repository.Path, "update-ref", "refs/remotes/origin/dev", "HEAD");
        var idle = Path.Combine(repository.Path, "idle");
        var token = Guid.NewGuid().ToString("N");
        var idleBranch = "refs/heads/lane/governance/idle-" + token;
        TestGit.Run(repository.Path, "update-ref", "--create-reflog", "-m", "worktree-idle:" + token,
            idleBranch, "HEAD");
        TestGit.Run(repository.Path, "worktree", "add", idle, idleBranch["refs/heads/".Length..]);

        var result = CleanLanesCommand.Run(repository.Path, ["--force", "--lanes-only"],
            new DateTimeOffset(2030, 1, 2, 0, 0, 0, TestBudgets.ZeroDuration));

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(idle));
        Assert.Contains("idle_pool", result.Output, StringComparison.Ordinal);
        var removed = WorktreeCommand.Run(repository.Path, ["remove", "--names", "idle"]);
        Assert.True(removed.Success, removed.Error);
        Assert.False(Directory.Exists(idle));
    }

    [Fact]
    public void ImplicitSameTaskRetryRecoversOwnedDeadInitializerAtActualPath()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string branch = "lane/math/interrupted-init";
        var target = Path.Combine(repository.Path, "retained-initialization");
        var fallback = Path.Combine(repository.Path, "fallback");
        var token = Guid.NewGuid().ToString("N");
        var creation = WorktreeHookFixture.RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        TestGit.Run(repository.Path, "update-ref", "--create-reflog", "-m", "worktree-init:" + token,
            "refs/heads/" + branch, creation, new string('0', creation.Length));
        TestGit.Run(repository.Path, "worktree", "add", "--no-checkout", "--lock", "--reason",
            "worktree-init:" + token, target, branch);
        File.WriteAllText(Path.Combine(target, "README.md"), "partial initialization bytes\n");
        string[] arguments = ["--kind", "math", "--name", "interrupted-init", "--base", "HEAD",
            "--path", fallback, "--prefer-idle", "--skip-restore"];

        var result = WorktreeCommand.Run(repository.Path, arguments);

        Assert.True(result.Success, result.Error);
        using var receipt = JsonDocument.Parse(result.Output);
        Assert.Equal("recovered", receipt.RootElement.GetProperty("status").GetString());
        var actual = WorktreeHookFixture.RunGit(target, "rev-parse", "--show-toplevel").Trim();
        Assert.Equal(actual, receipt.RootElement.GetProperty("path").GetString());
        Assert.Contains("worktree-recovered:" + token, WorktreeHookFixture.RunGit(target, "reflog", "--format=%gs"));
        Assert.False(File.Exists(Path.Combine(GitWorktreeDirectory.Read(target)!, "locked")));
        Assert.False(Directory.Exists(fallback));
        Assert.Equal("partial initialization bytes\n", File.ReadAllText(Path.Combine(target, "README.md")));
        File.WriteAllText(Path.Combine(repository.Path, "lean-toolchain"), "leanprover/lean4:v4.34.2\n");
        TestGit.Run(repository.Path, "commit", "-am", "Advance requested base");
        var repeated = WorktreeCommand.Run(repository.Path, arguments);
        Assert.True(repeated.Success, repeated.Error);
        using var reuse = JsonDocument.Parse(repeated.Output);
        Assert.Equal("reused", reuse.RootElement.GetProperty("status").GetString());
        Assert.Equal(actual, reuse.RootElement.GetProperty("path").GetString());
    }

    [Theory]
    [InlineData(false, "restore")]
    [InlineData(true, "restore")]
    [InlineData(false, "checkout")]
    [InlineData(true, "checkout")]
    [InlineData(false, "protocol-timeout")]
    [InlineData(true, "protocol-timeout")]
    public void SameTaskRecoveryFailureReportsActualTargetWithoutFallback(bool implicitTarget, string failure)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string branch = "lane/math/interrupted-init";
        var target = Path.Combine(repository.Path, "retained-initialization");
        var fallback = Path.Combine(repository.Path, "fallback");
        var token = Guid.NewGuid().ToString("N");
        var creation = WorktreeHookFixture.RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        TestGit.Run(repository.Path, "update-ref", "--create-reflog", "-m", "worktree-init:" + token,
            "refs/heads/" + branch, creation, new string('0', creation.Length));
        TestGit.Run(repository.Path, "worktree", "add", "--no-checkout", "--lock", "--reason",
            "worktree-init:" + token, target, branch);
        target = WorktreeHookFixture.RunGit(target, "rev-parse", "--show-toplevel").Trim();
        File.WriteAllText(Path.Combine(target, "README.md"), "partial initialization bytes\n");
        if (failure == "checkout")
            WorktreeHookFixture.Install(repository.Path, "post-checkout",
                "echo 'recovery checkout failed' >&2\nexit 37\n");
        var arguments = new List<string> { "--kind", "math", "--name", "interrupted-init",
            "--base", "HEAD", "--path", implicitTarget ? fallback : target };
        if (implicitTarget) arguments.Add("--prefer-idle");
        if (failure != "restore") arguments.Add("--skip-restore");
        var runner = new RecoveryTimeoutRunner(failure == "protocol-timeout");

        var result = WorktreeCommand.Run(repository.Path, arguments, runner);

        Assert.False(result.Success);
        Assert.Equal(failure == "protocol-timeout" ? 124 : 73, result.ExitCode);
        Assert.StartsWith("WORKTREE_FAILED ", result.Error, StringComparison.Ordinal);
        using var receipt = JsonDocument.Parse(result.Error["WORKTREE_FAILED ".Length..]);
        var root = receipt.RootElement;
        Assert.Equal("worktree_init", root.GetProperty("event").GetString());
        Assert.Equal("failed", root.GetProperty("status").GetString());
        Assert.Equal("recovery", root.GetProperty("stage").GetString());
        Assert.Equal(target, root.GetProperty("path").GetString());
        Assert.Equal(target, root.GetProperty("target").GetString());
        Assert.Equal(branch, root.GetProperty("branch").GetString());
        Assert.Equal(target, root.GetProperty("retained_material").GetProperty("path").GetString());
        Assert.Equal(branch, root.GetProperty("retained_material").GetProperty("branch").GetString());
        Assert.Equal("WORKTREE_RETAINED " + (failure switch
        {
            "restore" => "initialization_restore_failed:1",
            "checkout" => "recovery checkout failed",
            _ => "recovery protocol timed out",
        }) + "\n", root.GetProperty("reason").GetString());
        Assert.Equal("rerun make worktree with the same KIND/NAME/DEST; or reclaim the registered target with make worktree-remove",
            root.GetProperty("recovery_action").GetString());
        Assert.False(Directory.Exists(fallback));
        Assert.True(File.Exists(Path.Combine(GitWorktreeDirectory.Read(target)!, "locked")));
        Assert.Equal(creation, WorktreeHookFixture.RunGit(target, "rev-parse", "HEAD").Trim());
        Assert.Equal("partial initialization bytes\n", File.ReadAllText(Path.Combine(target, "README.md")));
        Assert.DoesNotContain(runner.Inner.Invocations, call => call.FileName == "git"
            && call.Arguments.Take(2).SequenceEqual(["worktree", "add"]));
    }

    private sealed class RecoveryTimeoutRunner(bool timeout) : IWorktreeProcessRunner
    {
        internal RecordingWorktreeProcessRunner Inner { get; } = new();

        public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan budget) =>
            timeout && fileName == "python3" && arguments.Contains("recover-init")
                ? new ProcessOutput(124, [], Encoding.UTF8.GetBytes("WORKTREE_RETAINED recovery protocol timed out\n"))
                : Inner.Run(fileName, arguments, workingDirectory, budget);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IdleClaimUsesActualPathAndKeepsTaskBranchAndCache(bool exact)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        TestGit.Run(repository.Path, "update-ref", "refs/remotes/origin/dev", "HEAD");
        var idle = Path.Combine(repository.Path, "idle");
        var token = Guid.NewGuid().ToString("N");
        var idleBranch = "refs/heads/lane/governance/idle-" + token;
        TestGit.Run(repository.Path, "update-ref", "--create-reflog", "-m", "worktree-idle:" + token,
            idleBranch, "HEAD");
        TestGit.Run(repository.Path, "worktree", "add", idle, idleBranch["refs/heads/".Length..]);
        TestGit.Run(repository.Path, "config", "core.excludesFile", Path.Combine(repository.Path, "ignore"));
        File.WriteAllText(Path.Combine(repository.Path, "ignore"), ".lake/\n");
        Directory.CreateDirectory(Path.Combine(idle, ".lake"));
        File.WriteAllText(Path.Combine(idle, ".lake", "sentinel"), "cached bytes\n");
        var fallback = Path.Combine(repository.Path, "fallback");
        var arguments = new List<string> { "--kind", "math", "--name", "claimed", "--base", "dev",
            "--path", exact ? idle : fallback, "--skip-restore" };
        if (!exact) arguments.Add("--prefer-idle");

        var result = WorktreeCommand.Run(repository.Path, arguments);

        Assert.True(result.Success, result.Error);
        using var receipt = JsonDocument.Parse(result.Output);
        Assert.Equal("claimed", receipt.RootElement.GetProperty("status").GetString());
        var registeredPath = WorktreeHookFixture.RunGit(idle, "rev-parse", "--show-toplevel").Trim();
        Assert.Contains("worktree " + registeredPath + "\n",
            WorktreeHookFixture.RunGit(repository.Path, "worktree", "list", "--porcelain"), StringComparison.Ordinal);
        Assert.Equal(registeredPath, receipt.RootElement.GetProperty("path").GetString());
        Assert.False(Directory.Exists(fallback));
        Assert.Equal("cached bytes\n", File.ReadAllText(Path.Combine(idle, ".lake", "sentinel")));
        Assert.Equal("lane/math/claimed", WorktreeHookFixture.RunGit(idle, "branch", "--show-current").Trim());
        Assert.Contains("worktree-allocation:", WorktreeHookFixture.RunGit(idle, "reflog", "-1", "--format=%gs"));
        var repeated = WorktreeCommand.Run(repository.Path, arguments);
        Assert.True(repeated.Success, repeated.Error);
        using var reuse = JsonDocument.Parse(repeated.Output);
        Assert.Equal("reused", reuse.RootElement.GetProperty("status").GetString());
        Assert.Equal(registeredPath, reuse.RootElement.GetProperty("path").GetString());
    }
}
