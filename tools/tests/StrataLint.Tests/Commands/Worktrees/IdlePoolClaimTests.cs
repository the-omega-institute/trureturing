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
    public void NativePidfdDistinguishesDeadLeaderFromWholeGroupExit()
    {
        if (!OperatingSystem.IsLinux()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root,
                "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures/host_cleanup_tests.py"),
                Path.Combine(root, "tools/scripts/host-cleanup.py"),
                "HostCleanupTests.test_native_pidfd_dead_leader_live_worker"],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture);
        Console.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DormantTaskClaimUsesEmbeddedHostAndPreservesBranch(bool exact)
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        TestGit.Run(repository.Path, "update-ref", "refs/remotes/origin/dev", "HEAD");
        const string previous = "lane/math/dormant";
        var target = Path.Combine(repository.Path, "dormant");
        TestGit.Run(repository.Path, "worktree", "add", "-b", previous, target, "HEAD");
        File.WriteAllText(Path.Combine(target, "README.md"), "unmerged dormant source\n");
        const string timestamp = "1700000000";
        var committed = TestProcessRunner.Run("env",
            ["GIT_COMMITTER_DATE=@" + timestamp + " +0000", "git", "commit", "-am", "Dormant task"],
            target, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.True(committed.ExitCode == 0, Encoding.UTF8.GetString(committed.StandardError));
        var saved = TestGit.Run(target, "rev-parse", "HEAD").Trim();
        var log = Path.Combine(GitWorktreeDirectory.Read(target)!, "logs", "HEAD");
        File.WriteAllLines(log, File.ReadAllLines(log).Select(line =>
        {
            var parts = line.Split('\t', 2);
            var fields = parts[0].Split(' ');
            fields[^2] = timestamp;
            return string.Join(' ', fields) + (parts.Length == 2 ? "\t" + parts[1] : "");
        }));
        File.WriteAllText(Path.Combine(repository.Path, ".git", "info", "exclude"), ".lake/\n");
        Directory.CreateDirectory(Path.Combine(target, ".lake"));
        File.WriteAllText(Path.Combine(target, ".lake", "sentinel"), "cached bytes\n");
        var fallback = Path.Combine(repository.Path, "fallback");
        var arguments = new List<string> { "--kind", "math", "--name", "next", "--base", "dev",
            "--path", exact ? target : fallback, "--skip-restore" };
        if (!exact) arguments.Add("--prefer-idle");

        var result = WorktreeCommand.Run(repository.Path, arguments, new ActivityIsolatedRunner());

        Assert.True(result.Success, result.Error);
        using var receipt = JsonDocument.Parse(result.Output);
        Assert.Equal("claimed", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("refs/heads/" + previous, receipt.RootElement.GetProperty("previous_branch").GetString());
        Assert.Equal(saved, TestGit.Run(repository.Path, "rev-parse", previous).Trim());
        Assert.Equal("unmerged dormant source\n", TestGit.Run(repository.Path, "show", previous + ":README.md"));
        Assert.Equal("lane/math/next", TestGit.Run(target, "branch", "--show-current").Trim());
        Assert.Equal("cached bytes\n", File.ReadAllText(Path.Combine(target, ".lake", "sentinel")));
        Assert.False(Directory.Exists(fallback));
    }

    [Fact]
    public void ImplicitCreationRunsEmbeddedDiskCheckAfterNoReusableTree()
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        TestGit.Run(repository.Path, "update-ref", "refs/remotes/origin/dev", "HEAD");
        var target = Path.Combine(repository.Path, "fallback");
        var result = TestProcessRunner.Run("env", ["WORKTREE_REQUIRE_DISK_CHECK=1", "dotnet",
            typeof(WorktreeCommand).Assembly.Location, "worktree", "--source", repository.Path,
            "--kind", "math", "--name", "disk-check", "--base", "dev", "--path", target,
            "--prefer-idle", "--skip-restore"], repository.Path,
            TestBudgets.ProtocolProbeHangGuard, 1024 * 1024);
        var stdout = Encoding.UTF8.GetString(result.StandardOutput);
        var stderr = Encoding.UTF8.GetString(result.StandardError);
        if (result.ExitCode == 0)
        {
            using var receipt = JsonDocument.Parse(stdout);
            Assert.Equal("succeeded", receipt.RootElement.GetProperty("status").GetString());
            Assert.True(Directory.Exists(target));
        }
        else
        {
            Assert.Contains("WORKTREE_LOW_DISK", stderr, StringComparison.Ordinal);
            Assert.False(Directory.Exists(target));
        }
    }

    [Fact]
    public void ExactCreationChecksDiskWhenDeferredTargetIsMissing()
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        using var executables = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        TestGit.Run(repository.Path, "update-ref", "refs/remotes/origin/dev", "HEAD");
        var python = TestProcessRunner.Run("python3", ["-I", "-c", "import sys; print(sys.executable)"],
            repository.Path, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);
        Assert.Equal(0, python.ExitCode);
        var shim = Path.Combine(executables.Path, "python3");
        File.WriteAllText(shim, """
            #!/bin/sh
            for argument do
              if [ "$argument" = check-disk ]; then
                printf '%s\n' WORKTREE_LOW_DISK_fixture >&2
                exit 73
              fi
            done
            exec "$WORKTREE_TEST_PYTHON" "$@"
            """ + "\n");
        File.SetUnixFileMode(shim, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var target = Path.Combine(repository.Path, "removed-before-creation");

        var result = TestProcessRunner.Run("env", ["WORKTREE_REQUIRE_DISK_CHECK=1",
            "WORKTREE_TEST_PYTHON=" + Encoding.UTF8.GetString(python.StandardOutput).Trim(),
            "PATH=" + executables.Path + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
            "dotnet", typeof(WorktreeCommand).Assembly.Location, "worktree", "--source", repository.Path,
            "--kind", "math", "--name", "deferred-disk", "--base", "dev", "--path", target,
            "--skip-restore"], repository.Path, TestBudgets.ProtocolProbeHangGuard, 1024 * 1024);

        Assert.Equal(73, result.ExitCode);
        Assert.Contains("WORKTREE_LOW_DISK_fixture", Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.False(Directory.Exists(target));
        Assert.DoesNotContain("lane/math/deferred-disk", TestGit.Run(repository.Path, "branch", "--list"),
            StringComparison.Ordinal);
    }

    [Fact]
    public void OldIdleTreeUsesAutomaticCommitAgeRemoval()
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
        Assert.Contains("head_commit_age", result.Output, StringComparison.Ordinal);
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

        var result = WorktreeCommand.Run(repository.Path, arguments, new ActivityIsolatedRunner());

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
        var repeated = WorktreeCommand.Run(repository.Path, arguments, new ActivityIsolatedRunner());
        Assert.True(repeated.Success, repeated.Error);
        using var reuse = JsonDocument.Parse(repeated.Output);
        Assert.Equal("reused", reuse.RootElement.GetProperty("status").GetString());
        Assert.Equal(registeredPath, reuse.RootElement.GetProperty("path").GetString());
    }

    private sealed class ActivityIsolatedRunner : IWorktreeProcessRunner
    {
        private readonly ProductionWorktreeProcessRunner inner = new();

        public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments,
            string workingDirectory, TimeSpan budget)
        {
            if (fileName != "python3") return inner.Run(fileName, arguments, workingDirectory, budget);
            var fixture = Path.Combine(TestRepositoryLayout.FindRoot(), "tools", "tests",
                "StrataLint.WorktreeContract.Tests", "Fixtures", "activity_fixture.py");
            return inner.Run(fileName, ["-I", "-B", fixture, "--", .. arguments], workingDirectory, budget);
        }
    }

}
