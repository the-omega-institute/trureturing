using StrataLint.Runtime;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    private const string UpstreamBranch = "lane/math/upstream";

    [Theory]
    [InlineData(null, "origin/dev", "never", "none")]
    [InlineData("false", "origin/dev", "always", "none")]
    [InlineData("true", "dev", "always", "none")]
    [InlineData("always", "dev", "local", "none")]
    [InlineData("simple", "origin/dev", "remote", "none")]
    [InlineData("simple", "refs/remotes/origin/lane/math/upstream", "remote", "none")]
    [InlineData("inherit", "dev", "remote", "none")]
    [InlineData("inherit", "origin/dev", "always", "none")]
    [InlineData("inherit", "dev", "local", "local")]
    [InlineData("inherit", "dev", "remote", "local")]
    [InlineData("inherit", "dev", "never", "multiple")]
    [InlineData("inherit", "dev", "remote", "unfetched")]
    [InlineData("true", "refs/cache/vendor/dev", "remote", "custom")]
    [InlineData("true", "refs/heads/vendor/dev", "remote", "heads")]
    [InlineData("simple", "refs/cache/vendor/else", "remote", "simple-custom")]
    [InlineData("true", "refs/remotes/origin/dev", "never", "negative")]
    [InlineData("always", "origin/dev", "local", "none")]
    [InlineData("true", "origin/dev", "never", "none")]
    [InlineData("true", "origin/dev", "local", "none")]
    [InlineData("true", "origin/dev", "remote", "none")]
    [InlineData("true", "origin/dev", "always", "none")]
    [InlineData("always", "dev", "never", "none")]
    [InlineData("always", "dev", "remote", "none")]
    [InlineData("always", "dev", "always", "none")]
    public void CreationTrackingMatchesNativeWorktreeAdd(
        string? merge, string revision, string rebase, string special)
    {
        using var repository = new TemporaryDirectory();
        InitializeUpstreamRepository(repository.Path, merge, revision, rebase, special);
        var target = Path.Combine(repository.Path, "upstream-target");
        var oracle = NativeUpstreamOracle(repository.Path, revision);

        var result = WorktreeCommand.Run(repository.Path, UpstreamArguments(target, revision));

        Assert.True(result.Success, result.Error);
        Assert.Equal(oracle.Configuration, ReadUpstreamConfiguration(repository.Path));
        var upstream = ReadResolvedUpstream(target);
        Assert.Equal(oracle.ExitCode, upstream.ExitCode);
        Assert.Equal(oracle.Upstream, upstream.Upstream);
        AssertRegisteredAndUsable(repository.Path, target, UpstreamBranch);
        Assert.False(File.Exists(Path.Combine(GitWorktreeDirectory.Read(target)!, "locked")));
        var reflog = WorktreeHookFixture.RunGit(repository.Path, "reflog", "show", "--format=%gs", $"refs/heads/{UpstreamBranch}");
        Assert.Single(reflog.Split('\n'), line => line.StartsWith("worktree-init:", StringComparison.Ordinal));
    }

    [Fact]
    public void CreationPostCheckoutSeesTheSameUpstreamAsNativeAdd()
    {
        using var repository = new TemporaryDirectory();
        InitializeUpstreamRepository(repository.Path, "true", "origin/dev", "remote", "none");
        var target = Path.Combine(repository.Path, "upstream-target");
        WorktreeHookFixture.Install(repository.Path, "post-checkout", """
            common=$(git rev-parse --git-common-dir)
            git rev-parse --symbolic-full-name '@{upstream}' >> "$common/upstream-at-checkout.log"
            """ + "\n");
        WorktreeHookFixture.RunGit(repository.Path, "worktree", "add", "-b", UpstreamBranch, target, "origin/dev");
        WorktreeHookFixture.RunGit(repository.Path, "worktree", "remove", "--force", target);
        WorktreeHookFixture.RunGit(repository.Path, "branch", "-D", UpstreamBranch);

        var result = WorktreeCommand.Run(repository.Path, UpstreamArguments(target, "origin/dev"));

        Assert.True(result.Success, result.Error);
        WorktreeFixtureFile.AssertContent(Path.Combine(repository.Path, ".git", "upstream-at-checkout.log"),
            "refs/remotes/origin/dev\nrefs/remotes/origin/dev\n");
    }

    [Fact]
    public void FailedBranchCasLeavesForeignTrackingConfigurationIntact()
    {
        using var repository = new TemporaryDirectory();
        InitializeUpstreamRepository(repository.Path, "true", "origin/dev", "remote", "none");
        var target = Path.Combine(repository.Path, "upstream-target");
        var runner = new UpstreamFailureRunner(target, "foreign-branch");

        var failed = WorktreeCommand.Run(repository.Path, UpstreamArguments(target, "origin/dev"), runner);

        Assert.False(failed.Success);
        Assert.Equal(WorktreeHookFixture.RunGit(repository.Path, "rev-parse", "HEAD"),
            WorktreeHookFixture.RunGit(repository.Path, "rev-parse", $"refs/heads/{UpstreamBranch}"));
        Assert.Equal("foreign\n", WorktreeHookFixture.RunGit(repository.Path, "config", "--get", $"branch.{UpstreamBranch}.remote"));
        Assert.Equal("refs/heads/foreign\n", WorktreeHookFixture.RunGit(repository.Path, "config", "--get", $"branch.{UpstreamBranch}.merge"));
        Assert.False(Directory.Exists(target));
    }

    [Fact]
    public void InheritedMultipleUpstreamsWithRebaseFailLikeNativeWithoutLeavingOwnedState()
    {
        using var repository = new TemporaryDirectory();
        InitializeUpstreamRepository(repository.Path, "inherit", "dev", "always", "multiple");
        var target = Path.Combine(repository.Path, "upstream-target");
        var native = TestProcessRunner.Run("git", ["worktree", "add", "-b", UpstreamBranch, "--no-checkout", target, "dev"],
            repository.Path, BoundedProcessRunner.HangDetectionBudget, 4096);
        Assert.NotEqual(0, native.ExitCode);
        if (GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{UpstreamBranch}") == 0)
            WorktreeHookFixture.RunGit(repository.Path, "branch", "-D", UpstreamBranch);

        var failed = WorktreeCommand.Run(repository.Path, UpstreamArguments(target, "dev"));

        Assert.False(failed.Success);
        Assert.Contains("multiple upstream", failed.Error, StringComparison.Ordinal);
        Assert.Equal(1, GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{UpstreamBranch}"));
        Assert.Equal(new[] { string.Empty, string.Empty, string.Empty }, ReadUpstreamConfiguration(repository.Path));
        Assert.False(Directory.Exists(target));
    }

    [Theory]
    [InlineData("tracking-timeout")]
    [InlineData("tracking-nonzero")]
    [InlineData("add-rejected")]
    [InlineData("post-checkout")]
    [InlineData("inherit-partial")]
    [InlineData("policy-changed")]
    public void FailedCreationPreservesBranchTrackingAndAllowsAlternateContinuation(string failure)
    {
        using var repository = new TemporaryDirectory();
        var inherit = failure == "inherit-partial";
        var revision = inherit ? "dev" : "origin/dev";
        InitializeUpstreamRepository(repository.Path, inherit ? "inherit" : "true", revision,
            inherit || failure == "policy-changed" ? "never" : "remote", inherit ? "multiple" : "none");
        var oracle = NativeUpstreamOracle(repository.Path, revision);
        var before = ReadUpstreamConfiguration(repository.Path);
        var target = Path.Combine(repository.Path, "upstream-target");
        var runner = new UpstreamFailureRunner(target, failure);

        var failed = WorktreeCommand.Run(repository.Path, UpstreamArguments(target, revision), runner);

        Assert.False(failed.Success);
        using var receipt = JsonDocument.Parse(failed.Error["WORKTREE_FAILED ".Length..]);
        Assert.Contains("simulated upstream", receipt.RootElement.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Equal(0, GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{UpstreamBranch}"));
        var retainedConfiguration = ReadUpstreamConfiguration(repository.Path);
        var alternate = Path.Combine(repository.Path, "alternate-upstream");
        var arguments = UpstreamArguments(alternate, revision)
            .Select(argument => argument == "upstream" ? "alternate-upstream" : argument).ToArray();
        var retry = WorktreeCommand.Run(repository.Path, arguments);
        Assert.True(retry.Success, retry.Error);
        Assert.Equal(retainedConfiguration, ReadUpstreamConfiguration(repository.Path));
        AssertRegisteredAndUsable(repository.Path, alternate,
            $"{WorktreeCommand.CreationNamespace}/math/alternate-upstream");

    }

    [Theory]
    [InlineData("tracking-timeout")]
    [InlineData("concurrent-config")]
    [InlineData("concurrent-unset-remote")]
    [InlineData("concurrent-unset-merge")]
    [InlineData("concurrent-unset-rebase")]
    public void TrackingFailurePreservesConcurrentConfigurationWithRetainedBranch(string failure)
    {
        using var repository = new TemporaryDirectory();
        InitializeUpstreamRepository(repository.Path, "true", "origin/dev", "always", "none");
        WorktreeHookFixture.RunGit(repository.Path, "config", $"branch.{UpstreamBranch}.remote", "previous");
        WorktreeHookFixture.RunGit(repository.Path, "config", $"branch.{UpstreamBranch}.merge", "refs/heads/previous");
        WorktreeHookFixture.RunGit(repository.Path, "config", $"branch.{UpstreamBranch}.rebase", "false");
        WorktreeHookFixture.RunGit(repository.Path, "config", $"branch.{UpstreamBranch}.description", "keep");
        var before = ReadUpstreamConfiguration(repository.Path);
        var target = Path.Combine(repository.Path, "upstream-target");
        var runner = new UpstreamFailureRunner(target, failure);
        var deletedKey = failure.StartsWith("concurrent-unset-", StringComparison.Ordinal)
            ? $"branch.{UpstreamBranch}.{failure["concurrent-unset-".Length..]}" : null;
        if (deletedKey is not null)
            WorktreeHookFixture.Install(repository.Path, "post-checkout", $$"""
                git config --unset-all '{{deletedKey}}'
                echo 'simulated upstream configuration deletion' >&2
                exit 1
                """ + "\n");

        var failed = WorktreeCommand.Run(repository.Path, UpstreamArguments(target, "origin/dev"), runner);

        Assert.False(failed.Success);
        using var receipt = JsonDocument.Parse(failed.Error["WORKTREE_FAILED ".Length..]);
        Assert.Contains("simulated upstream", receipt.RootElement.GetProperty("reason").GetString(), StringComparison.Ordinal);
        if (failure.StartsWith("concurrent-", StringComparison.Ordinal))
        {
            Assert.Equal(0, GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{UpstreamBranch}"));
            if (deletedKey is not null)
                Assert.Equal(1, GitExit(repository.Path, "config", "--get", deletedKey));
            else
                Assert.Equal("refs/heads/concurrent\n", WorktreeHookFixture.RunGit(repository.Path,
                    "config", "--get", $"branch.{UpstreamBranch}.merge"));
        }
        else
        {
            Assert.Equal(0, GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{UpstreamBranch}"));
            Assert.NotEqual(before, ReadUpstreamConfiguration(repository.Path));
        }
        Assert.Equal("keep\n", WorktreeHookFixture.RunGit(repository.Path, "config", "--get", $"branch.{UpstreamBranch}.description"));
    }

    private static void InitializeUpstreamRepository(string root, string? merge, string revision, string rebase, string special)
    {
        InitializeRepository(root);
        WorktreeHookFixture.RunGit(root, "remote", "add", "origin", root);
        WorktreeHookFixture.RunGit(root, "fetch", "origin");
        if (merge is not null) WorktreeHookFixture.RunGit(root, "config", "branch.autoSetupMerge", merge);
        WorktreeHookFixture.RunGit(root, "config", "branch.autoSetupRebase", rebase);
        WorktreeHookFixture.RunGit(root, "config", "branch.dev.remote", special == "local" ? "." : "origin");
        WorktreeHookFixture.RunGit(root, "config", "branch.dev.merge",
            special == "unfetched" ? "refs/heads/not-fetched" : "refs/heads/dev");
        if (special == "multiple") WorktreeHookFixture.RunGit(root, "config", "--add", "branch.dev.merge", "refs/heads/second");
        WorktreeHookFixture.RunGit(root, "update-ref", $"refs/remotes/origin/{UpstreamBranch}", "HEAD");
        if (special is "custom" or "heads")
        {
            var destination = special == "custom" ? "refs/cache/vendor/*" : "refs/heads/vendor/*";
            WorktreeHookFixture.RunGit(root, "config", "remote.origin.fetch", $"+refs/heads/*:{destination}");
            WorktreeHookFixture.RunGit(root, "update-ref", revision, "HEAD");
        }
        if (special == "simple-custom")
        {
            WorktreeHookFixture.RunGit(root, "config", "remote.origin.fetch", $"+refs/heads/{UpstreamBranch}:refs/cache/vendor/else");
            WorktreeHookFixture.RunGit(root, "update-ref", revision, "HEAD");
        }
        if (special == "negative") WorktreeHookFixture.RunGit(root, "config", "--add", "remote.origin.fetch", "^refs/heads/dev");
    }

    private static (string[] Configuration, int ExitCode, string Upstream) NativeUpstreamOracle(string root, string revision)
    {
        var native = Path.Combine(root, "native-upstream");
        WorktreeHookFixture.RunGit(root, "worktree", "add", "-b", UpstreamBranch, "--no-checkout", native, revision);
        var config = ReadUpstreamConfiguration(root);
        var resolved = ReadResolvedUpstream(native);
        WorktreeHookFixture.RunGit(root, "worktree", "remove", "--force", native);
        WorktreeHookFixture.RunGit(root, "branch", "-D", UpstreamBranch);
        return (config, resolved.ExitCode, resolved.Upstream);
    }

    private static string[] ReadUpstreamConfiguration(string root) =>
        new[] { "remote", "merge", "rebase" }.Select(key =>
        {
            var result = TestProcessRunner.Run("git", ["config", "--null", "--get-all", $"branch.{UpstreamBranch}.{key}"],
                root, BoundedProcessRunner.HangDetectionBudget, 4096);
            Assert.Contains(result.ExitCode, new[] { 0, 1 });
            return Encoding.UTF8.GetString(result.StandardOutput);
        }).ToArray();

    private static (int ExitCode, string Upstream) ReadResolvedUpstream(string target)
    {
        var result = TestProcessRunner.Run("git", ["rev-parse", "--symbolic-full-name", "@{upstream}"],
            target, BoundedProcessRunner.HangDetectionBudget, 4096);
        return (result.ExitCode, Encoding.UTF8.GetString(result.StandardOutput));
    }

    private static string[] UpstreamArguments(string target, string revision) =>
        ["--kind", "math", "--name", "upstream", "--path", target, "--base", revision, "--skip-restore"];

    private sealed class UpstreamFailureRunner(string target, string failure) : IWorktreeProcessRunner
    {
        private readonly RecordingWorktreeProcessRunner inner = new();
        private bool failed;

        public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout)
        {
            var tracking = fileName == "git" && arguments.Contains("branch", StringComparer.Ordinal)
                && arguments.Any(argument => argument.StartsWith("--set-upstream-to=", StringComparison.Ordinal));
            var add = fileName == "git" && arguments.Take(2).SequenceEqual(["worktree", "add"]);
            if (!failed && failure == "policy-changed" && fileName == "git" && arguments.FirstOrDefault() == "update-ref"
                && arguments.Contains("--create-reflog", StringComparer.Ordinal))
                WorktreeHookFixture.Install(workingDirectory, "reference-transaction", """
                    if [ "$1" = prepared ]; then
                        git config branch.autoSetupRebase always
                    fi
                    """ + "\n");
            if (!failed && failure == "foreign-branch" && fileName == "git" && arguments.FirstOrDefault() == "update-ref"
                && arguments.Contains("--create-reflog", StringComparer.Ordinal))
            {
                failed = true;
                WorktreeHookFixture.RunGit(workingDirectory, "update-ref", "--create-reflog", "-m", "foreign initializer",
                    $"refs/heads/{UpstreamBranch}", arguments[^2], arguments[^1]);
                WorktreeHookFixture.RunGit(workingDirectory, "config", $"branch.{UpstreamBranch}.remote", "foreign");
                WorktreeHookFixture.RunGit(workingDirectory, "config", $"branch.{UpstreamBranch}.merge", "refs/heads/foreign");
            }
            if (!failed && add && failure is "add-rejected" or "policy-changed")
            {
                failed = true;
                var hook = WorktreeHookFixture.Install(workingDirectory, "reference-transaction", """
                    common=$(git rev-parse --git-common-dir)
                    if [ "$1" = prepared ] && [ -f "$common/worktrees/upstream-target/commondir" ]; then
                        echo 'simulated upstream registration rejection' >&2
                        exit 1
                    fi
                    """ + "\n");
                try { return inner.Run(fileName, arguments, workingDirectory, timeout); }
                finally { File.Delete(hook); }
            }
            if (!failed && fileName == "git" && arguments.Take(4).SequenceEqual(["hook", "run", "--ignore-missing", "post-checkout"])
                && failure == "post-checkout")
            {
                failed = true;
                return new ProcessOutput(1, [], Encoding.UTF8.GetBytes("simulated upstream post-checkout failure"));
            }

            var result = inner.Run(fileName, arguments, workingDirectory, timeout);
            var partial = fileName == "git" && arguments.FirstOrDefault() == "config"
                && arguments.Contains("--replace-all", StringComparer.Ordinal)
                && arguments.Contains($"branch.{UpstreamBranch}.merge", StringComparer.Ordinal);
            if (!failed && result.ExitCode == 0 && ((tracking && failure.StartsWith("tracking-", StringComparison.Ordinal))
                || (tracking && failure == "concurrent-config") || (partial && failure == "inherit-partial")))
            {
                failed = true;
                Assert.False(Directory.Exists(target));
                if (failure == "concurrent-config")
                    WorktreeHookFixture.RunGit(workingDirectory, "config", $"branch.{UpstreamBranch}.merge", "refs/heads/concurrent");
                if (failure == "tracking-nonzero")
                    return new ProcessOutput(1, [], Encoding.UTF8.GetBytes("simulated upstream configuration failure"));
                throw new TimeoutException("simulated upstream configuration timeout");
            }
            return result;
        }
    }
}
