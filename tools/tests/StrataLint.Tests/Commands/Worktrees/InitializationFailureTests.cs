using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class WorktreeCommandTests
{
    [Theory]
    [InlineData("branch-timeout")]
    [InlineData("branch-nonzero")]
    [InlineData("branch-rejected")]
    [InlineData("add-timeout")]
    [InlineData("add-nonzero")]
    [InlineData("add-prepared")]
    [InlineData("add-rejected")]
    [InlineData("checkout-timeout")]
    [InlineData("checkout-nonzero")]
    [InlineData("checkout-index-lock")]
    public void InterruptedInitializationRemovesOwnedStateAndAllowsSameNameRetry(string failure)
    {
        if (failure == "add-prepared" && OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var branch = $"{WorktreeCommand.CreationNamespace}/math/interrupted-init";
        var runner = new InitializationFailureRunner(target, failure);

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target), runner);

        Assert.False(result.Success);
        Assert.Contains("simulated initialization", result.Error, StringComparison.Ordinal);
        using var receipt = JsonDocument.Parse(result.Error["WORKTREE_FAILED ".Length..]);
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("cleanup_error").ValueKind);
        Assert.False(Directory.Exists(target));
        Assert.False(Directory.Exists(WorktreeMetadataPath(repository.Path, target)));
        var inventory = WorktreeHookFixture.RunGit(repository.Path, "worktree", "list", "--porcelain");
        Assert.DoesNotContain($"worktree {LeanCacheGuard.PhysicalPath(target)}\n", inventory, StringComparison.Ordinal);
        Assert.DoesNotContain($"branch refs/heads/{branch}\n", inventory, StringComparison.Ordinal);
        Assert.Equal(1, GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{branch}"));

        var retryRunner = new InitializationFailureRunner(target, "none");
        var retry = WorktreeCommand.Run(repository.Path, InitializationArguments(target), retryRunner);

        Assert.True(retry.Success, retry.Error);
        AssertRegisteredAndUsable(repository.Path, target, branch);
        WorktreeFixtureFile.AssertContent(Path.Combine(target, "README.md"), "# worktree fixture\n");
        Assert.False(File.Exists(Path.Combine(WorktreeMetadataPath(repository.Path, target), "locked")));
        Assert.NotEqual(runner.CreationToken, retryRunner.CreationToken);
    }

    [Theory]
    [InlineData("branch-foreign-nonzero")]
    [InlineData("branch-foreign-timeout")]
    [InlineData("branch-recreated")]
    public void FailedBranchCreateIfAbsentPreservesIndependentBranchAtSameOid(string failure)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var branchRef = $"refs/heads/{WorktreeCommand.CreationNamespace}/math/interrupted-init";
        var head = WorktreeHookFixture.RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        var runner = new InitializationFailureRunner(target, failure);

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target), runner);

        Assert.False(result.Success);
        using var receipt = JsonDocument.Parse(result.Error["WORKTREE_FAILED ".Length..]);
        Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("cleanup_error").ValueKind);
        Assert.False(Directory.Exists(target));
        Assert.False(Directory.Exists(WorktreeMetadataPath(repository.Path, target)));
        Assert.Equal(head, WorktreeHookFixture.RunGit(repository.Path, "rev-parse", "--verify", branchRef).Trim());
        Assert.Equal($"{head}\t{InitializationFailureRunner.ForeignLock}\n",
            WorktreeHookFixture.RunGit(repository.Path, "reflog", "show", "--format=%H%x09%gs", branchRef));
        Assert.DoesNotContain(runner.Inner.Invocations, call => call.FileName == "git"
            && (call.Arguments.Take(2).SequenceEqual(["worktree", "add"])
                || call.Arguments.Contains("-d", StringComparer.Ordinal)));
    }

    [Theory]
    [InlineData("branch-changed", "initialization branch changed")]
    [InlineData("cleanup-branch-changed", "initialization branch changed")]
    [InlineData("cleanup-branch-race", "cannot lock ref")]
    [InlineData("cleanup-branch-recreated", "initialization branch ownership changed")]
    [InlineData("cleanup-branch-symbolic", "initialization branch changed")]
    public void BranchRollbackPreservesConcurrentRefUpdates(string failure, string cleanupError)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var branchRef = $"refs/heads/{WorktreeCommand.CreationNamespace}/math/interrupted-init";
        var runner = new InitializationFailureRunner(target, failure);

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target), runner);

        Assert.False(result.Success);
        using var receipt = JsonDocument.Parse(result.Error["WORKTREE_FAILED ".Length..]);
        Assert.Contains("simulated initialization", receipt.RootElement.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Contains(cleanupError, receipt.RootElement.GetProperty("cleanup_error").GetString(), StringComparison.Ordinal);
        Assert.False(Directory.Exists(target));
        Assert.False(Directory.Exists(WorktreeMetadataPath(repository.Path, target)));
        Assert.NotNull(runner.ChangedBranchOid);
        Assert.Equal(runner.ChangedBranchOid,
            WorktreeHookFixture.RunGit(repository.Path, "rev-parse", "--verify", branchRef).Trim());
    }

    [Theory]
    [InlineData("branch-receipt-error", "simulated branch receipt lookup failure")]
    [InlineData("cleanup-branch-timeout", "simulated branch cleanup timeout")]
    [InlineData("cleanup-branch-rejected", "simulated branch cleanup rejection")]
    public void BranchRollbackReportsFailureWithoutMaskingInitializationError(string failure, string cleanupError)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var branchRef = $"refs/heads/{WorktreeCommand.CreationNamespace}/math/interrupted-init";
        var runner = new InitializationFailureRunner(target, failure);

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target), runner);

        Assert.False(result.Success);
        using var receipt = JsonDocument.Parse(result.Error["WORKTREE_FAILED ".Length..]);
        Assert.Contains("simulated initialization", receipt.RootElement.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Contains(cleanupError, receipt.RootElement.GetProperty("cleanup_error").GetString(), StringComparison.Ordinal);
        Assert.False(Directory.Exists(target));
        Assert.False(Directory.Exists(WorktreeMetadataPath(repository.Path, target)));
        Assert.Equal(WorktreeHookFixture.RunGit(repository.Path, "rev-parse", "HEAD"),
            WorktreeHookFixture.RunGit(repository.Path, "rev-parse", "--verify", branchRef));
    }

    [Theory]
    [InlineData("foreign-elsewhere")]
    [InlineData("foreign-detached")]
    [InlineData("foreign-elsewhere-prepared")]
    public void BranchRollbackPreservesSurvivingRegistrations(string failure)
    {
        if (failure.EndsWith("prepared", StringComparison.Ordinal) && OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var foreignTarget = failure == "foreign-detached" ? target : Path.Combine(repository.Path, "foreign-init");
        var runner = new InitializationFailureRunner(target, failure, foreignTarget);

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target), runner);

        Assert.False(result.Success);
        using var receipt = JsonDocument.Parse(result.Error["WORKTREE_FAILED ".Length..]);
        Assert.Contains("simulated concurrent creator", receipt.RootElement.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Contains("registered worktree", receipt.RootElement.GetProperty("cleanup_error").GetString(), StringComparison.Ordinal);
        WorktreeFixtureFile.AssertContent(Path.Combine(foreignTarget, "keep.txt"), "concurrent work\n");
        WorktreeFixtureFile.AssertContent(Path.Combine(WorktreeMetadataPath(repository.Path, foreignTarget), "locked"),
            InitializationFailureRunner.ForeignLock + "\n");
        Assert.Equal(0, GitExit(repository.Path, "show-ref", "--verify", "--quiet",
            $"refs/heads/{WorktreeCommand.CreationNamespace}/math/interrupted-init"));
        Assert.DoesNotContain(runner.Inner.Invocations, call => call.FileName == "git"
            && (call.Arguments.Take(2).SequenceEqual(["worktree", "remove"])
                || call.Arguments.Contains("-d", StringComparer.Ordinal)));
    }

    [Fact]
    public void InitializationKeepsOwnershipLockDuringCheckoutAndReleasesItOnSuccess()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var runner = new InitializationFailureRunner(target, "none");

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target), runner);

        Assert.True(result.Success, result.Error);
        Assert.Matches("^worktree-init:[a-f0-9]{32}$", runner.CreationToken!);
        Assert.True(runner.CheckoutSawLock);
        Assert.False(runner.CheckoutSawTrackedContent);
        WorktreeFixtureFile.AssertContent(Path.Combine(target, "README.md"), "# worktree fixture\n");
        Assert.False(File.Exists(Path.Combine(WorktreeMetadataPath(repository.Path, target), "locked")));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FailedInitializationPreservesConcurrentCreatorsState(bool foreignLock)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var runner = new InitializationFailureRunner(target, foreignLock ? "foreign-locked" : "foreign-unlocked");

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target), runner);

        Assert.False(result.Success);
        Assert.Contains("simulated concurrent creator", result.Error, StringComparison.Ordinal);
        WorktreeFixtureFile.AssertContent(Path.Combine(target, "keep.txt"), "concurrent work\n");
        if (foreignLock)
            WorktreeFixtureFile.AssertContent(Path.Combine(WorktreeMetadataPath(repository.Path, target), "locked"),
                InitializationFailureRunner.ForeignLock + "\n");
        AssertRegisteredAndUsable(repository.Path, target, $"{WorktreeCommand.CreationNamespace}/math/interrupted-init");
        Assert.DoesNotContain(runner.Inner.Invocations, call =>
            call.FileName == "git" && (call.Arguments.Take(2).SequenceEqual(["worktree", "remove"])
                || call.Arguments.Contains("-d", StringComparer.Ordinal)));
    }

    [Fact]
    public void PartialRegistrationWithAnotherInitializersTokenIsPreserved()
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var runner = new InitializationFailureRunner(target, "foreign-prepared");

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target), runner);

        Assert.False(result.Success);
        Assert.Contains("simulated concurrent creator", result.Error, StringComparison.Ordinal);
        WorktreeFixtureFile.AssertContent(Path.Combine(target, "keep.txt"), "concurrent work\n");
        WorktreeFixtureFile.AssertContent(Path.Combine(WorktreeMetadataPath(repository.Path, target), "locked"),
            InitializationFailureRunner.ForeignLock + "\n");
        Assert.Contains($"worktree {LeanCacheGuard.PhysicalPath(target)}\n",
            WorktreeHookFixture.RunGit(repository.Path, "worktree", "list", "--porcelain"), StringComparison.Ordinal);
        Assert.Equal(0, GitExit(repository.Path, "show-ref", "--verify", "--quiet",
            $"refs/heads/{WorktreeCommand.CreationNamespace}/math/interrupted-init"));
        Assert.DoesNotContain(runner.Inner.Invocations, call => call.FileName == "git"
            && (call.Arguments.Take(2).SequenceEqual(["worktree", "remove"])
                || call.Arguments.Take(2).SequenceEqual(["branch", "-D"])
                || call.Arguments.Contains("-d", StringComparer.Ordinal)));
    }

    [Theory]
    [InlineData("gitdir")]
    [InlineData("commondir")]
    public void InitializationTokenWithForeignMetadataLinksDoesNotAuthorizeCleanup(string link)
    {
        using var repository = new TemporaryDirectory();
        using var foreign = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        InitializeRepository(foreign.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var runner = new InitializationFailureRunner(target, $"add-invalid-{link}", Path.Combine(foreign.Path, ".git"));

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target), runner);

        Assert.False(result.Success);
        using var receipt = JsonDocument.Parse(result.Error["WORKTREE_FAILED ".Length..]);
        Assert.Contains("simulated initialization", receipt.RootElement.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Contains("could not validate initialization metadata ownership",
            receipt.RootElement.GetProperty("cleanup_error").GetString(), StringComparison.Ordinal);
        Assert.True(Directory.Exists(target));
        Assert.True(Directory.Exists(WorktreeMetadataPath(repository.Path, target)));
        Assert.Equal(0, GitExit(repository.Path, "show-ref", "--verify", "--quiet",
            $"refs/heads/{WorktreeCommand.CreationNamespace}/math/interrupted-init"));
        WorktreeFixtureFile.AssertContent(Path.Combine(foreign.Path, "README.md"), "# worktree fixture\n");
        WorktreeFixtureFile.AssertContent(Path.Combine(foreign.Path, ".git", "HEAD"), "ref: refs/heads/dev\n");
    }

    [Theory]
    [InlineData("cleanup-timeout", "simulated cleanup timeout")]
    [InlineData("cleanup-ownership-changed", "initialization ownership changed")]
    public void InitializationFailureReportsCleanupExceptionWithoutMaskingOriginalError(string failure, string cleanupError)
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var runner = new InitializationFailureRunner(target, failure);

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target), runner);

        Assert.False(result.Success);
        using var receipt = JsonDocument.Parse(result.Error["WORKTREE_FAILED ".Length..]);
        Assert.Contains("simulated initialization", receipt.RootElement.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Contains(cleanupError, receipt.RootElement.GetProperty("cleanup_error").GetString(), StringComparison.Ordinal);
        Assert.True(Directory.Exists(target));
        Assert.Equal(0, GitExit(repository.Path, "show-ref", "--verify", "--quiet",
            $"refs/heads/{WorktreeCommand.CreationNamespace}/math/interrupted-init"));
        if (failure == "cleanup-ownership-changed")
            WorktreeFixtureFile.AssertContent(Path.Combine(WorktreeMetadataPath(repository.Path, target), "locked"),
                InitializationFailureRunner.ForeignLock + "\n");
    }

    [Theory]
    [InlineData("sha1", 40, false)]
    [InlineData("sha256", 64, false)]
    [InlineData("sha1", 40, true)]
    [InlineData("sha256", 64, true)]
    public void InitializationRunsPostCheckoutOnceWithCreationArgumentsAndRollsBackHookFailure(
        string objectFormat, int oidLength, bool failHook)
    {
        using var repository = new TemporaryDirectory();
        WorktreeHookFixture.RunGit(repository.Path, "init", "--initial-branch=dev", $"--object-format={objectFormat}");
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "interrupted-init");
        var branch = $"{WorktreeCommand.CreationNamespace}/math/interrupted-init";
        var head = WorktreeHookFixture.RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        var hook = WorktreeHookFixture.Install(repository.Path, "post-checkout", """
            common=$(git rev-parse --git-common-dir)
            printf '%s %s %s\n' "$1" "$2" "$3" >> "$common/post-checkout.log"
            test -f README.md || exit 97
            test -f "$(git rev-parse --git-path locked)" || exit 98
            """ + (failHook ? "\necho 'simulated initialization hook failure' >&2\nexit 1\n" : "\n"));
        WorktreeHookFixture.Install(repository.Path, "reference-transaction", """
            common=$(git rev-parse --git-common-dir)
            printf '%s\n' "$1" >> "$common/reference-transaction.log"
            """ + "\n");

        var result = WorktreeCommand.Run(repository.Path, InitializationArguments(target));

        Assert.Equal(oidLength, head.Length);
        WorktreeFixtureFile.AssertContent(Path.Combine(repository.Path, ".git", "post-checkout.log"),
            $"{new string('0', oidLength)} {head} 1\n");
        Assert.True(File.Exists(Path.Combine(repository.Path, ".git", "reference-transaction.log")));
        if (failHook)
        {
            Assert.False(result.Success);
            Assert.Contains("simulated initialization hook failure", result.Error, StringComparison.Ordinal);
            using var receipt = JsonDocument.Parse(result.Error["WORKTREE_FAILED ".Length..]);
            Assert.Equal(JsonValueKind.Null, receipt.RootElement.GetProperty("cleanup_error").ValueKind);
            Assert.False(Directory.Exists(target));
            Assert.False(Directory.Exists(WorktreeMetadataPath(repository.Path, target)));
            Assert.Equal(1, GitExit(repository.Path, "show-ref", "--verify", "--quiet", $"refs/heads/{branch}"));
            File.Delete(hook);
            result = WorktreeCommand.Run(repository.Path, InitializationArguments(target));
        }
        Assert.True(result.Success, result.Error);
        AssertRegisteredAndUsable(repository.Path, target, branch);
        Assert.False(File.Exists(Path.Combine(WorktreeMetadataPath(repository.Path, target), "locked")));
    }

    private static string[] InitializationArguments(string target) =>
    [
        "--kind", "math", "--name", "interrupted-init",
        "--path", target, "--base", "HEAD", "--skip-restore",
    ];

    private sealed class InitializationFailureRunner(string target, string failure, string? foreignPath = null) : IWorktreeProcessRunner
    {
        internal const string ForeignLock = "worktree-init:ffffffffffffffffffffffffffffffff";
        internal RecordingWorktreeProcessRunner Inner { get; } = new();
        internal string? CreationToken { get; private set; }
        internal string? ChangedBranchOid { get; private set; }
        internal bool CheckoutSawLock { get; private set; }
        internal bool CheckoutSawTrackedContent { get; private set; }

        public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout)
        {
            var branchRef = $"refs/heads/{WorktreeCommand.CreationNamespace}/math/interrupted-init";
            var createBranch = fileName == "git" && arguments.FirstOrDefault() == "update-ref"
                && arguments.Contains("--create-reflog", StringComparer.Ordinal);
            var deleteBranch = fileName == "git" && arguments.FirstOrDefault() == "update-ref"
                && arguments.Contains("-d", StringComparer.Ordinal);
            var add = fileName == "git" && arguments.Take(2).SequenceEqual(["worktree", "add"]);
            var checkout = fileName == "git" && arguments.FirstOrDefault() is "checkout" or "reset";
            var foreignTarget = failure.StartsWith("foreign-elsewhere", StringComparison.Ordinal) ? foreignPath! : target;
            if (fileName == "git" && arguments.FirstOrDefault() == "for-each-ref"
                && failure is "cleanup-branch-recreated" or "cleanup-branch-symbolic")
                ReplaceBranch(workingDirectory, branchRef, failure == "cleanup-branch-symbolic");
            if (add)
            {
                var token = arguments[arguments.ToList().IndexOf("--reason") + 1];
                CreationToken ??= token;
                Assert.Equal(CreationToken, token);
            }
            if (createBranch)
            {
                CreationToken = arguments[arguments.ToList().IndexOf("-m") + 1];
                if (failure.StartsWith("branch-foreign-", StringComparison.Ordinal))
                {
                    WorktreeHookFixture.RunGit(workingDirectory, "update-ref", "--create-reflog", "-m", ForeignLock,
                        branchRef, arguments[^2], arguments[^1]);
                    var rejected = Inner.Run(fileName, arguments, workingDirectory, timeout);
                    Assert.NotEqual(0, rejected.ExitCode);
                    if (failure.EndsWith("timeout", StringComparison.Ordinal))
                        throw new TimeoutException("simulated initialization timeout");
                    return rejected;
                }
            }
            if ((createBranch && failure == "branch-rejected") || (add && failure == "add-rejected"))
            {
                var body = createBranch ? """
                    if [ "$1" = prepared ]; then
                        echo 'simulated initialization rejection' >&2
                        exit 1
                    fi
                    """ : """
                    common=$(git rev-parse --git-common-dir)
                    metadata="$common/worktrees/interrupted-init"
                    if [ "$1" = prepared ] && [ -f "$metadata/commondir" ] && [ -f "$metadata/gitdir" ]; then
                        test -f "$(cat "$metadata/gitdir")"
                        test ! -f "$metadata/HEAD"
                        cat "$metadata/locked" > "$common/rejected-initialization.log"
                        echo 'simulated initialization rejection after linking' >&2
                        exit 1
                    fi
                    """;
                var hook = WorktreeHookFixture.Install(workingDirectory, "reference-transaction", body + "\n");
                ProcessOutput rejected;
                try
                {
                    rejected = Inner.Run(fileName, arguments, workingDirectory, timeout);
                    Assert.NotEqual(0, rejected.ExitCode);
                }
                finally
                {
                    File.Delete(hook);
                }
                Assert.False(Directory.Exists(target));
                Assert.False(Directory.Exists(WorktreeMetadataPath(workingDirectory, target)));
                Assert.DoesNotContain($"worktree {LeanCacheGuard.PhysicalPath(target)}\n",
                    WorktreeHookFixture.RunGit(workingDirectory, "worktree", "list", "--porcelain"), StringComparison.Ordinal);
                Assert.Equal(add ? 0 : 1, GitExit(workingDirectory, "show-ref", "--verify", "--quiet", branchRef));
                if (add)
                    WorktreeFixtureFile.AssertContent(Path.Combine(workingDirectory, ".git", "rejected-initialization.log"),
                        arguments[arguments.ToList().IndexOf("--reason") + 1] + "\n");
                return rejected;
            }
            if (fileName == "git" && arguments.FirstOrDefault() == "reflog" && failure == "branch-receipt-error")
                return new ProcessOutput(1, [], Encoding.UTF8.GetBytes("simulated branch receipt lookup failure"));
            if (deleteBranch && failure == "cleanup-branch-timeout")
                throw new TimeoutException("simulated branch cleanup timeout");
            if (deleteBranch && failure == "cleanup-branch-rejected")
            {
                var hook = WorktreeHookFixture.Install(workingDirectory, "reference-transaction", """
                    if [ "$1" = prepared ]; then
                        echo 'simulated branch cleanup rejection' >&2
                        exit 1
                    fi
                    """ + "\n");
                try
                {
                    return Inner.Run(fileName, arguments, workingDirectory, timeout);
                }
                finally
                {
                    File.Delete(hook);
                }
            }
            if (deleteBranch && failure == "cleanup-branch-race") MoveBranch(workingDirectory, branchRef);
            if (add && failure.EndsWith("prepared", StringComparison.Ordinal))
            {
                var partialArguments = arguments.ToList();
                partialArguments[^2] = foreignTarget;
                var reasonIndex = partialArguments.IndexOf("--reason");
                if (failure.StartsWith("foreign-", StringComparison.Ordinal)) partialArguments[reasonIndex + 1] = ForeignLock;
                var hook = WorktreeHookFixture.Install(workingDirectory, "reference-transaction", $$"""
                    common=$(git rev-parse --git-common-dir)
                    if [ "$1" = prepared ] && [ -f "$common/worktrees/{{Path.GetFileName(foreignTarget)}}/commondir" ]; then
                        kill -KILL "$PPID"
                    fi
                    """ + "\n");
                try
                {
                    var partial = Inner.Run(fileName, partialArguments, workingDirectory, timeout);
                    Assert.NotEqual(0, partial.ExitCode);
                }
                finally
                {
                    File.Delete(hook);
                }
                var metadata = WorktreeMetadataPath(workingDirectory, foreignTarget);
                Assert.False(File.Exists(Path.Combine(metadata, "HEAD")));
                var inventory = WorktreeHookFixture.RunGit(workingDirectory, "worktree", "list", "--porcelain", "-z");
                var fields = Assert.Single(inventory.Split("\0\0", StringSplitOptions.RemoveEmptyEntries)
                    .Select(record => record.Split('\0')),
                    record => record.Contains($"worktree {LeanCacheGuard.PhysicalPath(foreignTarget)}", StringComparer.Ordinal));
                Assert.Contains($"locked {partialArguments[reasonIndex + 1]}", fields);
                Assert.DoesNotContain(fields, field => field.StartsWith("branch ", StringComparison.Ordinal));
                File.WriteAllText(Path.Combine(foreignTarget, "keep.txt"), "concurrent work\n");
                throw new TimeoutException(failure.StartsWith("foreign-", StringComparison.Ordinal)
                    ? "simulated concurrent creator" : "simulated initialization timeout");
            }
            if (add && failure.StartsWith("foreign-", StringComparison.Ordinal))
            {
                var foreignArguments = arguments.ToList();
                foreignArguments[^2] = foreignTarget;
                if (failure == "foreign-detached")
                {
                    foreignArguments.Insert(2, "--detach");
                    foreignArguments[^1] = "HEAD";
                }
                var reasonIndex = foreignArguments.IndexOf("--reason");
                if (reasonIndex >= 0) foreignArguments[reasonIndex + 1] = ForeignLock;
                var foreign = Inner.Run(fileName, foreignArguments, workingDirectory, timeout);
                Assert.Equal(0, foreign.ExitCode);
                var metadata = GitWorktreeDirectory.Read(foreignTarget)!;
                if (failure == "foreign-unlocked" && File.Exists(Path.Combine(metadata, "locked")))
                    TestGit.Run(workingDirectory, "worktree", "unlock", foreignTarget);
                if (failure == "foreign-locked" && !File.Exists(Path.Combine(metadata, "locked")))
                    TestGit.Run(workingDirectory, "worktree", "lock", "--reason", ForeignLock, foreignTarget);
                File.WriteAllText(Path.Combine(foreignTarget, "keep.txt"), "concurrent work\n");
                throw new TimeoutException("simulated concurrent creator");
            }

            if (fileName == "git" && arguments.Take(2).SequenceEqual(["worktree", "remove"])
                && failure == "cleanup-timeout")
                throw new TimeoutException("simulated cleanup timeout");
            if (fileName == "git" && arguments.Take(2).SequenceEqual(["worktree", "remove"])
                && failure == "cleanup-ownership-changed")
            {
                File.WriteAllText(Path.Combine(GitWorktreeDirectory.Read(target)!, "locked"), ForeignLock + "\n");
                return new ProcessOutput(1, [], Encoding.UTF8.GetBytes("simulated git removal failure"));
            }

            if (checkout)
            {
                var metadata = GitWorktreeDirectory.Read(target)!;
                CheckoutSawLock = File.Exists(Path.Combine(metadata, "locked"));
                WorktreeFixtureFile.AssertContent(Path.Combine(metadata, "locked"), CreationToken + "\n");
                CheckoutSawTrackedContent = File.Exists(Path.Combine(target, "README.md"));
                if (failure.StartsWith("checkout-", StringComparison.Ordinal))
                {
                    File.WriteAllText(Path.Combine(target, "README.md"), "partial checkout\n");
                    if (failure == "checkout-index-lock") File.WriteAllText(Path.Combine(metadata, "index.lock"), string.Empty);
                    return FailInitialization(failure);
                }
            }

            var result = Inner.Run(fileName, arguments, workingDirectory, timeout);
            if (createBranch && result.ExitCode == 0 && failure.StartsWith("branch-", StringComparison.Ordinal))
            {
                Assert.Equal($"{arguments[^2]}\t{CreationToken}\n",
                    WorktreeHookFixture.RunGit(workingDirectory, "reflog", "show", "-1", "--format=%H%x09%gs", branchRef));
                Assert.False(Directory.Exists(target));
                Assert.False(Directory.Exists(WorktreeMetadataPath(workingDirectory, target)));
                if (failure == "branch-changed") MoveBranch(workingDirectory, branchRef);
                if (failure == "branch-recreated") ReplaceBranch(workingDirectory, branchRef, false);
                return FailInitialization(failure);
            }
            if (add && result.ExitCode == 0 && failure == "cleanup-branch-changed") MoveBranch(workingDirectory, branchRef);
            if (add && result.ExitCode == 0 && failure.StartsWith("add-invalid-", StringComparison.Ordinal))
                File.WriteAllText(Path.Combine(GitWorktreeDirectory.Read(target)!, failure["add-invalid-".Length..]),
                    foreignPath + "\n");
            if (add && result.ExitCode == 0
                && (failure.StartsWith("add-", StringComparison.Ordinal) || failure.StartsWith("cleanup-", StringComparison.Ordinal)))
                return FailInitialization(failure);
            return result;
        }

        private void ReplaceBranch(string repository, string branchRef, bool symbolic)
        {
            ChangedBranchOid = WorktreeHookFixture.RunGit(repository, "rev-parse", "HEAD").Trim();
            WorktreeHookFixture.RunGit(repository, "update-ref", "--no-deref", "-d", branchRef, ChangedBranchOid);
            if (symbolic)
            {
                var targetRef = WorktreeHookFixture.RunGit(repository, "symbolic-ref", "HEAD").Trim();
                WorktreeHookFixture.RunGit(repository, "symbolic-ref", branchRef, targetRef);
            }
            else
                WorktreeHookFixture.RunGit(repository, "update-ref", "--create-reflog", "-m", ForeignLock,
                    branchRef, ChangedBranchOid, new string('0', ChangedBranchOid.Length));
        }

        private void MoveBranch(string repository, string branchRef)
        {
            ChangedBranchOid = WorktreeHookFixture.RunGit(repository,
                "commit-tree", "HEAD^{tree}", "-p", "HEAD", "-m", "concurrent branch update").Trim();
            WorktreeHookFixture.RunGit(repository, "update-ref", "-m", "concurrent branch update", branchRef, ChangedBranchOid);
        }

        private static ProcessOutput FailInitialization(string failure)
        {
            if (failure.EndsWith("nonzero", StringComparison.Ordinal))
                return new ProcessOutput(1, [], Encoding.UTF8.GetBytes("simulated initialization failure"));
            throw new TimeoutException("simulated initialization timeout");
        }
    }
}
