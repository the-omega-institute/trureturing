using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed class WorktreeCommandTests
{
    [Fact]
    public void RootUsageListsWorktreeCommand()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            Array.Empty<string>(),
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        // usage 由 dispatch 表渲染,所以这里验「它列出了每一个实现着的动词」,而不是再抄
        // 一份会漂移的清单——原先那份手抄仍在点名早已删除的 golden-record。
        Assert.Contains("worktree", CliApplication.ImplementedCommands);
        Assert.All(
            CliApplication.ImplementedCommands,
            command => Assert.Contains(command, console.Error, StringComparison.Ordinal));
        Assert.DoesNotContain("|lean-cache|", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void CliDispatchesLeanCacheEnsureThroughWorktree()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["worktree", "ensure-cache"],
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(0, exitCode);
        Assert.Contains("present", console.Output, StringComparison.Ordinal);
        Assert.Empty(console.Error);
    }

    [Fact]
    public void WriterEntryConvergesBeforeStartingLakeBuild()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["with-cache-writer", "--", "lake", "build"],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Equal(
            ["get", "clean", "build"],
            runner.Invocations
                .Where(static call => call.FileName == "lake")
                .Select(static call => call.Arguments.Last())
                .ToArray());
        Assert.True(LeanCacheStamp.Matches(
            Path.Combine(repository.Path, ".lake"),
            ReadPins(repository.Path),
            out _));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(
            System.Text.Json.JsonValueKind.Null,
            receipt.RootElement.GetProperty("mathlib_missing_olean_files").ValueKind);
    }

    [Fact]
    public void WriterEntryRejectsExitZeroCacheGetWhenMathlibOleansAreMissing()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["with-cache-writer", "--", "lake", "build"],
            runner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        Assert.False(Directory.Exists(Path.Combine(repository.Path, ".lake")));
        Assert.False(File.Exists(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake"))));
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal(
            MathlibProjectionFixture.ModuleCount,
            receipt.RootElement.GetProperty("mathlib_missing_olean_files").GetInt32());
        Assert.Contains(
            receipt.RootElement.GetProperty("mathlib_missing_olean_samples").EnumerateArray(),
            sample => sample.GetString() == MathlibProjectionFixture.FirstModule);
    }

    [Fact]
    public void WriterEntryRejectsStampedCacheThatLostAnOleanBeforeStartingCommand()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        MathlibProjectionFixture.RemoveAllOleans(Path.Combine(repository.Path, ".lake"));
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["with-cache-writer", "--", "lake", "build"],
            runner);

        Assert.False(result.Success);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Error);
        Assert.Equal(
            MathlibProjectionFixture.ModuleCount,
            receipt.RootElement.GetProperty("mathlib_missing_olean_files").GetInt32());
    }

    [Fact]
    public void WriterEntryNeverStartsBuildWhenProvisioningFails()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner { FailLake = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["with-cache-writer", "--", "lake", "build"],
            runner);

        Assert.False(result.Success);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
    }

    [Fact]
    public void ParseUsesCanonicalDefaults()
    {
        var parsed = WorktreeCommand.ParseArguments(
            "/repo",
            new[] { "--branch", "harness/worktree-probe", "--path", "/tmp/probe" });

        Assert.Equal("harness/worktree-probe", parsed.Branch);
        Assert.Equal(Path.GetFullPath("/tmp/probe"), parsed.Path);
        Assert.Equal("origin/dev", parsed.Base);
        Assert.Equal(Path.GetFullPath("/repo"), parsed.Source);
        Assert.False(parsed.SkipRestore);
    }

    [Fact]
    public void ParseAcceptsEveryFlagInAnyOrder()
    {
        var parsed = WorktreeCommand.ParseArguments(
            "/repo",
            new[]
            {
                "--skip-restore",
                "--source", "/source",
                "--base", "HEAD",
                "--path", "/tmp/probe",
                "--branch", "agent/prover/D5-T0099",
            });

        Assert.Equal("agent/prover/D5-T0099", parsed.Branch);
        Assert.Equal("HEAD", parsed.Base);
        Assert.Equal(Path.GetFullPath("/source"), parsed.Source);
        Assert.True(parsed.SkipRestore);
    }

    [Fact]
    public void UsageForbidsSharedLakeSymlinks()
    {
        Assert.Contains("--skip-restore", WorktreeCommand.Usage, StringComparison.Ordinal);
        Assert.Contains("symlink", WorktreeCommand.Usage, StringComparison.OrdinalIgnoreCase);
        Assert.Contains(".lake", WorktreeCommand.Usage, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("feature/probe")]
    [InlineData("harness")]
    [InlineData("harness/")]
    [InlineData("agent/prover")]
    [InlineData("agent/prover/task/extra")]
    public void ParseRejectsBranchOutsideBranchLockGrammar(string branch)
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
            WorktreeCommand.ParseArguments(
                "/repo",
                new[] { "--branch", branch, "--path", "/tmp/probe" }));

        Assert.Contains("harness/* or agent/<official>/<task-code>", exception.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("--branch", "harness/probe")]
    [InlineData("--path", "/tmp/probe")]
    [InlineData("--unknown", "value")]
    public void ParseRejectsMissingOrUnknownArguments(string flag, string value)
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
            WorktreeCommand.ParseArguments("/repo", new[] { flag, value }));

        Assert.Contains("USAGE: StrataLint worktree", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CommandSelectsMatchingDonorAndClonesIndependentLakeCache()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var cacheFile = Path.Combine(repository.Path, ".lake", "build", "cache.bin");
        Directory.CreateDirectory(Path.GetDirectoryName(cacheFile)!);
        File.WriteAllText(cacheFile, "warm cache\n");
        StampCache(repository.Path);
        var target = Path.Combine(repository.Path, "provisioned");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[]
            {
                "worktree",
                "--branch", "harness/integration-probe",
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
                "--skip-restore",
            },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(0, exitCode);
        Assert.Equal("harness/integration-probe", ReviewRegressionTests.RunGit(target, "branch", "--show-current").Trim());
        Assert.Equal("warm cache\n", File.ReadAllText(Path.Combine(target, ".lake", "build", "cache.bin")));
        File.WriteAllText(cacheFile, "donor changed\n");
        Assert.Equal("warm cache\n", File.ReadAllText(Path.Combine(target, ".lake", "build", "cache.bin")));
        AssertReviewScaffoldsAreIgnored(target);
        Assert.Contains("\"event\":\"worktree_init\"", console.Output, StringComparison.Ordinal);
        Assert.Contains("\"branch\":\"harness/integration-probe\"", console.Output, StringComparison.Ordinal);
        Assert.Contains(
            $"\"donor\":\"{LeanCacheGuard.PhysicalPath(repository.Path)}\"",
            console.Output,
            StringComparison.Ordinal);
        Assert.Contains("\"pin_sha256\":\"", console.Output, StringComparison.Ordinal);
        Assert.Contains("\"cache_strategy\":\"cloned\"", console.Output, StringComparison.Ordinal);
        Assert.Contains("\"shared_cache_scope\":\"machine\"", console.Output, StringComparison.Ordinal);
        Assert.Contains("\"mathlib_cache_pruned_files\":0", console.Output, StringComparison.Ordinal);
        Assert.Contains("\"mathlib_cache_clean_status\":\"not-run\"", console.Output, StringComparison.Ordinal);
        Assert.Contains("\"elapsed_ms\":", console.Output, StringComparison.Ordinal);
        if (OperatingSystem.IsMacOS())
        {
            Assert.Contains("\"cache_method\":\"clonefile\"", console.Output, StringComparison.Ordinal);
            Assert.Equal(string.Empty, console.Error);
        }
        else
        {
            Assert.Contains("\"cache_method\":\"copy\"", console.Output, StringComparison.Ordinal);
            Assert.Contains("clonefile failed", console.Error, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void CommandHoldsTargetWriterGuardThroughoutProvisioning()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        var target = Path.Combine(repository.Path, "guarded-provision");
        bool? concurrentWriterAcquired = null;
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) =>
            {
                using var concurrent = LeanCacheGuard.TryAcquireExclusive(Path.Combine(target, ".lake"));
                concurrentWriterAcquired = concurrent is not null;
            },
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/guarded-provision",
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
                "--skip-restore",
            ],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.False(concurrentWriterAcquired);
    }

    [Fact]
    public void BusyTargetWriterFailsClosedWithoutDeletingTheActiveWritersWorktree()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        var target = Path.Combine(repository.Path, "busy-target-writer");
        LeanCacheGuard? activeWriter = null;
        var runner = new RecordingWorktreeProcessRunner
        {
            AfterWorktreeAdd = addedTarget =>
            {
                var lake = Path.Combine(addedTarget, ".lake");
                activeWriter = LeanCacheGuard.TryAcquireExclusive(lake);
                Assert.NotNull(activeWriter);
                Directory.CreateDirectory(lake);
                File.WriteAllText(Path.Combine(lake, "active-writer.marker"), "owned\n");
            },
        };
        try
        {
            var result = WorktreeCommand.Run(
                repository.Path,
                [
                    "--branch", "harness/busy-target-writer",
                    "--path", target,
                    "--base", "HEAD",
                    "--source", repository.Path,
                    "--skip-restore",
                ],
                runner,
                new RecordingDirectoryCloner());

            Assert.False(result.Success);
            Assert.Contains("writer guard is busy", result.Error, StringComparison.OrdinalIgnoreCase);
            Assert.True(File.Exists(Path.Combine(target, ".lake", "active-writer.marker")));
        }
        finally
        {
            activeWriter?.Dispose();
        }
    }

    [Fact]
    public void WorktreeFailureReceiptRetainsMachinePruneOutcomeAfterStampFailure()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "stamp-failure");
        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/stamp-failure",
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
                "--skip-restore",
            ],
            new RecordingWorktreeProcessRunner { BlockStampAfterClean = true },
            new RecordingDirectoryCloner());

        Assert.False(result.Success);
        Assert.StartsWith("WORKTREE_FAILED ", result.Error, StringComparison.Ordinal);
        using var receipt = System.Text.Json.JsonDocument.Parse(
            result.Error["WORKTREE_FAILED ".Length..]);
        Assert.Equal("failed", receipt.RootElement.GetProperty("status").GetString());
        Assert.Equal("machine", receipt.RootElement.GetProperty("shared_cache_scope").GetString());
        Assert.Equal(1, receipt.RootElement.GetProperty("mathlib_cache_pruned_files").GetInt32());
        Assert.Equal("succeeded", receipt.RootElement.GetProperty("mathlib_cache_clean_status").GetString());
    }

    [Fact]
    public void CommandAppendsOnlyMissingReviewScaffoldIgnores()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        File.WriteAllText(
            Path.Combine(repository.Path, ".gitignore"),
            "existing-output/\r\n.echo-review.md");
        ReviewRegressionTests.RunGit(repository.Path, "add", ".gitignore");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "fixture ignore policy");
        var cacheFile = Path.Combine(repository.Path, ".lake", "build", "cache.bin");
        Directory.CreateDirectory(Path.GetDirectoryName(cacheFile)!);
        File.WriteAllText(cacheFile, "warm cache\n");
        StampCache(repository.Path);
        var target = Path.Combine(repository.Path, "provisioned-with-ignore");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "worktree",
                "--branch", "harness/ignore-probe",
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
                "--skip-restore",
            ],
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(0, exitCode);
        Assert.Equal(
            "existing-output/\r\n.echo-review.md\r\n.caller-review-prompt.md\r\n.sshx-*\r\n",
            File.ReadAllText(Path.Combine(target, ".gitignore")));
        AssertReviewScaffoldsAreIgnored(target);
    }

    [Fact]
    public void CommandLeavesCompleteReviewScaffoldIgnoresByteExactAndClean()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string expected =
            "/.lake/\n.caller-review-prompt.md\n.echo-review.md\n.sshx-*\n";
        File.WriteAllText(Path.Combine(repository.Path, ".gitignore"), expected);
        ReviewRegressionTests.RunGit(repository.Path, "add", ".gitignore");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "fixture complete ignore policy");
        var cacheFile = Path.Combine(repository.Path, ".lake", "build", "cache.bin");
        Directory.CreateDirectory(Path.GetDirectoryName(cacheFile)!);
        File.WriteAllText(cacheFile, "warm cache\n");
        StampCache(repository.Path);
        var target = Path.Combine(repository.Path, "provisioned-clean");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "worktree",
                "--branch", "harness/clean-ignore-probe",
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
                "--skip-restore",
            ],
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(0, exitCode);
        Assert.Equal(expected, File.ReadAllText(Path.Combine(target, ".gitignore")));
        Assert.Equal(string.Empty, ReviewRegressionTests.RunGit(target, "status", "--porcelain"));
    }

    [Fact]
    public void IgnoreWriteFailureRollsBackWorktreeAndBranch()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var ignoreDirectory = Path.Combine(repository.Path, ".gitignore");
        Directory.CreateDirectory(ignoreDirectory);
        File.WriteAllText(Path.Combine(ignoreDirectory, "marker"), "fixture\n");
        ReviewRegressionTests.RunGit(repository.Path, "add", ".gitignore/marker");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "fixture invalid ignore path");
        const string branch = "harness/ignore-write-failure";
        var target = Path.Combine(repository.Path, "ignore-write-failure");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "worktree",
                "--branch", branch,
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
                "--skip-restore",
            ],
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("WORKTREE_FAILED", console.Error, StringComparison.Ordinal);
        Assert.False(Directory.Exists(target));
        var branchLookup = BoundedProcessRunner.Run(
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{branch}"],
            repository.Path,
            TimeSpan.FromSeconds(30),
            4096);
        Assert.Equal(1, branchLookup.ExitCode);
    }

    [Fact]
    public void CommandRejectsExistingPathBeforeGitMutation()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "existing");
        Directory.CreateDirectory(target);
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[]
            {
                "worktree",
                "--branch", "harness/existing-path",
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
            },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("path already exists", console.Error, StringComparison.Ordinal);
        Assert.True(Directory.Exists(target));
    }

    [Fact]
    public void CommandRejectsUnresolvableBaseBeforeGitMutation()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "invalid-base");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[]
            {
                "worktree",
                "--branch", "harness/invalid-base",
                "--path", target,
                "--base", "missing-revision",
                "--source", repository.Path,
            },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("WORKTREE_FAILED", console.Error, StringComparison.Ordinal);
        Assert.False(Directory.Exists(target));
        var branchLookup = BoundedProcessRunner.Run(
            "git",
            new[] { "show-ref", "--verify", "--quiet", "refs/heads/harness/invalid-base" },
            repository.Path,
            TimeSpan.FromSeconds(30),
            4096);
        Assert.Equal(1, branchLookup.ExitCode);
    }

    [Fact]
    public void CommandRejectsExistingBranchBeforeGitMutation()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string branch = "harness/already-present";
        ReviewRegressionTests.RunGit(repository.Path, "branch", branch, "HEAD");
        var target = Path.Combine(repository.Path, "branch-conflict");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "worktree",
                "--branch", branch,
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
                "--skip-restore",
            ],
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("branch already exists", console.Error, StringComparison.Ordinal);
        Assert.False(Directory.Exists(target));
    }

    private static void InitializeRepository(string root)
    {
        ReviewRegressionTests.RunGit(root, "init", "--initial-branch=dev");
        ReviewRegressionTests.RunGit(root, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(root, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(Path.Combine(root, "README.md"), "# worktree fixture\n");
        File.WriteAllText(Path.Combine(root, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(root, "lake-manifest.json"), "{\"version\": \"1.1.0\"}\n");
        ReviewRegressionTests.RunGit(root, "add", "README.md", "lean-toolchain", "lake-manifest.json");
        ReviewRegressionTests.RunGit(root, "commit", "-m", "fixture baseline");
    }

    private static void StampCache(string root)
    {
        var lake = Path.Combine(root, ".lake");
        Directory.CreateDirectory(lake);
        MathlibProjectionFixture.Write(lake);
        LeanCacheStamp.Write(lake, ReadPins(root));
    }

    private static LeanPinSet ReadPins(string root) =>
        LeanPinSet.TryReadWorktree(root, out var reason)
        ?? throw new InvalidOperationException(reason);

    private static System.Text.Json.JsonDocument ParseReceipt(string output) =>
        System.Text.Json.JsonDocument.Parse(output["LEAN_CACHE ".Length..]);

    private static void AssertReviewScaffoldsAreIgnored(string root)
    {
        foreach (var path in new[] { ".caller-review-prompt.md", ".echo-review.md", ".sshx-review" })
        {
            var result = BoundedProcessRunner.Run(
                "git",
                ["check-ignore", "--quiet", "--no-index", path],
                root,
                TimeSpan.FromSeconds(30),
                4096);
            Assert.Equal(0, result.ExitCode);
        }
    }
}
