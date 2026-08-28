using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed partial class WorktreeCommandTests
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
        using var environment = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        MathlibProjectionFixture.Write(Path.Combine(repository.Path, ".lake"));
        var lake = Path.Combine(environment.Path, "toolchain", "lake");
        Directory.CreateDirectory(Path.GetDirectoryName(lake)!);
        File.WriteAllText(lake, "fake lake\n");
        var runner = new RecordingWorktreeProcessRunner { LakeFileName = lake };

        WithLakeResolutionEnvironment(
            path: environment.Path,
            home: environment.Path,
            action: () =>
            {
                var result = WorktreeCommand.Run(
                    repository.Path,
                    ["with-cache-writer", "--", lake, "build"],
                    runner);

                Assert.True(result.Success, result.Error);
                using var receipt = ParseReceipt(result.Output);
                Assert.Equal(0, receipt.RootElement.GetProperty("mathlib_missing_olean_files").GetInt32());
            });

        Assert.Equal(
            [lake, lake],
            runner.Invocations
                .Where(invocation => invocation.FileName == lake)
                .Select(static invocation => invocation.FileName)
                .ToArray());
        Assert.Equal(
            ["get", "build"],
            runner.Invocations
                .Where(invocation => invocation.FileName == lake)
                .Select(static invocation => invocation.Arguments.Last())
                .ToArray());
        Assert.True(LeanCacheStamp.Matches(
            Path.Combine(repository.Path, ".lake"),
            ReadPins(repository.Path),
            out _));
    }

    [Fact]
    public void WriterEntryReportsMissingMathlibOleansAndContinuesWhenProjectIsWarm()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        _ = ProjectOleanFixture.Write(repository.Path, "ExistingProject");
        var runner = new RecordingWorktreeProcessRunner { OmitMathlibOleans = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["with-cache-writer", "--", "lake", "build"],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        Assert.True(Directory.Exists(Path.Combine(repository.Path, ".lake")));
        Assert.True(File.Exists(LeanCacheStamp.PathFor(Path.Combine(repository.Path, ".lake"))));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(
            MathlibProjectionFixture.ModuleCount,
            receipt.RootElement.GetProperty("mathlib_missing_olean_files").GetInt32());
        Assert.Contains(
            receipt.RootElement.GetProperty("mathlib_missing_olean_samples").EnumerateArray(),
            sample => sample.GetString() == MathlibProjectionFixture.FirstModule);
    }

    [Fact]
    public void WriterEntryReportsStampedCacheMissingOleansAndStartsCommand()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        MathlibProjectionFixture.RemoveAllOleans(Path.Combine(repository.Path, ".lake"));
        _ = ProjectOleanFixture.Write(repository.Path, "ExistingProject");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            repository.Path,
            ["with-cache-writer", "--", "lake", "build"],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(
            MathlibProjectionFixture.ModuleCount,
            receipt.RootElement.GetProperty("mathlib_missing_olean_files").GetInt32());
    }

    [Fact]
    public void WriterEntryContinuesToLakeBuildWhenCacheGetFails()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        _ = ProjectOleanFixture.Write(repository.Path, "ExistingProject");
        var runner = new RecordingWorktreeProcessRunner { FailLake = true };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["with-cache-writer", "--", "lake", "build"],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Contains(
            runner.Invocations,
            static call => call.FileName == "lake" && call.Arguments.SequenceEqual(["build"]));
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal("degraded", receipt.RootElement.GetProperty("status").GetString());
        Assert.Contains(
            "cache get failed",
            receipt.RootElement.GetProperty("reason").GetString()!,
            StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void EnsureCacheFailsClosedWhenLakeCannotBeResolved()
    {
        using var repository = new TemporaryDirectory();
        using var environment = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var runner = new RecordingWorktreeProcessRunner();
        MathlibProjectionFixture.Write(Path.Combine(repository.Path, ".lake"));
        WithLakeResolutionEnvironment(
            path: environment.Path,
            home: environment.Path,
            action: () =>
            {
                var result = WorktreeCommand.Run(repository.Path, ["ensure-cache"], runner);

                Assert.False(result.Success);
                Assert.Empty(result.Output);
                using var receipt = ParseReceipt(result.Error);
                var reason = receipt.RootElement.GetProperty("reason").GetString()!;
                Assert.Contains("LAKE_BIN", reason, StringComparison.Ordinal);
                Assert.Contains(Path.Combine(environment.Path, "lake"), reason, StringComparison.Ordinal);
                Assert.Contains(
                    Path.Combine(environment.Path, ".elan", "bin", "lake"),
                    reason,
                    StringComparison.Ordinal);
            });
        Assert.Empty(runner.Invocations);
    }

    [Fact]
    public void ParseUsesCanonicalDefaults()
    {
        var parsed = WorktreeCommand.ParseArguments(
            "/repo",
            new[] { "--branch", "harness/math/worktree-probe", "--path", "/tmp/probe" });

        Assert.Equal("harness/math/worktree-probe", parsed.Branch);
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
                "--branch", "harness/math/D5-T0099",
            });

        Assert.Equal("harness/math/D5-T0099", parsed.Branch);
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
    [InlineData("--branch", "harness/math/probe")]
    [InlineData("--path", "/tmp/probe")]
    [InlineData("--unknown", "value")]
    public void ParseRejectsMissingOrUnknownArguments(string flag, string value)
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
            WorktreeCommand.ParseArguments("/repo", new[] { flag, value }));

        Assert.Contains("USAGE: StrataLint worktree", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void WorktreeCreationDoesNotProvisionLeanCache()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        var target = Path.Combine(repository.Path, "lazy-cache");
        var runner = new RecordingWorktreeProcessRunner();
        var cloner = new RecordingDirectoryCloner();

        var result = WorktreeCommand.Run(
            repository.Path,
            [
                "--branch", "harness/math/lazy-cache",
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
                "--skip-restore",
            ],
            runner,
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(Path.Combine(target, ".lake")));
        Assert.Empty(cloner.Invocations);
        Assert.DoesNotContain(
            runner.Invocations,
            static call => (Path.GetFileName(call.FileName) == "lake"
                    && call.Arguments.SequenceEqual(["exe", "cache", "get"]))
                || (call.FileName == "cp" && call.Arguments.FirstOrDefault() == "-R"));
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
        var target = Path.Combine(repository.Path, "provisioned-with-ignore");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "worktree",
                "--branch", "harness/math/ignore-probe",
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
        var target = Path.Combine(repository.Path, "provisioned-clean");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "worktree",
                "--branch", "harness/math/clean-ignore-probe",
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
        const string branch = "harness/math/ignore-write-failure";
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
        var branchLookup = TestProcessRunner.Run(
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{branch}"],
            repository.Path,
            BoundedProcessRunner.HangDetectionBudget,
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
                "--branch", "harness/math/existing-path",
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
                "--branch", "harness/math/invalid-base",
                "--path", target,
                "--base", "missing-revision",
                "--source", repository.Path,
            },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("WORKTREE_FAILED", console.Error, StringComparison.Ordinal);
        Assert.False(Directory.Exists(target));
        var branchLookup = TestProcessRunner.Run(
            "git",
            new[] { "show-ref", "--verify", "--quiet", "refs/heads/harness/math/invalid-base" },
            repository.Path,
            BoundedProcessRunner.HangDetectionBudget,
            4096);
        Assert.Equal(1, branchLookup.ExitCode);
    }

    [Fact]
    public void CommandRejectsExistingBranchBeforeGitMutation()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        const string branch = "harness/math/already-present";
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

    private static void WithLakeResolutionEnvironment(string path, string home, Action action)
    {
        var previousLake = Environment.GetEnvironmentVariable("LAKE_BIN");
        var previousPath = Environment.GetEnvironmentVariable("PATH");
        var previousHome = Environment.GetEnvironmentVariable("HOME");
        try
        {
            Environment.SetEnvironmentVariable("LAKE_BIN", null);
            Environment.SetEnvironmentVariable("PATH", path);
            Environment.SetEnvironmentVariable("HOME", home);
            action();
        }
        finally
        {
            Environment.SetEnvironmentVariable("LAKE_BIN", previousLake);
            Environment.SetEnvironmentVariable("PATH", previousPath);
            Environment.SetEnvironmentVariable("HOME", previousHome);
        }
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
            var result = TestProcessRunner.Run(
                "git",
                ["check-ignore", "--quiet", "--no-index", path],
                root,
                BoundedProcessRunner.HangDetectionBudget,
                4096);
            Assert.Equal(0, result.ExitCode);
        }
    }
}

public sealed partial class LeanCacheEnsureCommandTests
{
    [Fact]
    public void DonorGuardsAreSharedWhileCanonicalWriterGuardIsExclusive()
    {
        using var root = new TemporaryDirectory();
        var lake = Path.Combine(root.Path, ".lake");
        using var first = LeanCacheGuard.TryAcquireShared(lake);
        using var second = LeanCacheGuard.TryAcquireShared(lake);

        Assert.NotNull(first);
        Assert.NotNull(second);
        using var writer = LeanCacheGuard.TryAcquireExclusive(lake);
        Assert.Null(writer);
    }

    [Fact]
    public void BusyTargetWriterFailsClosedBeforeEnsuring()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = AddWorktree(repository.Path, "busy-writer-target");
        var runner = new RecordingWorktreeProcessRunner();
        using var busy = LeanCacheWriterGuard.TryAcquire(Path.Combine(target, ".lake"));
        Assert.NotNull(busy);

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.False(result.Success);
        Assert.Contains("busy", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Empty(runner.Invocations);
    }

    [Fact]
    public void EnsureHoldsTargetWriterGuardThroughoutProvisioning()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "guarded donor cache\n");
        var target = AddWorktree(repository.Path, "guarded-target");
        bool? concurrentWriterAcquired = null;
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = (_, _) =>
            {
                using var concurrent = LeanCacheWriterGuard.TryAcquire(Path.Combine(target, ".lake"));
                concurrentWriterAcquired = concurrent is not null;
            },
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.False(concurrentWriterAcquired);
    }

    [Fact]
    public void MissingLakeCanBeSeededFromAnotherRegisteredWorktree()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var donor = AddWorktree(repository.Path, "registered-donor");
        WriteCache(donor, "registered donor cache\n");
        var target = AddWorktree(repository.Path, "registered-target");

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(
            LeanCacheGuard.PhysicalPath(donor),
            receipt.RootElement.GetProperty("donor").GetString());
        Assert.Equal(
            "registered donor cache\n",
            LeanCacheFixtureFile.ReadText(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.True(LeanCacheStamp.Matches(Path.Combine(target, ".lake"), ReadPins(target), out _));
    }

    [Fact]
    public void BusyDonorIsSkippedAndEnsureUsesCacheGet()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var donor = AddWorktree(repository.Path, "busy-donor");
        WriteCache(donor, "busy cache\n");
        var target = AddWorktree(repository.Path, "busy-target");
        using var busy = LeanCacheGuard.TryAcquireExclusive(Path.Combine(donor, ".lake"));
        Assert.NotNull(busy);

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        Assert.Contains("busy", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
    }

    [Fact]
    public void CwdBusyProbeSkipsDonorWithoutTreatingTheProbeAsProof()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "busy cache\n");
        var target = AddWorktree(repository.Path, "cwd-busy-target");
        var runner = new RecordingWorktreeProcessRunner { BusyRoot = repository.Path };
        Assert.True(LeanCacheBusyProbe.IsBusy(repository.Path, runner));

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Contains("busy", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.DoesNotContain(runner.Invocations, static call => call.FileName == "cp");
    }

    [Fact]
    public void DonorBecomingBusyAfterStagingFallsBackWithoutPublishingTheCopy()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "copy raced cache\n");
        var target = AddWorktree(repository.Path, "post-copy-busy");
        var runner = new RecordingWorktreeProcessRunner
        {
            BusyRoot = repository.Path,
            BusyOnlyAfterCopy = true,
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            runner,
            new RecordingDirectoryCloner { FailureReason = "clonefile unavailable" });

        Assert.True(result.Success, result.Error);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.Empty(Directory.EnumerateDirectories(target, ".lake.stage-*"));
        Assert.True(LeanCacheStamp.Matches(Path.Combine(target, ".lake"), ReadPins(target), out _));
    }

    [Fact]
    public void DonorStampChangingAfterStagingFallsBackWithoutPublishingTheCopy()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "copy raced stamp\n");
        var target = AddWorktree(repository.Path, "post-copy-stamp-change");
        var cloner = new RecordingDirectoryCloner
        {
            AfterClone = static (source, _) => File.Delete(LeanCacheStamp.PathFor(source)),
        };

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner(),
            cloner);

        Assert.True(result.Success, result.Error);
        Assert.Single(cloner.Invocations);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.Exists(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.Empty(Directory.EnumerateDirectories(target, ".lake.stage-*"));
        Assert.True(LeanCacheStamp.Matches(Path.Combine(target, ".lake"), ReadPins(target), out _));
    }

    [Fact]
    public void LakeSymlinkIsRejectedAsDonor()
    {
        using var repository = new TemporaryDirectory();
        using var sharedCache = new MathlibCacheFixture();
        InitializeRepository(repository.Path);
        var realCache = Path.Combine(repository.Path, "real-cache");
        Directory.CreateDirectory(realCache);
        Directory.CreateSymbolicLink(Path.Combine(repository.Path, ".lake"), realCache);
        var target = AddWorktree(repository.Path, "symlink-donor-target");

        var result = WorktreeCommand.Run(
            repository.Path,
            ["ensure-cache", "--path", target],
            new RecordingWorktreeProcessRunner());

        Assert.True(result.Success, result.Error);
        Assert.Contains("symlink", result.Output, StringComparison.OrdinalIgnoreCase);
        Assert.True(File.Exists(Path.Combine(target, ".lake", "cache-get.marker")));
        Assert.False(File.GetAttributes(Path.Combine(target, ".lake")).HasFlag(FileAttributes.ReparsePoint));
    }

    [Fact]
    public void ClonefileCleanupFailureReceiptSerializesInjectedError()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        WriteCache(repository.Path, "cleanup failure donor cache\n");
        var target = AddWorktree(repository.Path, "cleanup-failure-target");
        var cloner = new RecordingDirectoryCloner
        {
            Results = new Queue<DirectoryCloneResult>(
                [new(false, true, 5, 1, "clonefile(2) failed: EIO")]),
            AfterClone = (_, path) => Directory.CreateDirectory(path),
        };
        var cleanupCalls = 0;
        void Cleanup(string path)
        {
            cleanupCalls++;
            if (cleanupCalls == 1) throw new IOException("injected clone retry cleanup failure");
            if (Directory.Exists(path)) Directory.Delete(path, recursive: true);
        }
        var runner = new RecordingWorktreeProcessRunner();

        var result = LeanCacheEnsureCommand.Run(
            repository.Path,
            ["--path", target],
            runner,
            cloner,
            Cleanup);

        Assert.True(result.Success, result.Error);
        Assert.Empty(result.Error);
        Assert.Equal(2, cleanupCalls);
        using var receipt = ParseReceipt(result.Output);
        Assert.Equal(
            "injected clone retry cleanup failure",
            receipt.RootElement.GetProperty("clonefile_cleanup_error").GetString());
    }
}
