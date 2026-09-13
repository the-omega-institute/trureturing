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
            new[] { "--kind", "math", "--name", "worktree-probe", "--path", "/tmp/probe" });

        Assert.Equal(
            $"{WorktreeCommand.CreationNamespace}/math/worktree-probe",
            parsed.Branch);
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
                "--name", "D5-T0099",
                "--kind", "math",
            });

        Assert.Equal($"{WorktreeCommand.CreationNamespace}/math/D5-T0099", parsed.Branch);
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
    [InlineData("--branch", "feature/probe")]
    [InlineData("--kind", "math")]
    [InlineData("--name", "probe")]
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
                "--kind", "math",
                "--name", "lazy-cache",
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
                "--kind", "math",
                "--name", "ignore-probe",
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
                "--kind", "math",
                "--name", "clean-ignore-probe",
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
        var branch = $"{WorktreeCommand.CreationNamespace}/math/ignore-write-failure";
        var target = Path.Combine(repository.Path, "ignore-write-failure");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "worktree",
                "--kind", "math",
                "--name", "ignore-write-failure",
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
                "--kind", "math",
                "--name", "existing-path",
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
                "--kind", "math",
                "--name", "invalid-base",
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
            [
                "show-ref", "--verify", "--quiet",
                $"refs/heads/{WorktreeCommand.CreationNamespace}/math/invalid-base",
            ],
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
        var branch = $"{WorktreeCommand.CreationNamespace}/math/already-present";
        ReviewRegressionTests.RunGit(repository.Path, "branch", branch, "HEAD");
        var target = Path.Combine(repository.Path, "branch-conflict");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [
                "worktree",
                "--kind", "math",
                "--name", "already-present",
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

// 本类的其余测试已迁往 Commands/Worktrees/LeanCacheEnsureCommandTests.WorktreeIntegration.cs。
// 这一个留在原处**不是疏漏**:SL-003 的 unknown 棘轮按 (PartitionKey, SourcePath, Id)
// 认身份,而该方法被派生器判为 conservative unknown;换文件即造新身份,判词原文:
//   SL-003 …WorktreeIntegration.cs: conservative unknown test method introduced after
//   fork point: tools/tests/StrataLint.Tests::LeanCacheEnsureCommandTests.
//   MissingLakeCanBeSeededFromAnotherRegisteredWorktree
// 要搬它,须先消掉它的 unknown 分类(补 ScribePathProvenance 或改测试的取路径方式),
// 那是另一层,不夹带在本层。
public sealed partial class LeanCacheEnsureCommandTests
{
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
}
