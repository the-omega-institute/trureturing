using System.Text.Json;
using StrataLint.Runtime;
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
        _ = ProjectOleanFixture.Write(repository.Path, "ExistingProject");
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
        using var repository = new TemporaryDirectory();
        var missingArguments = WorktreeCommand.Run(repository.Path, [], new RecordingWorktreeProcessRunner());
        Assert.False(missingArguments.Success);
        Assert.Contains("[--restore-dependencies]", missingArguments.Error, StringComparison.Ordinal);
        Assert.Contains("ensure-cache [--path DIR] [--restore-dependencies]", WorktreeCommand.Usage, StringComparison.Ordinal);
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
                || (call.FileName == "cp" && call.Arguments.FirstOrDefault() == "-pR"));
    }

    [Fact]
    public void LargeCheckoutCompletesWithoutEnteringInitializationRecovery()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        StampCache(repository.Path);
        var target = Path.Combine(repository.Path, "large-checkout");
        var recorder = new RecordingWorktreeProcessRunner();
        var runner = new SlowCheckoutProcessRunner(recorder);

        var result = WorktreeCommand.Run(repository.Path,
            ["--kind", "governance", "--name", "large-checkout", "--path", target,
             "--base", "HEAD", "--source", repository.Path, "--skip-restore"], runner);

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain(recorder.Invocations,
            call => call.Arguments.Contains("recover-init"));
        Assert.True(File.Exists(Path.Combine(target, "lean-toolchain")));
    }

    private sealed class SlowCheckoutProcessRunner(IWorktreeProcessRunner inner) : IWorktreeProcessRunner
    {
        public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments,
            string workingDirectory, TimeSpan timeout)
        {
            // Model a checkout that needs more than the ordinary five-minute Git budget.
            if (fileName == "git" && arguments.Take(2).SequenceEqual(["reset", "--hard"])
                && timeout < TimeSpan.FromSeconds(600))
                throw new TimeoutException("simulated large checkout exceeds the supplied timeout");
            return inner.Run(fileName, arguments, workingDirectory, timeout);
        }
    }

    [Fact]
    public void CommandAppendsOnlyMissingReviewScaffoldIgnores()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        File.WriteAllText(
            Path.Combine(repository.Path, ".gitignore"),
            "existing-output/\r\n.echo-review.md");
        TestGit.Run(repository.Path, "add", ".gitignore");
        TestGit.Run(repository.Path, "commit", "-m", "fixture ignore policy");
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
        TestGit.Run(repository.Path, "add", ".gitignore");
        TestGit.Run(repository.Path, "commit", "-m", "fixture complete ignore policy");
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
        Assert.Equal(string.Empty, TestGit.Run(target, "status", "--porcelain"));
    }

    [Fact]
    public void IgnoreWriteFailurePreservesWorktreeAndBranch()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var ignoreDirectory = Path.Combine(repository.Path, ".gitignore");
        Directory.CreateDirectory(ignoreDirectory);
        File.WriteAllText(Path.Combine(ignoreDirectory, "marker"), "fixture\n");
        TestGit.Run(repository.Path, "add", ".gitignore/marker");
        TestGit.Run(repository.Path, "commit", "-m", "fixture invalid ignore path");
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
        Assert.True(Directory.Exists(target));
        var branchLookup = TestProcessRunner.Run(
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{branch}"],
            repository.Path,
            BoundedProcessRunner.HangDetectionBudget,
            4096);
        Assert.Equal(0, branchLookup.ExitCode);
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

        Assert.Equal(73, exitCode);
        Assert.Contains("repository_identity", console.Error, StringComparison.Ordinal);
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
        TestGit.Run(repository.Path, "branch", branch, "HEAD");
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

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EmbeddedQualificationPersistsBoundedNativeDiagnostics(bool failInventory)
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        using var storage = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var tree = Path.Combine(storage.Path, "locked-tree");
        TestGit.Run(repository.Path, "worktree", "add", "-b", "locked-lane", tree);
        TestGit.Run(repository.Path, "worktree", "lock", "--reason", "intentional", tree);
        var names = new[] { "TRURETURING_MAINTENANCE_LOG_DIR", "TRURETURING_MAINTENANCE_RUN_ID", "PATH" };
        var previous = names.ToDictionary(name => name, Environment.GetEnvironmentVariable);
        try
        {
            var logs = Path.Combine(storage.Path, "logs");
            Environment.SetEnvironmentVariable(names[0], logs);
            Environment.SetEnvironmentVariable(names[1], null);
            if (failInventory)
            {
                var binary = Path.Combine(storage.Path, "bin");
                Directory.CreateDirectory(binary);
                var git = Path.Combine(binary, "git");
                File.WriteAllText(git, "#!/bin/sh\necho 'private Git diagnostic' >&2\nexit 1\n");
                File.SetUnixFileMode(git, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
                Environment.SetEnvironmentVariable("PATH", binary + Path.PathSeparator + previous["PATH"]);
            }
            var lines = new List<string>();
            var result = WorktreeProtocolCommand.RunLines(repository.Path,
                ["qualify", "--path", tree, "--stream"], new ProductionWorktreeProcessRunner(),
                TimeSpan.FromSeconds(30), lines.Add);
            Assert.Equal(failInventory ? 74 : 0, result.ExitCode);
            using var receipt = JsonDocument.Parse(lines[^1]);
            Assert.Equal("worktree_qualification", receipt.RootElement.GetProperty("event").GetString());
            Assert.Equal(failInventory ? "failed" : "succeeded", receipt.RootElement.GetProperty("status").GetString());
            Assert.Equal(1, receipt.RootElement.GetProperty("item_count").GetInt32());
            using var item = JsonDocument.Parse(lines.Single(line => line.Contains("worktree_qualification_item", StringComparison.Ordinal)));
            Assert.Equal(failInventory ? "failed" : "refused", item.RootElement.GetProperty("outcome").GetString());
            Assert.Contains(failInventory ? "private Git diagnostic" : "locked_recent",
                item.RootElement.GetProperty("reason").GetString(), StringComparison.Ordinal);
            var text = File.ReadAllText(Path.Combine(logs, "worktree-protocol.jsonl"));
            var rows = text.Split('\n', StringSplitOptions.RemoveEmptyEntries)
                .Select(line => JsonSerializer.Deserialize<JsonElement>(line)).ToArray();
            var observed = rows.Single(row => row.GetProperty("event").GetString() == "qualification_item");
            Assert.Equal("qualify", observed.GetProperty("action").GetString());
            Assert.Equal(failInventory ? "qualification_failed" : "locked_recent", observed.GetProperty("reason_code").GetString());
            Assert.Equal(failInventory ? "GitFailure" : "Refused", observed.GetProperty("error_type").GetString());
            if (failInventory) Assert.Equal("unavailable", observed.GetProperty("failure_kind").GetString());
            var summary = rows.Single(row => row.GetProperty("event").GetString() == "operation_finished");
            Assert.Equal(1, summary.GetProperty("item_count").GetInt32());
            Assert.Equal(failInventory ? 1 : 0, summary.GetProperty("failed_count").GetInt32());
            Assert.Equal(failInventory ? 0 : 1, summary.GetProperty("refused_count").GetInt32());
            Assert.Equal(0, summary.GetProperty("qualified_count").GetInt32());
            Assert.Equal(0, summary.GetProperty("deferred_count").GetInt32());
            Assert.Equal(failInventory ? 74 : 0, rows[^1].GetProperty("exit_code").GetInt32());
            Assert.DoesNotContain("private Git diagnostic", text, StringComparison.Ordinal);
            Assert.True(Directory.Exists(tree));
            Assert.Empty(result.Error);
        }
        finally
        {
            foreach (var name in names) Environment.SetEnvironmentVariable(name, previous[name]);
        }
    }

    [Fact]
    public void NativeReturnRetainsEffectAndObservesFailedAutomaticPool()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B",
            Path.Combine(root, "tools/tests/StrataLint.WorkflowScript.Tests/Fixtures/maintenance_log_tests.py"),
            root, "MaintenanceLogTests.test_native_return_pool_failure"], root, TimeSpan.FromSeconds(90), 1024 * 1024);
        Assert.True(result.ExitCode == 0, System.Text.Encoding.UTF8.GetString(result.StandardOutput)
            + System.Text.Encoding.UTF8.GetString(result.StandardError));
    }

    private static void InitializeRepository(string root)
    {
        TestGit.Run(root, "init", "--initial-branch=dev");
        TestGit.Run(root, "config", "user.email", "stratalint@example.invalid");
        TestGit.Run(root, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(Path.Combine(root, "README.md"), "# worktree fixture\n");
        File.WriteAllText(Path.Combine(root, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(root, "lake-manifest.json"), LeanCacheFixtureFile.Manifest());
        StrataLint.TestSupport.RegPackageFixture.Write(root);
        TestGit.Run(root, "add", "README.md", "lean-toolchain", "lake-manifest.json", "Reg", "tools/lean-inspector-reg");
        TestGit.Run(root, "commit", "-m", "fixture baseline");
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
