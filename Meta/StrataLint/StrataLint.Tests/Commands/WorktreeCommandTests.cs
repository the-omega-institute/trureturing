using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

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
        Assert.Contains("check|ledger-genesis|route|selftest|topology|worktree", console.Error);
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
        Assert.False(parsed.Warm);
    }

    [Fact]
    public void ParseAcceptsEveryFlagInAnyOrder()
    {
        var parsed = WorktreeCommand.ParseArguments(
            "/repo",
            new[]
            {
                "--warm",
                "--source", "/source",
                "--base", "HEAD",
                "--path", "/tmp/probe",
                "--branch", "agent/prover/D5-T0099",
            });

        Assert.Equal("agent/prover/D5-T0099", parsed.Branch);
        Assert.Equal("HEAD", parsed.Base);
        Assert.Equal(Path.GetFullPath("/source"), parsed.Source);
        Assert.True(parsed.Warm);
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
    public void CommandCreatesRealWorktreeAndClonesLakeCache()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var cacheFile = Path.Combine(repository.Path, ".lake", "build", "cache.bin");
        Directory.CreateDirectory(Path.GetDirectoryName(cacheFile)!);
        File.WriteAllText(cacheFile, "warm cache\n");
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
            },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(0, exitCode);
        Assert.Equal("harness/integration-probe", ReviewRegressionTests.RunGit(target, "branch", "--show-current").Trim());
        Assert.Equal("warm cache\n", File.ReadAllText(Path.Combine(target, ".lake", "build", "cache.bin")));
        Assert.Contains($"WORKTREE path={Path.GetFullPath(target)} branch=harness/integration-probe clone=", console.Output);
        Assert.Contains(" warm=false elapsed_ms=", console.Output);
        Assert.Equal(string.Empty, console.Error);
    }

    [Fact]
    public void CommandSkipsMissingLakeCacheWithActionableNotice()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "without-cache");
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[]
            {
                "worktree",
                "--branch", "harness/without-cache",
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
            },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(0, exitCode);
        Assert.Contains(" clone=skipped ", console.Output, StringComparison.Ordinal);
        Assert.Contains("lake exe cache get", console.Error, StringComparison.Ordinal);
        Assert.True(Directory.Exists(target));
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
    public void WarmFailureRemovesWorktreeAndCreatedBranch()
    {
        using var repository = new TemporaryDirectory();
        InitializeRepository(repository.Path);
        var target = Path.Combine(repository.Path, "failed-warm");
        var branch = "harness/failed-warm";
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            new[]
            {
                "worktree",
                "--branch", branch,
                "--path", target,
                "--base", "HEAD",
                "--source", repository.Path,
                "--warm",
            },
            new ProductionCliEnvironment(repository.Path),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("WORKTREE_FAILED", console.Error, StringComparison.Ordinal);
        Assert.False(Directory.Exists(target));
        var branchLookup = BoundedProcessRunner.Run(
            "git",
            new[] { "show-ref", "--verify", "--quiet", $"refs/heads/{branch}" },
            repository.Path,
            TimeSpan.FromSeconds(30),
            4096);
        Assert.Equal(1, branchLookup.ExitCode);
    }

    private static void InitializeRepository(string root)
    {
        ReviewRegressionTests.RunGit(root, "init", "--initial-branch=dev");
        ReviewRegressionTests.RunGit(root, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(root, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(Path.Combine(root, "README.md"), "# worktree fixture\n");
        ReviewRegressionTests.RunGit(root, "add", "README.md");
        ReviewRegressionTests.RunGit(root, "commit", "-m", "fixture baseline");
    }
}
