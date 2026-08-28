using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class WorktreeBranchGrammarTests
{
    private static string ExpectedCreationNamespace => WorktreeCommand.CreationNamespace;
    private static string HistoricalLifecycleNamespace =>
        WorktreeCommand.HistoricalLifecycleNamespace;

    [Fact]
    public void ParseAcceptsEveryCreationKind()
    {
        foreach (var kind in WorktreeCommand.CreationKinds)
        {
            var parsed = WorktreeCommand.ParseArguments(
                "/repo",
                ["--kind", kind, "--name", "w99-foo", "--path", "/tmp/probe"]);

            Assert.Equal($"{ExpectedCreationNamespace}/{kind}/w99-foo", parsed.Branch);
        }
    }

    [Theory]
    [InlineData("w30-existing")]
    [InlineData("math/w30-new")]
    [InlineData("math/w30-new/extra")]
    public void OwnershipPredicateAcceptsEveryNonEmptyCurrentBranch(string suffix)
    {
        Assert.True(WorktreeCommand.IsManagedBranch($"{ExpectedCreationNamespace}/{suffix}"));
    }

    [Theory]
    [InlineData("w30-existing")]
    [InlineData("math/w30-new")]
    [InlineData("math/w30-new/extra")]
    public void OwnershipPredicateAcceptsEveryNonEmptyHistoricalBranch(string suffix)
    {
        Assert.True(WorktreeCommand.IsManagedBranch($"{HistoricalLifecycleNamespace}/{suffix}"));
    }

    [Theory]
    [InlineData("")]
    [InlineData("harness")]
    [InlineData("harness/")]
    [InlineData("agent/prover/D5-T0099")]
    [InlineData("feature/probe")]
    public void OwnershipPredicateRejectsBranchesOutsideLifecycleNamespaces(string branch)
    {
        Assert.False(WorktreeCommand.IsManagedBranch(branch));
        Assert.False(WorktreeCommand.IsManagedBranch(ExpectedCreationNamespace));
        Assert.False(WorktreeCommand.IsManagedBranch(ExpectedCreationNamespace + "/"));
    }

    [Theory]
    [InlineData("", "task")]
    [InlineData("bogus", "task")]
    [InlineData("math", "")]
    [InlineData("math", "task/extra")]
    public void ParseRejectsValuesOutsideCreationGrammar(string kind, string name)
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
            WorktreeCommand.ParseArguments(
                "/repo",
                ["--kind", kind, "--name", name, "--path", "/tmp/probe"]));

        Assert.Contains(
            $"{ExpectedCreationNamespace}/<kind>/<task-code>",
            exception.Message,
            StringComparison.Ordinal);
        Assert.All(
            WorktreeCommand.CreationKinds,
            candidate => Assert.Contains(candidate, exception.Message, StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("")]
    [InlineData("unknown")]
    public void CommandRejectsMissingOrUnknownKindBeforeRunnerOrState(string kind)
    {
        using var fixture = new TemporaryDirectory();
        var target = Path.Combine(fixture.Path, "target");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            fixture.Path,
            [
                "--kind", kind,
                "--name", "task",
                "--path", target,
                "--base", "HEAD",
                "--source", fixture.Path,
                "--skip-restore",
            ],
            runner);

        Assert.False(result.Success);
        Assert.Contains("kind must be one of:", result.Error, StringComparison.Ordinal);
        Assert.All(
            WorktreeCommand.CreationKinds,
            candidate => Assert.Contains(candidate, result.Error, StringComparison.Ordinal));
        Assert.Empty(runner.Invocations);
        Assert.False(File.Exists(target));
        Assert.False(Directory.Exists(target));
        Assert.Empty(Directory.EnumerateFileSystemEntries(fixture.Path));
    }

    [Fact]
    public void ValidateBranchIsPureAndAcceptsCanonicalCreationName()
    {
        var runner = new RecordingWorktreeProcessRunner();
        var branch = $"{ExpectedCreationNamespace}/{WorktreeCommand.CreationKinds[0]}/w99-foo";

        var result = WorktreeCommand.Run(
            "/path/that/need/not/exist",
            ["validate-branch", "--branch", branch],
            runner);

        Assert.True(result.Success, result.Error);
        Assert.Empty(result.Error);
        Assert.Empty(runner.Invocations);
        using var receipt = JsonDocument.Parse(result.Output);
        Assert.Equal("branch_validation", receipt.RootElement.GetProperty("event").GetString());
        Assert.Equal(branch, receipt.RootElement.GetProperty("branch").GetString());
        Assert.True(receipt.RootElement.GetProperty("canonical").GetBoolean());
        Assert.True(receipt.RootElement.GetProperty("lifecycle_managed").GetBoolean());
        Assert.Equal("canonical", receipt.RootElement.GetProperty("status").GetString());
    }

    [Fact]
    public void ValidateBranchExplainsHistoricalLifecycleNamespaceIsNotCreationAlias()
    {
        var runner = new RecordingWorktreeProcessRunner();
        var branch = $"{HistoricalLifecycleNamespace}/{WorktreeCommand.CreationKinds[0]}/w99-foo";

        var result = WorktreeCommand.Run(
            "/path/that/need/not/exist",
            ["validate-branch", "--branch", branch],
            runner);

        Assert.False(result.Success);
        Assert.Empty(result.Error);
        Assert.Empty(runner.Invocations);
        using var receipt = JsonDocument.Parse(result.Output);
        Assert.False(receipt.RootElement.GetProperty("canonical").GetBoolean());
        Assert.True(receipt.RootElement.GetProperty("lifecycle_managed").GetBoolean());
        Assert.Equal(
            "BRANCH_GRAMMAR_NONCONFORMING",
            receipt.RootElement.GetProperty("status").GetString());
        Assert.Contains(
            "historical lifecycle namespace",
            receipt.RootElement.GetProperty("reason").GetString(),
            StringComparison.Ordinal);
        Assert.Contains(
            HistoricalLifecycleNamespace,
            receipt.RootElement.GetProperty("reason").GetString(),
            StringComparison.Ordinal);
        Assert.Contains(
            ExpectedCreationNamespace,
            receipt.RootElement.GetProperty("reason").GetString(),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ValidateBranchUsesStableCanonicalNonconformingAndUsageExitCodes()
    {
        using var fixture = new TemporaryDirectory();
        var environment = new ProductionCliEnvironment(fixture.Path);

        var canonicalConsole = new BufferedConsole();
        var canonical = CliApplication.Run(
            [
                "worktree", "validate-branch", "--branch",
                $"{ExpectedCreationNamespace}/{WorktreeCommand.CreationKinds[0]}/w99-foo",
            ],
            environment,
            canonicalConsole);

        var nonconformingConsole = new BufferedConsole();
        var nonconforming = CliApplication.Run(
            ["worktree", "validate-branch", "--branch", "feature/probe"],
            environment,
            nonconformingConsole);

        var usageConsole = new BufferedConsole();
        var usage = CliApplication.Run(
            ["worktree", "validate-branch", "--branch"],
            environment,
            usageConsole);

        Assert.Equal(0, canonical);
        Assert.Equal(1, nonconforming);
        Assert.Equal(64, usage);
        Assert.Contains("\"status\":\"canonical\"", canonicalConsole.Output, StringComparison.Ordinal);
        Assert.Contains(
            "\"status\":\"BRANCH_GRAMMAR_NONCONFORMING\"",
            nonconformingConsole.Output,
            StringComparison.Ordinal);
        Assert.Contains("USAGE:", usageConsole.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void UsageListsKindsFromTheCreationGrammarOwner()
    {
        Assert.All(
            WorktreeCommand.CreationKinds,
            kind => Assert.Contains(kind, WorktreeCommand.Usage, StringComparison.Ordinal));
    }
}
