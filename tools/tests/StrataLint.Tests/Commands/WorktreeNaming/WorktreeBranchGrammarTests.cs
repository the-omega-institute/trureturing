using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class WorktreeBranchGrammarTests
{
    [Fact]
    public void ParseAcceptsEveryCreationKind()
    {
        foreach (var kind in WorktreeCommand.CreationKinds)
        {
            var branch = $"harness/{kind}/w99-foo";

            var parsed = WorktreeCommand.ParseArguments(
                "/repo",
                ["--branch", branch, "--path", "/tmp/probe"]);

            Assert.Equal(branch, parsed.Branch);
        }
    }

    [Theory]
    [InlineData("harness/w30-existing")]
    [InlineData("harness/math/w30-new")]
    [InlineData("harness/math/w30-new/extra")]
    public void OwnershipPredicateAcceptsEveryNonEmptyHarnessBranch(string branch)
    {
        Assert.True(WorktreeCommand.IsManagedBranch(branch));
    }

    [Theory]
    [InlineData("")]
    [InlineData("harness")]
    [InlineData("harness/")]
    [InlineData("agent/prover/D5-T0099")]
    [InlineData("feature/probe")]
    public void OwnershipPredicateRejectsBranchesOutsideHarnessNamespace(string branch)
    {
        Assert.False(WorktreeCommand.IsManagedBranch(branch));
    }

    [Theory]
    [InlineData("feature/probe")]
    [InlineData("harness")]
    [InlineData("harness/")]
    [InlineData("harness/probe")]
    [InlineData("harness/bogus/probe")]
    [InlineData("harness/math/task/extra")]
    [InlineData("agent/prover")]
    [InlineData("agent/prover/D5-T0099")]
    [InlineData("agent/prover/task/extra")]
    public void ParseRejectsBranchOutsideCreationGrammar(string branch)
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
            WorktreeCommand.ParseArguments(
                "/repo",
                new[] { "--branch", branch, "--path", "/tmp/probe" }));

        Assert.Contains(
            "harness/<kind>/<task-code>",
            exception.Message,
            StringComparison.Ordinal);
        Assert.All(
            WorktreeCommand.CreationKinds,
            kind => Assert.Contains(kind, exception.Message, StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("harness//task")]
    [InlineData("harness/unknown/task")]
    public void CommandRejectsMissingOrUnknownKindBeforeRunnerOrState(string branch)
    {
        using var fixture = new TemporaryDirectory();
        var target = Path.Combine(fixture.Path, "target");
        var runner = new RecordingWorktreeProcessRunner();

        var result = WorktreeCommand.Run(
            fixture.Path,
            [
                "--branch", branch,
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
            kind => Assert.Contains(kind, result.Error, StringComparison.Ordinal));
        Assert.Empty(runner.Invocations);
        Assert.False(File.Exists(target));
        Assert.False(Directory.Exists(target));
        Assert.Empty(Directory.EnumerateFileSystemEntries(fixture.Path));
    }

    [Fact]
    public void UsageListsKindsFromTheCreationGrammarOwner()
    {
        Assert.All(
            WorktreeCommand.CreationKinds,
            kind => Assert.Contains(kind, WorktreeCommand.Usage, StringComparison.Ordinal));
    }
}
