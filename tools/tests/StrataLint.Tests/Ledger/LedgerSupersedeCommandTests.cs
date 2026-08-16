using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LedgerSupersedeCommandTests
{
    [Fact]
    public void RootUsageListsLedgerSupersedeCommand()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [],
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("ledger-supersede", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void LedgerSupersedeVerbDispatchesToTheEnvironment()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["ledger-supersede", "--candidate-lean-report", "report.json"],
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("ledger supersede is not configured", console.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("UNKNOWN_COMMAND", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ProductionCommandAppendsSupersedeForPinBumpAndThenIsIdempotent()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(pinBump: true);
        var baselineLines = FrozenLedgerTestData.Lines(fixture.BaselineBytes);
        var arguments = new[] { "--candidate-lean-report", fixture.ReportPath };

        var first = fixture.Environment.SupersedeLedger(arguments);

        Assert.True(first.Success, first.Error);
        Assert.Contains("appended_supersedes=1", first.Output, StringComparison.Ordinal);
        var files = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        var view = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            files.ToImmutableDictionary(static file => file.Path)));
        Assert.Equal(baselineLines.Length + 1, view.EventCount);
        var active = Assert.Single(view.ActiveByCase.Values);
        Assert.NotNull(active.Environment);
        Assert.Equal(
            FrozenLedgerTestData.GitBlobOid("leanprover/lean4:v4.25.0\n"),
            active.Environment.LeanToolchainBlobOid);
        var references = Assert.Single(fixture.Gateway.FrozenReferenceValidations);
        Assert.Single(references.Inputs);
        Assert.Single(references.EnvironmentReferences);
        Assert.Single(references.CommitOids);
        Assert.Single(references.TreeOids);
        Assert.Equal(4, references.BlobOids.Length);

        var afterFirst = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);
        var second = fixture.Environment.SupersedeLedger(arguments);

        Assert.True(second.Success, second.Error);
        Assert.Contains("no changed environment pins", second.Output, StringComparison.Ordinal);
        Assert.Equal(afterFirst, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
        Assert.Single(fixture.Gateway.FrozenReferenceValidations);
    }
}
