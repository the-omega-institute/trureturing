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
        var supersede = Assert.Single(view.Events, static item => item.EventType == "Supersede");
        Assert.False(
            supersede.Payload.GetProperty("input").TryGetProperty("supporting_blob_oids", out _),
            "Supersede input duplicated its named environment pins");

        var afterFirst = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);
        var second = fixture.Environment.SupersedeLedger(arguments);

        Assert.True(second.Success, second.Error);
        Assert.Contains("no changed environment pins", second.Output, StringComparison.Ordinal);
        Assert.Equal(afterFirst, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
        Assert.Single(fixture.Gateway.FrozenReferenceValidations);
    }

    [Fact]
    public void ProductionSupersedeWriterEmitsCurrentSchemaV4()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(pinBump: true);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.True(result.Success, result.Error);
        var files = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(fixture.LedgerPath);
        var view = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            files.ToImmutableDictionary(static file => file.Path)));
        var supersede = Assert.Single(view.Events, static item => item.EventType == "Supersede");
        Assert.Equal(FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion, supersede.SchemaVersion);
        Assert.Equal(4, supersede.SchemaVersion);
    }

    [Fact]
    public void SupersedeRejectsWeakerMeaningFromChangedImportedModule()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "ambiently-weakened-imported-expression",
            pinBump: true,
            aImportsB: true,
            reportBDriftInChangeSet: true);
        var before = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success, result.Output);
        Assert.Contains("import closure", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(before, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }

    [Fact]
    public void SupersedeAcceptsPinBumpStatementDriftWhenRepositoryImportClosureIsByteUnchanged()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "ambiently-different-elaborated-expression",
            pinBump: true,
            aImportsB: true);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_supersedes=2", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SupersedeAcceptsPinnedExternalImportElaborationDrift()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "ambiently-different-elaborated-expression",
            pinBump: true,
            aImportsExternal: true,
            externalPackagePinned: true);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("appended_supersedes=1", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SupersedeRejectsWeakerMeaningFromAnUntrackedExternalImport()
    {
        using var fixture = new LedgerAppendCommandTests.LedgerAppendFixture(
            currentAStatementMaterial: "True",
            pinBump: true,
            aImportsExternal: true);
        var before = FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath);

        var result = fixture.Environment.SupersedeLedger(
            ["--candidate-lean-report", fixture.ReportPath]);

        Assert.False(result.Success, result.Output);
        Assert.Contains("external import", result.Error, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(before, FrozenLedgerTestData.ReadLedgerDirectory(fixture.LedgerPath));
    }
}
