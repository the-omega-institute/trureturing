using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestAndAlignCommandsPreserveNonpropositionalReceipt()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var document = BackfillInventoryLoader.Load(Decode(Snapshot(fixture.Files)));
        var source = Assert.Single(document.RequireDigestionSources());
        var target = Assert.Single(source.Entries);
        var settled = target with
        {
            Receipts = target.Receipts with
            {
                Nonpropositional = new("The source contains commentary with no proposition.", null, null),
            },
            ProjectedStatus = new(DigestionMigrationState.Nonpropositional, DigestionTruthState.Inapplicable),
        };
        var updated = document.WithDigestionSources([source with { Entries = [settled] }]);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, updated);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, updated);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var raw = Snapshot(fixture.Files);
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw);
        var aligned = IngestCommand.Run(temporary.Path, repository,
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty), ["--base", "baseline"]);
        Assert.True(aligned.Success, aligned.Error);
        var reportSource = new FakeLeanReportSource(null);
        var ingested = new ProductionCliEnvironment(temporary.Path, repository, reportSource,
            new FakeScribeEmissionVerifier(null)).Ingest(ReportInputUnchangedArguments);
        Assert.True(ingested.Success, ingested.Error);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(BackfillInventoryWriter.WriteAtom(settled).ToArray(),
            BackfillInventoryWriter.WriteAtom(Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path)
                .RequireDigestionEntries())).ToArray());
    }
}
