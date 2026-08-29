using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestDeltaIgnoresHistoricalOrphanCasBlob()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var historicalOrphan = DigestionCasStore.Capture(
            Encoding.UTF8.GetBytes("historical orphan outside ingest delta\n"));
        AddCas(fixture.Files, historicalOrphan);
        AddCas(fixture.Baseline, historicalOrphan);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var reportSource = new FakeLeanReportSource(report: null);
        var scribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            scribeVerifier);

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
    }

    [Fact]
    public void IngestDeltaRejectsNewUnreferencedCasWithoutRecheckingHistoricalOrphan()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var historicalOrphan = DigestionCasStore.Capture(
            Encoding.UTF8.GetBytes("historical orphan outside new CAS delta\n"));
        var newOrphan = DigestionCasStore.Capture(
            Encoding.UTF8.GetBytes("new unreferenced CAS in candidate delta\n"));
        AddCas(fixture.Files, historicalOrphan);
        AddCas(fixture.Baseline, historicalOrphan);
        AddCas(fixture.Files, newOrphan);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = GeneratedIngestImage(temporary);
        var reportSource = new FakeLeanReportSource(report: null);
        var scribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds([(newOrphan.RelativePath, RawChangeKind.Added)]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            scribeVerifier);

        var result = environment.Ingest(ReportInputUnchangedArguments);

        Assert.False(result.Success);
        Assert.Contains($"orphan CAS blob: {newOrphan.RelativePath}", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain(historicalOrphan.RelativePath, result.Error, StringComparison.Ordinal);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    [Fact]
    public void IngestDeltaRejectsCasOrphanedByDeletedLastReferenceWithoutRecheckingHistoricalOrphan()
    {
        var fixture = UncoveredOnlyIngestFixture(addNewAtom: false);
        var atomPath = DirectoryAtomPath("old-receipt", "residual-open");
        var newlyOrphanedCasPath = Assert.Single(
            fixture.Files.Keys,
            DigestionCasStore.IsCanonicalPath);
        var historicalOrphan = DigestionCasStore.Capture(
            Encoding.UTF8.GetBytes("historical orphan outside deleted-reference delta\n"));
        AddCas(fixture.Files, historicalOrphan);
        AddCas(fixture.Baseline, historicalOrphan);
        Assert.True(fixture.Files.Remove(atomPath));
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = GeneratedIngestImage(temporary);
        var reportSource = new FakeLeanReportSource(report: null);
        var scribeVerifier = new FakeScribeEmissionVerifier(verification: null);
        var result = IngestCommand.Run(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.CreateWithKinds([(atomPath, RawChangeKind.Deleted)]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            reportSource,
            scribeVerifier,
            ["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains($"orphan CAS blob: {newlyOrphanedCasPath}", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain(historicalOrphan.RelativePath, result.Error, StringComparison.Ordinal);
        Assert.Equal(0, reportSource.CallCount);
        Assert.Equal(0, scribeVerifier.CallCount);
        Assert.Equal(before, GeneratedIngestImage(temporary));
    }

    private static void AddCas(IDictionary<string, string> files, DigestionCasObject casObject) =>
        files[casObject.RelativePath] = Encoding.UTF8.GetString(casObject.Bytes.AsSpan());
}
