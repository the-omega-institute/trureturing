using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.AtomContextFixture;

namespace StrataLint.Tests;

public sealed class SearchAtomsAllowProbe
{
    [Fact]
    public void InstalledSearchFindsStoredChildWithoutParsingMetadataOrReadingUnrelatedRecords()
    {
        var fixture = Create();
        var bytes = Encoding.UTF8.GetBytes("Persisted explicit nested child integration needle.");
        var id = DigestionFingerprint.Compute(bytes).RawSha256[7..];
        var rogue = new string('f', 64);
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Select(entry =>
            entry.Path.EndsWith(".yaml", StringComparison.Ordinal) || entry.Path.EndsWith("source.toml", StringComparison.Ordinal) || entry.Path == TheoryAtomizerDataLoader.DataPath
                ? RawRepositoryEntry.FromText(entry.Path, "invalid: [") : entry).Concat([
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/source/residual-open/{id}.yaml", "invalid: ["),
            new RawRepositoryEntry(DigestionCasStore.RootPath + id, [.. bytes]),
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/source/extra/residual-open/{rogue}.yaml", "invalid: ["),
            RawRepositoryEntry.FromText(DigestionCasStore.RootPath + rogue, "integration needle"),
            RawRepositoryEntry.FromText("Meta/Digestion/backfill/unrelated/source.toml", "invalid = ["),
        ]));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var report = new FakeLeanReportSource(null);
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["search-atoms", "--source", "source", "--text", "integration needle"],
            new ProductionCliEnvironment("/repo", gateway, report), console);
        Assert.True(exit == 0, console.Error);
        Assert.Contains($"atom_id={id}", console.Output, StringComparison.Ordinal);
        Assert.Contains($"path=Meta/Digestion/backfill/source/residual-open/{id}.yaml", console.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(rogue, console.Output, StringComparison.Ordinal);
        Assert.Equal(0, report.CallCount);
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.All(gateway.ScopedCurrentReads.SelectMany(static scope => scope), path =>
            Assert.StartsWith(DigestionQuerySelection.Literal(DigestionCasStore.RootPath), path));
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(static scope => scope), path =>
            path.Contains("unrelated", StringComparison.Ordinal) || path.Contains("source.toml", StringComparison.Ordinal)
            || path.Contains(".yaml", StringComparison.Ordinal) || path.Contains(TheoryAtomizerDataLoader.DataPath, StringComparison.Ordinal));
    }
}
