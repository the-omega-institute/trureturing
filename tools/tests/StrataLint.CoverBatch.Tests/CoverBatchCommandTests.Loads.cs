using StrataLint.Cli;
using StrataLint.Engine;
using Xunit.Abstractions;

namespace StrataLint.CoverBatch.Tests;

public sealed partial class CoverBatchCommandTests
{
    private readonly ITestOutputHelper output;

    public CoverBatchCommandTests(ITestOutputHelper output) => this.output = output;

    [Fact]
    public void BatchParsesEachLedgerSnapshotOnceIncludingDurabilityRanking()
    {
        using var world = new BatchWorld();
        using var loads = new LedgerLoadCounter();

        var result = world.Run(Row(First, Gid) + Row(Second, Gid)
            + Row(First, OtherGid) + Row(First, Gid));

        Assert.True(result.Success, result.Error + result.Output);
        WriteLoadCounts("duplicate-multi-gid-batch", loads);
        Assert.Equal([1, 1], loads.CandidateSnapshotLoads);
    }

    [Fact]
    public void FailureDispositionParsesEachLedgerSnapshotOnceIncludingDurabilityRanking()
    {
        using var world = new BatchWorld(entry => entry.AtomId == First
            ? entry with { Receipts = entry.Receipts with { UnresolvedSubitems = ["remaining clause"] } }
            : entry);
        LedgerLoadCounter loads;
        CommandResult result;
        using (loads = new LedgerLoadCounter())
            result = world.Run(Row(First, Gid) + Row(Second, Gid));

        Assert.Equal(["failed", "applied"], Results(result).Select(item => item.Status).ToArray());
        Assert.NotNull(world.Entry(First).Receipts.CoverDisposition);
        Assert.Empty(world.Entry(First).Coverage);
        Assert.Single(world.Entry(Second).Coverage);
        WriteLoadCounts("disposition-then-independent-batch", loads);
        // Initial, committed disposition.
        Assert.Equal([1, 1], loads.CandidateSnapshotLoads);
    }

    private void WriteLoadCounts(string scenario, LedgerLoadCounter loads) =>
        output.WriteLine("LEDGER_LOADS scenario={0} loads={1} per_snapshot=[{2}]",
            scenario, loads.CandidateSnapshotLoads.Sum(),
            string.Join(',', loads.CandidateSnapshotLoads));

    private sealed class LedgerLoadCounter : IDisposable
    {
        private readonly Action<RepositorySnapshot>? previous = BackfillInventoryLoader.DocumentLoading.Value;
        private readonly List<string> candidateImages = [];
        internal int[] CandidateSnapshotLoads => candidateImages.GroupBy(image => image, StringComparer.Ordinal)
            .Select(group => group.Count()).ToArray();

        internal LedgerLoadCounter() => BackfillInventoryLoader.DocumentLoading.Value = snapshot =>
            candidateImages.Add(string.Concat(snapshot.Files
                .Where(pair => BackfillInventoryLoader.IsCanonicalPath(pair.Key.Value))
                .OrderBy(pair => pair.Key.Value, StringComparer.Ordinal)
                .Select(pair => pair.Key.Value + "\0" + Convert.ToBase64String(pair.Value.RawBytes.AsSpan()) + "\n")));

        public void Dispose() => BackfillInventoryLoader.DocumentLoading.Value = previous;
    }
}
