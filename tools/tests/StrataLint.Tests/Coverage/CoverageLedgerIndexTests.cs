using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CoverageLedgerIndexTests
{
    [Fact]
    public void FrozenPathAbsentFromTruthDagFailsClosed()
    {
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create([]))).Snapshot;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(
                snapshot,
                LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()))).Capability;
        var states = LeanTruthStates.Resolve(snapshot, lean);
        Assert.True(RepoPath.TryCreate("D5/S0/Carrier/Missing.lean", out var missing));

        var exception = Assert.Throws<InvalidOperationException>(() =>
            CoverageLedgerIndex.FromStates(states, [missing], snapshot));

        Assert.Contains("absent from TruthDAG", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void V5FreezeSetIndexesDescriptorSelectors()
    {
        var catalog = FrozenLedgerTestData.BuildCatalog(
            FrozenLedgerTestData.Module("A"),
            FrozenLedgerTestData.Module("B"));
        var events = FrozenLedgerTestData.LoadEvents(FrozenLedgerTestData.EventFiles(catalog));

        var loaded = Assert.IsType<FrozenCoverageLoadOutcome.Loaded>(
            FrozenCoverageLedger.Load(events));

        Assert.Equal(
            catalog.ClosedNodes.Select(static node => node.RepoPath).OrderBy(static path => path.Value),
            loaded.ActiveFrozenPaths);
    }
}
