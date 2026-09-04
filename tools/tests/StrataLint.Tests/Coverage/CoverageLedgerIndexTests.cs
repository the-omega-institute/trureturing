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

}
