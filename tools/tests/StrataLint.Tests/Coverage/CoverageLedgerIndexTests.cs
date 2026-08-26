using System.Text;
using StrataLint.Cli;
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
    public void RevocationRemovesPreviouslyFrozenPathFromCoverageIndex()
    {
        const string node = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        var bytes = Encoding.UTF8.GetBytes(
            "{\"event_type\":\"Genesis\",\"payload\":{}}\n"
            + "{\"event_type\":\"Freeze\",\"payload\":{\"frozen_node_id\":\"" + node
            + "\",\"input\":{\"descriptor_selector\":\"D5/S0/Carrier/Ring.lean\"}}}\n"
            + "{\"event_type\":\"Revoke\",\"payload\":{\"affected_frozen_node_ids\":[\"" + node + "\"]}}\n");
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

        var loaded = Assert.IsType<FrozenCoverageLoadOutcome.Loaded>(
            FrozenCoverageLedger.Load(syntax));

        Assert.Empty(loaded.ActiveFrozenPaths);
    }

    [Fact]
    public void TwoActiveFrozenNodesCannotCollapseOntoOnePath()
    {
        const string first = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        const string second = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        const string path = "D5/S0/Carrier/Ring.lean";
        var bytes = Encoding.UTF8.GetBytes(
            "{\"event_type\":\"Genesis\",\"payload\":{}}\n"
            + Freeze(first, path)
            + Freeze(second, path));
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

        var invalid = Assert.IsType<FrozenCoverageLoadOutcome.Invalid>(
            FrozenCoverageLedger.Load(syntax));

        Assert.Contains("duplicate path", invalid.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnknownLedgerEventFailsClosed()
    {
        var bytes = Encoding.UTF8.GetBytes("{\"event_type\":\"Mystery\",\"payload\":{}}\n");
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

        var invalid = Assert.IsType<FrozenCoverageLoadOutcome.Invalid>(
            FrozenCoverageLedger.Load(syntax));

        Assert.Contains("unknown event", invalid.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RetiredSupersedeEventFailsClosed()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "{\"event_type\":\"Genesis\",\"payload\":{}}\n"
            + "{\"event_type\":\"Supersede\",\"payload\":{}}\n");
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

        var invalid = Assert.IsType<FrozenCoverageLoadOutcome.Invalid>(
            FrozenCoverageLedger.Load(syntax));

        Assert.Contains("unknown event type Supersede", invalid.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void StateChangingEventCannotPrecedeGenesis()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "{\"event_type\":\"Freeze\",\"payload\":{}}\n"
            + "{\"event_type\":\"Genesis\",\"payload\":{}}\n");
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

        var invalid = Assert.IsType<FrozenCoverageLoadOutcome.Invalid>(
            FrozenCoverageLedger.Load(syntax));

        Assert.Contains("before Genesis", invalid.Message, StringComparison.Ordinal);
    }

    private static string Freeze(string node, string path) =>
        "{\"event_type\":\"Freeze\",\"payload\":{\"frozen_node_id\":\"" + node
        + "\",\"input\":{\"descriptor_selector\":\"" + path + "\"}}}\n";

    [Fact]
    public void SchemaV4FreezeWithoutNodePathAliasIsIndexedByItsDescriptorSelector()
    {
        const string node = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        var bytes = Encoding.UTF8.GetBytes(
            "{\"event_type\":\"Genesis\",\"payload\":{}}\n"
            + "{\"event_type\":\"Freeze\",\"payload\":{\"frozen_node_id\":\"" + node
            + "\",\"input\":{\"descriptor_selector\":\"D5/S0/Carrier/Ring.lean\"}}}\n");
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

        var loaded = Assert.IsType<FrozenCoverageLoadOutcome.Loaded>(
            FrozenCoverageLedger.Load(syntax));

        Assert.True(RepoPath.TryCreate("D5/S0/Carrier/Ring.lean", out var expected));
        Assert.Contains(expected, loaded.ActiveFrozenPaths);
    }
}
