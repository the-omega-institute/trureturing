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
        var dag = Assert.IsType<DagBuildOutcome.Accepted>(
            AcyclicTruthDag.Build(snapshot, lean)).Capability;
        Assert.True(RepoPath.TryCreate("D5/S0/Carrier/Missing.lean", out var missing));

        var exception = Assert.Throws<InvalidOperationException>(() =>
            CoverageLedgerIndex.FromDag(dag, [missing]));

        Assert.Contains("absent from TruthDAG", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RevocationRemovesPreviouslyFrozenPathFromCoverageIndex()
    {
        const string node = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        var bytes = Encoding.UTF8.GetBytes(
            "{\"event_type\":\"Genesis\",\"payload\":{}}\n"
            + "{\"event_type\":\"Freeze\",\"payload\":{\"frozen_node_id\":\"" + node
            + "\",\"node_path\":\"D5/S0/Carrier/Ring.lean\"}}\n"
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
    public void SupersedeReplacesTheActiveNodeIdentityWithoutChangingCoveragePath()
    {
        const string oldNode = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        const string newNode = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        const string path = "D5/S0/Carrier/Ring.lean";
        var bytes = Encoding.UTF8.GetBytes(
            "{\"event_type\":\"Genesis\",\"payload\":{}}\n"
            + Freeze(oldNode, path)
            + "{\"event_type\":\"Supersede\",\"payload\":{"
            + "\"case_id\":\"active-frozen/test\","
            + "\"frozen_node_id\":\"" + newNode + "\","
            + "\"input\":{\"descriptor_selector\":\"" + path + "\"}}}\n"
            + "{\"event_type\":\"Revoke\",\"payload\":{\"affected_frozen_node_ids\":[\""
            + newNode + "\"]}}\n");
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

        var loaded = Assert.IsType<FrozenCoverageLoadOutcome.Loaded>(
            FrozenCoverageLedger.Load(syntax));

        Assert.Empty(loaded.ActiveFrozenPaths);
    }

    [Fact]
    public void StateChangingEventCannotPrecedeGenesis()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "{\"event_type\":\"Reattest\",\"payload\":{}}\n"
            + "{\"event_type\":\"Genesis\",\"payload\":{}}\n");
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

        var invalid = Assert.IsType<FrozenCoverageLoadOutcome.Invalid>(
            FrozenCoverageLedger.Load(syntax));

        Assert.Contains("before Genesis", invalid.Message, StringComparison.Ordinal);
    }

    private static string Freeze(string node, string path) =>
        "{\"event_type\":\"Freeze\",\"payload\":{\"frozen_node_id\":\"" + node
        + "\",\"node_path\":\"" + path + "\"}}\n";
}
