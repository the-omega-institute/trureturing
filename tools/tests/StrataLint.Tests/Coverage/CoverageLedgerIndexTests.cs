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

    // Reattest 会改 frozen_node_id(witness 含 source blob,重新 attest 即变):实测 971 个
    // lineage 中 107 个记录过多于一个 frozen_node_id。该消费者原先对 Reattest 直接 break,
    // 于是后续 Revoke 指向 Reattest 之后的 active id 时,active 表里没有它 ⟹ 被拒。
    // v4 的 legacy 形 Reattest 两个 node-id 字段都没有:正名 frozen_node_id 从来只属 extended 形,
    // 别名 semantic_receipt 随 schema v4 退役。它只在 materialUnchanged 时产生,故此时 id 未变,
    // 正确行为是**保持当前 active 不动**,而不是拒。
    // 我先前据「id 恒等于前驱」判定「丢失无害」而结案——那只证明了信息不丢失,
    // 没检查消费者能不能拿到它:消费者不看前驱,只看当前事件。等值不蕴含可用。
    [Fact]
    public void SchemaV4LegacyReattestWithoutAnyNodeIdKeepsTheExistingIdentity()
    {
        const string frozen = "sha256:eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee";
        const string path = "D5/S0/Carrier/Ring.lean";
        var bytes = Encoding.UTF8.GetBytes(
            "{\"event_type\":\"Genesis\",\"payload\":{}}\n"
            + "{\"event_type\":\"Freeze\",\"payload\":{\"frozen_node_id\":\"" + frozen
            + "\",\"input\":{\"descriptor_selector\":\"" + path + "\"}}}\n"
            + "{\"event_type\":\"Reattest\",\"payload\":{\"case_id\":\"active-frozen/x\","
            + "\"input\":{\"descriptor_selector\":\"" + path + "\"}}}\n"
            + "{\"event_type\":\"Revoke\",\"payload\":{\"affected_frozen_node_ids\":[\"" + frozen + "\"]}}\n");
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

        var loaded = Assert.IsType<FrozenCoverageLoadOutcome.Loaded>(
            FrozenCoverageLedger.Load(syntax));

        Assert.Empty(loaded.ActiveFrozenPaths);
    }

    [Fact]
    public void ReattestReplacesTheActiveNodeIdentityBeforeRevocation()
    {
        const string frozen = "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
        const string reattested = "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
        const string path = "D5/S0/Carrier/Ring.lean";
        var bytes = Encoding.UTF8.GetBytes(
            "{\"event_type\":\"Genesis\",\"payload\":{}}\n"
            + "{\"event_type\":\"Freeze\",\"payload\":{\"frozen_node_id\":\"" + frozen
            + "\",\"input\":{\"descriptor_selector\":\"" + path + "\"}}}\n"
            + "{\"event_type\":\"Reattest\",\"payload\":{\"frozen_node_id\":\"" + reattested
            + "\",\"input\":{\"descriptor_selector\":\"" + path + "\"}}}\n"
            + "{\"event_type\":\"Revoke\",\"payload\":{\"affected_frozen_node_ids\":[\"" + reattested + "\"]}}\n");
        var syntax = Assert.IsType<DagLedgerLoadOutcome.Loaded>(DagLedgerLoader.Load(bytes)).Syntax;

        var loaded = Assert.IsType<FrozenCoverageLoadOutcome.Loaded>(
            FrozenCoverageLedger.Load(syntax));

        Assert.Empty(loaded.ActiveFrozenPaths);
    }

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
