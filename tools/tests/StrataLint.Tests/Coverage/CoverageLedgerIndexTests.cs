using System.Collections.Immutable;
using System.Text.Json;
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
        var loaded = Assert.IsType<FrozenCoverageLoadOutcome.Loaded>(
            FrozenCoverageLedger.Load(
            [
                Event("Genesis", new { }),
                Event("Freeze", new
                {
                    frozen_node_id = node,
                    input = new { descriptor_selector = "D5/S0/Carrier/Ring.lean" },
                }),
                Event("Revoke", new { affected_frozen_node_ids = new[] { node } }),
            ]));

        Assert.Empty(loaded.ActiveFrozenPaths);
    }

    [Fact]
    public void ExtendedReattestMigratesActiveNodeIdentityBeforeRevocation()
    {
        const string frozen = "sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
        const string reattested = "sha256:dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd";
        const string path = "D5/S0/Carrier/Ring.lean";
        var loaded = Assert.IsType<FrozenCoverageLoadOutcome.Loaded>(
            FrozenCoverageLedger.Load(
            [
                Event("Genesis", new { }),
                Freeze(frozen, path),
                Event("Reattest", new
                {
                    frozen_node_id = reattested,
                    input = new { descriptor_selector = path },
                }),
                Event("Revoke", new { affected_frozen_node_ids = new[] { reattested } }),
            ]));

        Assert.Empty(loaded.ActiveFrozenPaths);
    }

    [Fact]
    public void TwoActiveFrozenNodesCannotCollapseOntoOnePath()
    {
        const string first = "sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        const string second = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        const string path = "D5/S0/Carrier/Ring.lean";
        var invalid = Assert.IsType<FrozenCoverageLoadOutcome.Invalid>(
            FrozenCoverageLedger.Load(
            [
                Event("Genesis", new { }),
                Freeze(first, path),
                Freeze(second, path),
            ]));

        Assert.Contains("duplicate path", invalid.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnknownLedgerEventFailsClosed()
    {
        var invalid = Assert.IsType<FrozenCoverageLoadOutcome.Invalid>(
            FrozenCoverageLedger.Load([Event("Genesis", new { }), Event("Mystery", new { })]));

        Assert.Contains("unknown event", invalid.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RetiredSupersedeEventFailsClosed()
    {
        var invalid = Assert.IsType<FrozenCoverageLoadOutcome.Invalid>(
            FrozenCoverageLedger.Load([Event("Genesis", new { }), Event("Supersede", new { })]));

        Assert.Contains("unknown event type Supersede", invalid.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void StateChangingEventCannotPrecedeGenesis()
    {
        var invalid = Assert.IsType<FrozenCoverageLoadOutcome.Invalid>(
            FrozenCoverageLedger.Load([Event("Freeze", new { }), Event("Genesis", new { })]));

        Assert.Contains("before Genesis", invalid.Message, StringComparison.Ordinal);
    }

    private static DagLedgerFileEvent Freeze(string node, string path) => Event("Freeze", new
    {
        frozen_node_id = node,
        input = new { descriptor_selector = path },
    });

    [Fact]
    public void SchemaV4FreezeWithoutNodePathAliasIsIndexedByItsDescriptorSelector()
    {
        const string node = "sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
        var loaded = Assert.IsType<FrozenCoverageLoadOutcome.Loaded>(
            FrozenCoverageLedger.Load(
            [
                Event("Genesis", new { }),
                Freeze(node, "D5/S0/Carrier/Ring.lean"),
            ]));

        Assert.True(RepoPath.TryCreate("D5/S0/Carrier/Ring.lean", out var expected));
        Assert.Contains(expected, loaded.ActiveFrozenPaths);
    }

    private static DagLedgerFileEvent Event(string eventType, object payload) => new(
        RepoPath.CreateKnown($"Golden/Frozen/accepted/{eventType.ToLowerInvariant()}.json"),
        eventType,
        "sha256:" + new string('0', 64),
        eventType,
        JsonSerializer.SerializeToElement(payload),
        eventType == "Genesis" ? 2 : 4,
        null);
}
