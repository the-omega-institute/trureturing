using System.Collections.Immutable;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class FrozenLedgerV5CoreTests
{
    [Fact]
    public void BaseViewDerivesCaseAndNodeIdentityFromTheV5PropositionSnapshot()
    {
        var catalog = BuildCatalog(Module("A"));
        var expected = Assert.Single(catalog.ClosedNodes);
        var file = Assert.Single(EventFiles(catalog));

        var view = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            ImmutableDictionary<RepoPath, RepositoryFile>.Empty.Add(file.Path, file)));

        var entry = Assert.Single(view.ActiveByCase);
        Assert.Equal(
            FrozenLedgerCanonicalWriter.CaseId(expected.RepoPath, expected.StatementId),
            entry.Key);
        Assert.Equal(expected.FrozenNodeId, entry.Value.Material.FrozenNodeId);
        foreach (var retired in new[] { "case_id", "frozen_node_id", "witness_id", "input" })
        {
            Assert.DoesNotContain(
                entry.Value.Payload.GetType().GetProperties(),
                property => string.Equals(property.Name, retired, StringComparison.OrdinalIgnoreCase));
            Assert.DoesNotContain($"\"{retired}\"", file.Text, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void ClosedDagOrderingUsesDerivedFrozenNodeIdentity()
    {
        var catalog = BuildCatalog(Module("A"), Module("B", imports: ["A"]));
        var files = EventFiles(catalog).Reverse();

        var ordered = LoadEvents(files);

        Assert.Equal([PathFor("A"), PathFor("B")], ordered.Select(static item => item.DescriptorPath.Value));
        Assert.Equal(
            Assert.Single(catalog.ByPath[RepoPathFor("B")].PrerequisiteFrozenNodeIds),
            catalog.ByPath[RepoPathFor("A")].FrozenNodeId);
    }

    [Fact]
    public void RevocationClosureUsesFrozenBaseEdgesAndIncludesEveryDescendant()
    {
        var catalog = BuildCatalog(
            Module("A"),
            Module("B", imports: ["A"]),
            Module("C", imports: ["B"]));
        var view = BaseView(catalog);
        var root = view.ActiveByPath[RepoPathFor("A")].Material.FrozenNodeId;

        var closure = RevocationPlanner.ComputeClosure(view.ActiveByCase, [root]);

        var pathsByNode = view.ActiveByPath.Values.ToDictionary(
            static entry => entry.Material.FrozenNodeId,
            static entry => entry.Material.RepoPath.Value);
        Assert.Equal(
            [PathFor("A"), PathFor("B"), PathFor("C")],
            closure.AffectedFrozenNodeIds.Select(id => pathsByNode[id]).Order(StringComparer.Ordinal));
    }

    [Fact]
    public void KernelFailureReceiptBindsStatementInsteadOfRetiredWitnessIdentity()
    {
        var baseline = Baseline(BuildCatalog(Module("A")));
        var node = Assert.Single(baseline.ActiveFrozenNodes);
        var evidence = new RevocationEvidence.KernelWitnessFailure(
            node.FrozenNodeId,
            node.StatementId,
            string.Empty,
            string.Empty);

        var text = System.Text.Encoding.UTF8.GetString(
            RevocationReceiptWriter.Write(baseline, evidence).AsSpan());

        Assert.Contains("\"failed_statement_id\"", text, StringComparison.Ordinal);
        Assert.DoesNotContain("witness_id", text, StringComparison.Ordinal);
    }
}
