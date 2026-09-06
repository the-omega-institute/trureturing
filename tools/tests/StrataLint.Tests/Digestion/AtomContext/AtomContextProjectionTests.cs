using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.AtomContextFixture;

namespace StrataLint.Tests;

public sealed class AtomContextProjectionTests
{
    [Fact]
    public void AtomContextFailsClosedOnAbsentAtom()
    {
        var fixture = Create();
        AssertCode("ATOM_ABSENT", () => Resolve(fixture, new string('0', 64)));
    }

    [Fact]
    public void AtomContextFailsClosedOnAmbiguousAtom()
    {
        var fixture = Create();
        var source = fixture.Ledger.RequireDigestionSources().Single();
        fixture = fixture with { Ledger = fixture.Ledger.WithDigestionSources([source, source with
        {
            SourceId = "other", Entries = [.. source.Entries.Select(entry => entry with { SourceId = "other" })],
        }]) };
        AssertCode("ATOM_AMBIGUOUS", () => Resolve(fixture, Id(fixture.Atomized.Claims[1])));
    }

    [Fact]
    public void AtomContextFailsClosedOnAtomizerNone()
    {
        var fixture = Create();
        var source = fixture.Ledger.RequireDigestionSources().Single();
        fixture = fixture with { Ledger = fixture.Ledger.WithDigestionSources([source with
        {
            Atomizer = AtomizerRegistry.NoAtomizerId,
            Entries = [.. source.Entries.Select(entry => entry with { Atomizer = AtomizerRegistry.NoAtomizerId })],
        }]) };
        AssertCode("ATOMIZER_NONE", () => Resolve(fixture, Id(fixture.Atomized.Claims[1])));
    }

    [Fact]
    public void AtomContextFailsClosedOnMissingSource()
    {
        var fixture = Create();
        AssertCode("SOURCE_MISSING", () => DigestionAtomContextProjection.Resolve(
            fixture.Snapshot(includeSource: false), fixture.Ledger, Id(fixture.Atomized.Claims[1])));
    }

    [Fact]
    public void AtomContextFailsClosedOnMissingOccurrence()
    {
        var fixture = Create();
        var target = Id(fixture.Atomized.Claims[1]);
        fixture = fixture with { SourceBytes = Encoding.UTF8.GetBytes("## Changed\n\nOther.\n") };
        AssertCode("OCCURRENCE_MISSING", () => Resolve(fixture, target));
    }

    [Fact]
    public void AtomContextFailsClosedOnAmbiguousOccurrence()
    {
        var fixture = Create();
        var target = Id(fixture.Atomized.Claims[1]);
        fixture = fixture with { SourceBytes = Encoding.UTF8.GetBytes(ThreeClaims + ThreeClaims) };
        AssertCode("OCCURRENCE_AMBIGUOUS", () => Resolve(fixture, target));
    }

    [Fact]
    public void AtomContextReturnsByteOrderedNeighborsNotHashOrder()
    {
        var fixture = Create();
        var claims = fixture.Atomized.Claims;
        Assert.False(claims.Select(Id).SequenceEqual(claims.Select(Id).Order(StringComparer.Ordinal)));
        var result = Resolve(fixture, Id(claims[1]));
        Assert.Equal(Id(claims[0]), result.Previous!.Value.AtomId);
        Assert.Equal(Id(claims[2]), result.Next!.Value.AtomId);
        Assert.Equal(claims[0].RawBytes.ToArray(), result.Previous.Value.RawBytes.ToArray());
        Assert.Equal(claims[2].RawBytes.ToArray(), result.Next.Value.RawBytes.ToArray());
        Assert.Equal("residual-open", result.Previous.Value.LedgerState);
        Assert.Equal((2, 3), (result.Index, result.Count));
        Assert.Equal(("source", SourcePath, "generic-v1"), (result.SourceId, result.SourcePath, result.Atomizer));
    }

    [Fact]
    public void AtomContextExpandsChainParentIntoChildrenAndNeverPairsParentWithChild()
    {
        var fixture = Create(ListClaims, expand: true);
        var plan = Assert.Single(fixture.Atomized.ClausePlans);
        Assert.Equal(3, plan.Children.Length);
        var result = Resolve(fixture, Id(plan.Children[1]));
        Assert.Equal(Id(plan.Children[0]), result.Previous!.Value.AtomId);
        Assert.Equal(Id(plan.Children[2]), result.Next!.Value.AtomId);
        Assert.Equal((3, 5), (result.Index, result.Count));
        var first = Resolve(fixture, Id(plan.Children[0]));
        Assert.Equal(Id(fixture.Atomized.Claims[0]), first.Previous!.Value.AtomId);
        var last = Resolve(fixture, Id(plan.Children[2]));
        Assert.Equal(Id(fixture.Atomized.Claims[2]), last.Next!.Value.AtomId);
        AssertCode("OCCURRENCE_MISSING", () => Resolve(fixture, Id(plan.Parent)));
    }

    [Fact]
    public void AtomContextRecursivelyExpandsNestedChains()
    {
        const string text = "## Before\n\nBefore.\n\n## Bundle\n\nPreamble.\n\n**Items**\n\n* Alpha;\n* Beta;\n* Gamma.\n\n## After\n\nAfter.\n";
        var fixture = Create(text, expand: true);
        var parentPlan = Assert.Single(fixture.Atomized.ClausePlans);
        var list = parentPlan.Children[1];
        var nested = Assert.IsType<DigestionClausePlan>(DigestionDecomposition.PlanClauses(list));
        var entries = fixture.Ledger.RequireDigestionEntries().ToDictionary(static entry => entry.AtomId);
        var materialized = DigestionDecomposition.Materialize(entries[Id(list)], nested, entries);
        entries[Id(list)] = materialized.Parent;
        foreach (var child in materialized.NewEntries) entries.Add(child.AtomId, child);
        fixture = fixture.WithEntries(entries.Values);
        var result = Resolve(fixture, Id(nested.Children[1]));
        Assert.Equal(Id(nested.Children[0]), result.Previous!.Value.AtomId);
        Assert.Equal(Id(nested.Children[2]), result.Next!.Value.AtomId);
        Assert.Equal((4, 6), (result.Index, result.Count));
    }

    [Fact]
    public void AtomContextRejectsChainThatDisagreesWithPlan()
    {
        var fixture = Create(ListClaims, expand: true);
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries().Select(entry =>
            entry.Receipts.ChainAtoms.IsEmpty ? entry : entry with
            {
                Receipts = entry.Receipts with { ChainAtoms = [.. entry.Receipts.ChainAtoms.Reverse()] },
            }));
        AssertCode("OCCURRENCE_MISSING", () => Resolve(fixture, Id(fixture.Atomized.Claims[0])));
    }

    [Fact]
    public void AtomContextReportsSourceStartAndEndBoundaries()
    {
        var fixture = Create();
        var first = Resolve(fixture, Id(fixture.Atomized.Claims[0]));
        Assert.Null(first.Previous);
        Assert.Equal("source-start", first.PreviousBoundaryReason);
        Assert.NotNull(first.Next);
        Assert.Null(first.NextBoundaryReason);
        var last = Resolve(fixture, Id(fixture.Atomized.Claims[^1]));
        Assert.Null(last.Next);
        Assert.Equal("source-end", last.NextBoundaryReason);
        Assert.NotNull(last.Previous);
        Assert.Null(last.PreviousBoundaryReason);
        Assert.Equal((1, 3), (first.Index, last.Index));
    }

    [Fact]
    public void AtomContextSingletonHasNoNeighbors()
    {
        var fixture = Create("## Alone\n\nOnly.\n");
        var result = Resolve(fixture, Id(fixture.Atomized.Claims.Single()));
        Assert.Null(result.Previous);
        Assert.Null(result.Next);
        Assert.Equal("source-start", result.PreviousBoundaryReason);
        Assert.Equal("source-end", result.NextBoundaryReason);
        Assert.Equal((1, 1), (result.Index, result.Count));
    }

    [Fact]
    public void AtomContextKeepsUnregisteredScaffoldsInTheStream()
    {
        var fixture = Create();
        fixture = fixture.WithEntries(fixture.Ledger.RequireDigestionEntries()
            .Where(entry => entry.AtomId == Id(fixture.Atomized.Claims[1])));
        var result = Resolve(fixture, Id(fixture.Atomized.Claims[1]));
        Assert.Equal(Id(fixture.Atomized.Claims[0]), result.Previous!.Value.AtomId);
        Assert.Null(result.Previous.Value.LedgerState);
        Assert.Null(result.Next!.Value.LedgerState);
    }

    private static DigestionAtomContext Resolve(AtomContextFixture fixture, string atomId) =>
        DigestionAtomContextProjection.Resolve(fixture.Snapshot(), fixture.Ledger, atomId);

    private static void AssertCode(string code, Action action) =>
        Assert.Equal(code, Assert.Throws<DigestionAtomContextException>(action).Code.ToString());
}
