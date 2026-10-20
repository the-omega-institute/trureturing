using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AtomPointerRepairTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void TargetedMigrationKeepsTheObservedNeighborChain(bool saved)
    {
        const string target = "## Target\n\nTarget.\n\n";
        var f = new DecomposeFixture(target);
        var neighbor = DecomposeFixture.Entry(DecomposeFixture.Bold);
        f.Add(neighbor, DecomposeFixture.Bold);
        var plan = DigestionDecomposition.Plan(neighbor, DecomposeFixture.Atom(DecomposeFixture.Bold).RawBytes,
            AtomizerRegistry.Require(neighbor.Atomizer).Atomize, f.Snapshot);
        foreach (var child in plan.Children)
        {
            var body = Encoding.UTF8.GetString(child.RawBytes.AsSpan());
            f.Add(DecomposeFixture.Entry(body), body);
        }
        f.Replace(neighbor with { Receipts = neighbor.Receipts with
            { ChainAtoms = [.. plan.Children.Select(child => child.Fingerprints.RawSha256[7..])] } });
        var text = target + DecomposeFixture.Bold + "## End\n\nEnd.\n";
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", text);
        var expected = DigestionContextIndexBuilder.Build(f.Snapshot, f.Document, "probe").Index;
        if (saved) f.CaptureContext();
        else f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => !file.Path.Contains("/context/", StringComparison.Ordinal)));
        var invalid = AddInvalid(f, "Unrelated historical claim.\n");
        var result = AtomContextMigrationCommand.Run("fixture", f.Gateway,
            ["--source", "probe", "--atom-id", f.Parent.AtomId, "--write"], f.Apply);
        Assert.True(result.Success, result.Output + result.Error);
        if (saved) Assert.Contains("changed=0", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(f.Gateway.ScopedCurrentReads.SelectMany(paths => paths),
            path => path == DigestionQuerySelection.Literal(DecomposeFixture.PathFor(invalid)));
        DeleteProse(f);
        AssertSaved(f, expected);
        var read = AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]);
        Assert.True(read.Success, read.Error);
        Assert.Contains("NEXT atom_id=" + plan.Children[0].Fingerprints.RawSha256[7..], read.Output, StringComparison.Ordinal);
        Assert.Single(DigestionContextPointerStore.Load(f.Snapshot, "probe", f.Parent.AtomId));
    }

    [Fact]
    public void TargetedMigrationAppendsChangedNeighborGraphWithoutReplacingSavedObservation()
    {
        const string target = "## Target\n\nTarget.\n\n";
        var f = new DecomposeFixture(target);
        var neighbor = DecomposeFixture.Entry(DecomposeFixture.Bold);
        f.Add(neighbor, DecomposeFixture.Bold);
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", target + DecomposeFixture.Bold);
        f.CaptureContext();
        var original = DigestionContextPointerStore.Load(f.Snapshot, "probe", f.Parent.AtomId).Single();
        var plan = DigestionDecomposition.Plan(neighbor, DecomposeFixture.Atom(DecomposeFixture.Bold).RawBytes,
            AtomizerRegistry.Require(neighbor.Atomizer).Atomize, f.Snapshot);
        foreach (var child in plan.Children)
        {
            var body = Encoding.UTF8.GetString(child.RawBytes.AsSpan());
            f.Add(DecomposeFixture.Entry(body), body);
        }
        f.Replace(neighbor with { Receipts = neighbor.Receipts with
            { ChainAtoms = [.. plan.Children.Select(child => child.Fingerprints.RawSha256[7..])] } });
        var result = AtomContextMigrationCommand.Run("fixture", f.Gateway,
            ["--source", "probe", "--atom-id", f.Parent.AtomId, "--write"], f.Apply);
        Assert.True(result.Success, result.Output + result.Error);
        DeleteProse(f);
        var versions = DigestionContextPointerStore.Load(f.Snapshot, "probe", f.Parent.AtomId);
        Assert.Equal(2, versions.Length);
        Assert.Equal(DigestionContextPointerStore.Write(original).ToArray(),
            DigestionContextPointerStore.Write(versions.Single(version => version.GraphSha256 is null)).ToArray());
        Assert.Equal(plan.Children[0].Fingerprints.RawSha256[7..],
            versions.Single(version => version.GraphSha256 is not null).Entries[0].Occurrences.Single().NextAtomId);
        var read = AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]);
        Assert.True(read.Success, read.Error);
        Assert.Contains("NEXT atom_id=" + plan.Children[0].Fingerprints.RawSha256[7..], read.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SavedTargetMigrationIsolatesAnInvalidDistantObservedAccount()
    {
        const string text = "## Target\n\nTarget.\n\n## Middle\n\nMiddle.\n\n## Distant\n\nDistant.\n";
        const string distant = "## Distant\n\nDistant.\n";
        var f = new DecomposeFixture("## Target\n\nTarget.\n\n");
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", text);
        f.CaptureContext();
        var invalid = AddInvalid(f, distant);
        var result = AtomContextMigrationCommand.Run("fixture", f.Gateway,
            ["--source", "probe", "--atom-id", f.Parent.AtomId, "--write"], f.Apply);
        Assert.True(result.Success, result.Output + result.Error);
        Assert.Contains("changed=0", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(f.Gateway.ScopedCurrentReads.SelectMany(paths => paths),
            path => path == DigestionQuerySelection.Literal(DecomposeFixture.PathFor(invalid)));
        DeleteProse(f);
        Assert.True(AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]).Success);
    }

    [Fact]
    public void TargetedMigrationRejectsAnInvalidObservedNeighbor()
    {
        const string target = "## Target\n\nTarget.\n\n";
        const string neighbor = "## Neighbor\n\nNeighbor.\n";
        var f = new DecomposeFixture(target);
        var invalid = AddInvalid(f, neighbor);
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", target + neighbor);
        var result = AtomContextMigrationCommand.Run("fixture", f.Gateway,
            ["--source", "probe", "--atom-id", f.Parent.AtomId, "--write"], f.Apply);
        Assert.False(result.Success);
        Assert.Contains("cannot be quarantined because coverage", result.Output + result.Error, StringComparison.Ordinal);
        Assert.Contains(invalid.AtomId, result.Output + result.Error, StringComparison.Ordinal);
        Assert.Equal(0, f.Writes);
    }

    [Theory]
    [InlineData("single")]
    [InlineData("separated")]
    [InlineData("adjacent")]
    public void DecompositionSplicesEveryOccurrenceAndBothExteriorEdges(string layout)
    {
        var text = "## Before\n\nBefore.\n\n" + DecomposeFixture.Bold
            + (layout == "adjacent" ? "" : "## After\n\nAfter.\n")
            + (layout == "single" ? "" : DecomposeFixture.Bold);
        var f = new DecomposeFixture();
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", text);
        f.CaptureContext();
        DeleteProse(f);
        var result = DecomposeAtomCommand.Run("fixture", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        AssertSavedMatchesSource(f, text);
    }

    [Theory]
    [InlineData("list")]
    [InlineData("table")]
    public void DecompositionKeepsSiblingStructuresOutOfIndependentChildren(string structure)
    {
        var governed = structure == "list"
            ? "The equivalence does not require:\n- surjectivity;\n- a section.\n\n"
            : "The columns mean hypotheses and consequences.\n\n| Hypothesis | Consequence |\n| --- | --- |\n| Alpha | Beta |\n\n";
        var text = "## Governed\n\n" + governed + "## Independent\n\nIndependent claim.\n";
        var f = new DecomposeFixture(text);
        DeleteProse(f);
        var result = DecomposeAtomCommand.Run("fixture", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        var children = f.Document.RequireDigestionEntries().Single(entry => entry.AtomId == f.Parent.AtomId).Receipts.ChainAtoms;
        var independent = children.Single(id => Encoding.UTF8.GetString(f.Current.Entries.Single(file =>
            file.Path == DigestionCasStore.RootPath + id).Bytes.AsSpan()).Contains("Independent claim.", StringComparison.Ordinal));
        var loaded = DigestionQuerySelection.ReadContext(f.Gateway, independent);
        var context = DigestionAtomContextProjection.Resolve(loaded.Snapshot, loaded.Document, independent);
        Assert.DoesNotContain(context.GoverningContext, scope => scope.Relation is "governed-list" or "table-definition");
        AssertSavedMatchesSource(f, text);
    }

    [Theory]
    [InlineData("list")]
    [InlineData("table")]
    public void DecompositionRetainsStructuresGoverningTheEntireParent(string structure)
    {
        const string parent = "First assertion. Second assertion.";
        var text = structure == "list"
            ? "## Governed\n\nThe conditions are:\n- " + parent + "\n- Other condition.\n"
            : "## Governed\n\nThe columns mean hypotheses and consequences.\n\n| Hypothesis | Consequence |\n| --- | --- |\n| " + parent + " | Beta |\n";
        var f = new DecomposeFixture(parent);
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", text);
        f.CaptureContext();
        DeleteProse(f);
        var result = DecomposeAtomCommand.Run("fixture", f.Gateway, [.. f.Args(), "--split-at", "17"], f.Apply);
        Assert.True(result.Success, result.Error);
        AssertSavedMatchesSource(f, text);
        foreach (var child in f.Document.RequireDigestionEntries().Single(entry => entry.AtomId == f.Parent.AtomId).Receipts.ChainAtoms)
        {
            var loaded = DigestionQuerySelection.ReadContext(f.Gateway, child);
            var context = DigestionAtomContextProjection.Resolve(loaded.Snapshot, loaded.Document, child);
            Assert.Contains(context.GoverningContext, scope => scope.Relation == (structure == "list" ? "governed-list" : "table-definition"));
        }
    }

    private static void AssertSavedMatchesSource(DecomposeFixture f, string text)
    {
        var withProse = RawRepositorySnapshot.Create(f.Current.Entries.Append(RawRepositoryEntry.FromText("docs/probe.md", text)));
        var expected = DigestionContextIndexBuilder.Build(DecomposeFixture.Decode(withProse), f.Document, "probe").Index;
        AssertSaved(f, expected);
        foreach (var entry in f.Document.RequireDigestionEntries())
        {
            var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", entry.AtomId]);
            Assert.True(result.Success, result.Error);
        }
        Assert.DoesNotContain(f.Gateway.ScopedCurrentReads.SelectMany(paths => paths), path => path == ":(literal)docs/probe.md");
    }

    private static void AssertSaved(DecomposeFixture f, DigestionContextPointerIndex expected)
    {
        foreach (var entry in expected.Entries)
        {
            var actual = DigestionContextPointerStore.Load(f.Snapshot, "probe", entry.AtomId).Single();
            Assert.Equal(Encoding.UTF8.GetString(DigestionContextPointerStore.Write(expected with { Entries = [entry] }).AsSpan()),
                Encoding.UTF8.GetString(DigestionContextPointerStore.Write(actual).AsSpan()));
        }
    }

    private static void DeleteProse(DecomposeFixture f) => f.Current = RawRepositorySnapshot.Create(
        f.Current.Entries.Where(file => file.Path != "docs/probe.md"));

    private static DigestionLedgerEntry AddInvalid(DecomposeFixture f, string body)
    {
        var entry = DecomposeFixture.Entry(body) with
        {
            Coverage = [new("D5/S1/Solenoid/RealFlowInjectivity.realFlow_injective", "sha256:" + new string('a', 64))],
            Receipts = new([], [], null, new("blocked", "supply witness", "multi-clause-guard")),
        };
        f.Add(entry, body);
        return entry;
    }
}
