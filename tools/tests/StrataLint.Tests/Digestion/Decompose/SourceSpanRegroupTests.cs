using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

// Private source-span fixture. Only CAS bytes come from the fixed historical frame;
// all ledger entries belong to the synthetic probe source, with no real coverage/status claims.
public sealed class SourceSpanRegroupTests
{
    // b1a766500edbea14cd043c76296732ce7c54a5c6:Meta/Digestion/atoms/sha256/cb34c7042532de49c5d101b960438736d2be8b0cbe9328b5466dc2e78c6b1d5d
    private const string Text = "## theorem 1: Exact stationary occupation-memory minimum\n\nFor a finite nonempty alphabet and capacities a_i>=0, the exact minimum is\n\n    D_min = product_i(a_i+1) - max_i a_i.\n\nFor a=(4,2,1,1), this gives60-4=56. It replaces the earlier ordinary interval\n20<=D_min<=56 for this specific model. Time-dependent controls still belong\nto the separate minimum12 problem.\n\n";

    [Fact]
    public void ExactSourceSpansRequireCutsAndProduceThePreservedNestedShape()
    {
        var bytes = Encoding.UTF8.GetBytes(Text);
        Assert.Equal(367, bytes.Length);
        var group = Encoding.UTF8.GetString(bytes[..294]);
        var parts = new[] { Encoding.UTF8.GetString(bytes[..177]), Encoding.UTF8.GetString(bytes[177..213]),
            Encoding.UTF8.GetString(bytes[213..294]), Encoding.UTF8.GetString(bytes[294..]) };
        var f = new DecomposeFixture(Text, AtomizerRegistry.GenericId);
        var children = parts.Select(text => DecomposeFixture.Entry(text, AtomizerRegistry.GenericId)).ToArray();
        for (var index = 0; index < parts.Length; index++) f.Add(children[index], parts[index]);
        var nested = DecomposeFixture.Entry(group, AtomizerRegistry.GenericId);
        f.Add(nested, group);
        f.Replace(f.Parent with { Receipts = f.Parent.Receipts with { ChainAtoms = [.. children.Select(e => e.AtomId)] } });
        Assert.Null(DigestionDecomposition.PlanClauses(DecomposeFixture.Atom(Text)));
        Assert.Null(DigestionDecomposition.PlanClauses(DecomposeFixture.Atom(group)));
        Assert.Equal("db69816dc1398fd509098ca181a7c0a5611d7d672f84d4d30224455575a545e3", nested.AtomId);
        Assert.Equal(new[] { "3c58cb906d906206c43885d23183fa3203cecac115f30b2829794392352e32ec",
            "9114434067390f1e295f493322ac3174651c5feae1d959983f914fcffcfd9e2e",
            "8cefcfb1f08fb27cce1b1679f2282954e4f0f6d8c76b12e6cd80919ed2c49039",
            "f7e723ac60c87e3255a2ac192a6d41e7639e9ace8cdb5793df3725897a3bc92f" }, children.Select(e => e.AtomId));
        var before = f.Current;
        var nestedResult = DecomposeAtomCommand.Run("synthetic", f.Gateway,
            [.. f.Args(nested.AtomId), "--split-at", "177", "--split-at", "213"], f.Apply);
        Assert.True(nestedResult.Success, nestedResult.Error);
        Assert.Empty(f.CasWrites);
        Assert.Single(f.LedgerWrites);
        var parentResult = DecomposeAtomCommand.Run("synthetic", f.Gateway,
            [.. f.Args(), "--reconcile-chain", "--split-at", "294"], f.Apply);
        Assert.True(parentResult.Success, parentResult.Error);
        Assert.Empty(f.CasWrites);
        Assert.Single(f.LedgerWrites);
        var parent = f.Document.RequireDigestionEntries().Single(e => e.AtomId == f.Parent.AtomId);
        var finalGroup = f.Document.RequireDigestionEntries().Single(e => e.AtomId == nested.AtomId);
        Assert.Equal(new[] { nested.AtomId, children[3].AtomId }, parent.Receipts.ChainAtoms);
        Assert.Equal(children.Take(3).Select(e => e.AtomId), finalGroup.Receipts.ChainAtoms);
        Assert.Empty(parent.Coverage);
        Assert.Empty(finalGroup.Coverage);
        foreach (var old in before.Entries.Where(e => e.Path != DecomposeFixture.PathFor(parent) && e.Path != DecomposeFixture.PathFor(nested)))
            Assert.Equal(old.Bytes.ToArray(), f.Current.Entries.Single(e => e.Path == old.Path).Bytes.ToArray());
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot, f.Document, DigestionAlignmentMode.Ingest);
        Assert.Empty(alignment.Findings);
        Assert.Contains(parent.AtomId, alignment.VerifiedClausePlanParents);
        Assert.Contains(nested.AtomId, alignment.VerifiedClausePlanParents);
    }
}
