using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void IngestRejectsMalformedChainWithoutClausePlan()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。current。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var baseline = Ledger([], CasEntry("parent", atom, captured.Reference));
        var source = Assert.Single(baseline.RequireDigestionSources());
        var candidate = baseline.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries.Select(entry => entry with
                {
                    Receipts = entry.Receipts with { ChainAtoms = ["child-atom"] },
                }).ToImmutableArray(),
            },
        ]);

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            candidate,
            Snapshot(sourceBytes, [captured]),
            baseline));

        Assert.Contains("parent CAS blob has no clause plan", exception.Message, StringComparison.Ordinal);
    }
}
