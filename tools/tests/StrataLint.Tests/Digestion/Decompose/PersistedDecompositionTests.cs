using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class PersistedDecompositionTests
{
    [Theory]
    [InlineData("\r")]
    [InlineData("\r\n")]
    [InlineData("\n")]
    public void PersistedBoldChainPreservesLineEndingBytes(string newline)
    {
        AssertPersistedChain(AtomizerRegistry.GenericId,
            $"**Theorem 1.1** A \u03b1.{newline}{newline}",
            $"**Second** B \u03b2.{newline}");
    }

    [Theory]
    [InlineData("\r")]
    [InlineData("\r\n")]
    [InlineData("\n")]
    public void PersistedListChainPreservesLineEndingBytes(string newline)
    {
        AssertPersistedChain(AtomizerRegistry.GenericId,
            $"**Theorem 1.1** A.{newline}{newline}- first \u03b1{newline}",
            $"- second \u03b2{newline}{newline}Closing remark.{newline}");
    }

    [Theory]
    [InlineData("\r")]
    [InlineData("\r\n")]
    [InlineData("\n")]
    public void GenericAlignerAcceptsFrozenCasChainWithLineEndings(string newline)
    {
        var f = CreatePersistedChain(AtomizerRegistry.GenericId,
            $"**Theorem 1.1** A.{newline}{newline}",
            $"**Second** B.{newline}");
        Assert.False(AtomizerRegistry.EmitsClausePlans(AtomizerRegistry.GenericId));

        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot, f.Document, DigestionAlignmentMode.Ingest);
        Assert.Empty(alignment.Findings);
        Assert.Contains(f.Parent.AtomId, alignment.VerifiedClausePlanParents);
        Assert.Equal(0, f.Writes);
    }

    [Theory]
    [InlineData(AtomizerRegistry.GenericId)]
    [InlineData(AtomizerRegistry.PzgId)]
    [InlineData(AtomizerRegistry.GictId)]
    [InlineData(AtomizerRegistry.ConeId)]
    [InlineData(AtomizerRegistry.ObserverId)]
    [InlineData(AtomizerRegistry.PeriodicTreeId)]
    [InlineData(AtomizerRegistry.WmId)]
    [InlineData(DecomposeFixture.Dialect)]
    public void PersistedPreambleRemainsClaimZero(string atomizer)
    {
        AssertPersistedChain(atomizer,
            "# Bundle\r\n\r\nPreamble \u03b1.\r\n\r\n",
            "**First** Assertion \u03b2.\r\n\r\n",
            "**Second** Assertion \u03b3.\r\n");
    }

    [Fact]
    public void PersistedListKeepsPreambleAndClosingProseInChildren()
    {
        AssertPersistedChain(AtomizerRegistry.PzgId,
            "**\u5b9a\u7406 1.1**\n\nPreamble.\n\n- first\n",
            "- second\n\nClosing remark.\n");
    }

    [Fact]
    public void PersistedListIncludesEveryIndentationLevelAtContentOffsets()
    {
        // The real 25-child outlier changes indentation at numbered item ten.
        AssertPersistedChain(AtomizerRegistry.GenericId,
            "# References\n\nPreamble.\n\n1. Reference one\n   - first\n2. Reference two\n   ",
            "- second\n10. Reference ten\n    ",
            "- third\n\nClosing remark.\n");
    }

    [Fact]
    public void PersistedBoldMarkersInsideCodeRemainMaterialized()
    {
        AssertPersistedChain(AtomizerRegistry.GenericId,
            "# Bundle\n\n```text\n",
            "**Quoted** Code content.\n```\n\n",
            "**Detail** Assertion.\n");
    }

    private static DecomposeFixture CreatePersistedChain(string atomizer, params string[] persistedChildren)
    {
        var text = string.Concat(persistedChildren);
        var f = new DecomposeFixture(text, atomizer);
        var children = persistedChildren.Select(child => DecomposeFixture.Entry(child, atomizer)).ToArray();
        for (var index = 0; index < children.Length; index++)
            f.Add(children[index], persistedChildren[index]);
        var parent = f.Parent with
        {
            Receipts = f.Parent.Receipts with { ChainAtoms = [.. children.Select(child => child.AtomId)] },
        };
        f.Replace(parent);
        return f;
    }

    private static void AssertPersistedChain(string atomizer, params string[] persistedChildren)
    {
        var text = string.Concat(persistedChildren);
        var f = CreatePersistedChain(atomizer, persistedChildren);
        var parent = Assert.Single(f.Document.RequireDigestionEntries(), entry => entry.AtomId == f.Parent.AtomId);

        var plan = DigestionDecomposition.Plan(parent, DecomposeFixture.Atom(text).RawBytes,
            AtomizerRegistry.Require(atomizer).Atomize, f.Rules);
        Assert.Equal(persistedChildren.Length, plan.Children.Length);
        Assert.Equal(parent.Receipts.ChainAtoms.ToArray(),
            plan.Children.Select(child => child.Fingerprints.RawSha256[7..]).ToArray());
        for (var index = 0; index < persistedChildren.Length; index++)
            Assert.Equal(Encoding.UTF8.GetBytes(persistedChildren[index]), plan.Children[index].RawBytes.ToArray());
        Assert.Null(DigestionDecomposition.IntegrityFailure(plan));
        Assert.Equal(Encoding.UTF8.GetBytes(text), plan.Children.SelectMany(child => child.RawBytes).ToArray());

        var before = f.Current;
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        Assert.Contains("cas_objects=0 ledger_updates=0", result.Output, StringComparison.Ordinal);
        Assert.Same(before, f.Current);
        Assert.Equal(0, f.Writes);
        if (atomizer == AtomizerRegistry.GenericId)
        {
            var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot, f.Document, DigestionAlignmentMode.Ingest);
            Assert.Empty(alignment.Findings);
            Assert.Contains(parent.AtomId, alignment.VerifiedClausePlanParents);
        }
    }
}
