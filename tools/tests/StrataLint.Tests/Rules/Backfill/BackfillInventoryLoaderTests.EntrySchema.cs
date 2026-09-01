using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Fact]
    public void BaselineDirectoryAtomAllowsUnknownHistoricalKeyButStillRequiresCurrentFields()
    {
        var currentAtomId = FixtureAtomId("theorem/delta");
        var source = Source("delta-v0.1", "docs/delta.md", "none") with
        {
            Text = Source("delta-v0.1", "docs/delta.md", "none").Text
                + "acknowledged_stale = [\"legacy-delta\"]\n",
        };
        var atom = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var legacyAtomPath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/residual-open/legacy-delta.yaml";
        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            source,
            (legacyAtomPath, atom.Text + "ast_path: theorem/delta\n")));

        Assert.Equal(currentAtomId, Assert.Single(document.RequireDigestionEntries()).AtomId);
        Assert.Equal([currentAtomId], Assert.Single(document.RequireDigestionSources()).AcknowledgedStale.ToArray());

        var missingRequiredField = atom.Text.Replace(
            "coverage_gids: []\n",
            string.Empty,
            StringComparison.Ordinal);
        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadBaseline(Snapshot(
                source,
                (atom.Path, missingRequiredField))));

        Assert.Equal("source delta-v0.1 entry keys are not canonical", exception.Message);
    }

    [Fact]
    public void BaselineDirectoryProjectsHistoricalChainAtomReferencesToContentIdentity()
    {
        var source = Source("delta-v0.1", "docs/delta.md", "none");
        var parent = Atom("delta-v0.1", "residual-open", "parent", "theorem/parent");
        var child = Atom("delta-v0.1", "residual-open", "child", "theorem/child");
        var childText = child.Text.Replace(
            "  chain_atoms: []\n",
            "  chain_atoms:\n    - legacy-parent\n",
            StringComparison.Ordinal);
        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            source,
            ($"{BackfillInventoryLoader.RootPath}delta-v0.1/residual-open/legacy-parent.yaml", parent.Text),
            ($"{BackfillInventoryLoader.RootPath}delta-v0.1/residual-open/legacy-child.yaml", childText)));

        var projectedChild = document.RequireDigestionEntries()
            .Single(entry => entry.AtomId == FixtureAtomId("theorem/child"));
        Assert.Equal([FixtureAtomId("theorem/parent")], projectedChild.Receipts.ChainAtoms.ToArray());
    }

    [Fact]
    public void DirectoryAtomWriterEscapesSingleQuotesInQuotedScalars()
    {
        var atom = Atom("delta-v0.1", "residual-open", "delta", "theorem/delta");
        var text = atom.Text.Replace(
            "  tail_authorization: null\n",
            "  tail_authorization: null\n"
            + "  quarantine:\n"
            + "    justification: \"source's theorem: missing\"\n"
            + "    reentry_condition: retry\n",
            StringComparison.Ordinal);
        var entry = Assert.Single(BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, text))).RequireDigestionEntries());

        var written = System.Text.Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());

        Assert.Contains("justification: \"source's theorem: missing\"", written, StringComparison.Ordinal);
        var roundTripped = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "none"),
            (atom.Path, written)));
        Assert.Equal("source's theorem: missing", Assert.Single(roundTripped.RequireDigestionEntries())
            .Receipts.Quarantine?.Justification);
    }
}
