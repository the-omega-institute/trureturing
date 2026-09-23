using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Fact]
    public void BaselineToleratesOneAtomFiledUnderTwoStateDirectories()
    {
        var (openPath, openText) = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var (closedPath, closedText) = Atom("delta-v0.1", "absorbed-closed", "delta-atom", "theorem/delta");
        Assert.NotEqual(openPath, closedPath);

        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "pzg-v1"),
            (openPath, openText),
            (closedPath, closedText)));

        var entries = document.RequireDigestionEntries();
        Assert.Equal(2, entries.Length);
        Assert.Single(entries.Select(static entry => entry.AtomId).Distinct(StringComparer.Ordinal));
    }

    [Fact]
    public void CandidateLoadLeavesDuplicateAtomToTheEvaluator()
    {
        var (openPath, openText) = Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta");
        var (closedPath, closedText) = Atom("delta-v0.1", "absorbed-closed", "delta-atom", "theorem/delta");

        var document = BackfillInventoryLoader.Load(Snapshot(
            Source("delta-v0.1", "docs/delta.md", "pzg-v1"),
            (openPath, openText),
            (closedPath, closedText)));

        Assert.Equal(2, document.RequireDigestionEntries().Length);
    }
}
