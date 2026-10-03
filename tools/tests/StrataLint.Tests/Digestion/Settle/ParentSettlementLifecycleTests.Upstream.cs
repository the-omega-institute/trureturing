using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.DigestionTestSupport;
using static StrataLint.TestSupport.NonpropositionalTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void ExplicitUpstreamParentRequiresOwnReceiptAndReopensAfterDescendantClear()
    {
        const string statement = "**Theorem 1.1** For every natural number n, n + 0 = n.\n\n";
        const string proof = "**Proof** Apply Nat.add_zero to n.\n";
        const string justification = "All clauses follow from Nat.add_zero; no frozen project GID is available.";
        var fixture = new DecomposeFixture(statement + proof);
        var originalContext = DigestionAtomContextProjection.Resolve(
            fixture.Snapshot, fixture.Document, fixture.Parent.AtomId);
        Assert.Null(originalContext.Previous);
        Assert.Null(originalContext.Next);
        var decomposition = DecomposeAtomCommand.Run("synthetic", fixture.Gateway,
            [.. fixture.Args(), "--split-at", Encoding.UTF8.GetByteCount(statement)
                .ToString(System.Globalization.CultureInfo.InvariantCulture)], fixture.Apply);
        Assert.True(decomposition.Success, decomposition.Error);
        var parent = fixture.Document.RequireDigestionEntries().Single(entry => entry.AtomId == fixture.Parent.AtomId);
        var children = parent.Receipts.ChainAtoms;
        Assert.Equal(2, children.Length);
        Assert.Equal(Encoding.UTF8.GetBytes(statement + proof), children.SelectMany(id =>
            fixture.Current.Entries.Single(entry => entry.Path == DigestionCasStore.RootPath + id).Bytes).ToArray());
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var parentBytes = BackfillInventoryWriter.WriteAtom(parent).ToArray();

        string Request(string id, string? previous, string? next) =>
            $"atom_id = '{id}'\njustification = '{justification}'\n"
            + $"previous_atom_id = '{previous ?? "source-boundary"}'\n"
            + $"next_atom_id = '{next ?? "source-boundary"}'\n";

        for (var index = 0; index < children.Length; index++)
        {
            // Expected neighbors come from the lossless two-clause source, not the context query.
            var request = Request(children[index], index == 0 ? null : children[0],
                index == 0 ? children[1] : null);
            var settled = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, request);
            Assert.True(settled.Success, settled.Error);
            fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        }
        var evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            fixture.Document, fixture.Snapshot, AcceptedLean(Array.Empty<string>()), baselineDocument: fixture.Document);
        Assert.Empty(evaluation.Findings);
        var evaluatedParent = evaluation.Entries.Single(item => item.Entry.AtomId == parent.AtomId);
        Assert.Equal("residual-open", StateName(evaluatedParent.DerivedStatus));
        Assert.Contains(evaluatedParent.Gaps, gap => gap.Code == "coverage-gid-missing");
        Assert.DoesNotContain(evaluatedParent.Gaps, gap => gap.Code == "chain-migration-incomplete");
        Assert.All(evaluation.Entries.Where(item => children.Contains(item.Entry.AtomId)), item =>
            Assert.Equal(State, StateName(item.DerivedStatus)));
        Assert.Equal(parentBytes, fixture.Current.Entries.Single(entry => entry.Path == PathFor(parent)).Bytes.ToArray());
        var stream = DigestionAtomContextProjection.MaterializeSource(fixture.Snapshot, fixture.Document, parent.SourceId);
        Assert.Equal(children.ToArray(), stream.AtomIds.ToArray());
        var parentContext = Assert.Single(stream.ResolveOccurrences(parent.AtomId));
        Assert.Equal(Encoding.UTF8.GetBytes(statement + proof), parentContext.Current.RawBytes.ToArray());
        Assert.Null(parentContext.Previous);
        Assert.Null(parentContext.Next);
        Assert.Equal((1, 1), (parentContext.Index, parentContext.Count));

        var result = SettleAtomCommandTests.Run(temporary.Path, fixture.Current,
            Request(parent.AtomId, originalContext.Previous?.AtomId, originalContext.Next?.AtomId));
        Assert.True(result.Success, result.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            fixture.Document, fixture.Snapshot, AcceptedLean(Array.Empty<string>()), baselineDocument: fixture.Document);
        Assert.Empty(evaluation.Findings);
        Assert.Equal(State, StateName(evaluation.Entries.Single(item => item.Entry.AtomId == parent.AtomId).DerivedStatus));

        var clearParent = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, "",
            ["--clear", parent.AtomId, "--base", "baseline"]);
        Assert.True(clearParent.Success, clearParent.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        Assert.Equal(parentBytes, fixture.Current.Entries.Single(entry => entry.Path == PathFor(parent)).Bytes.ToArray());
        result = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, Request(parent.AtomId, null, null));
        Assert.True(result.Success, result.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);

        // A cleared child must restore its own obligation without changing its parent or sibling.
        var closedSnapshot = fixture.Current;
        var clear = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, "",
            ["--clear", children[0], "--base", "baseline"]);
        Assert.True(clear.Success, clear.Error);
        Assert.Contains("SETTLE_ALIGN_REQUIRED ancestors=" + parent.AtomId, clear.Output, StringComparison.Ordinal);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        foreach (var entry in closedSnapshot.Entries.Where(entry =>
                     !entry.Path.EndsWith("/" + children[0] + ".yaml", StringComparison.Ordinal)))
            Assert.Equal(entry.Bytes.ToArray(), fixture.Current.Entries.Single(current => current.Path == entry.Path).Bytes.ToArray());
        var clearedChild = fixture.Document.RequireDigestionEntries().Single(entry => entry.AtomId == children[0]);
        Assert.Null(clearedChild.Receipts.Nonpropositional);
        Assert.Equal("residual-open", StateName(clearedChild.ProjectedStatus));
        evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            fixture.Document, fixture.Snapshot, AcceptedLean(Array.Empty<string>()), baselineDocument: fixture.Document);
        Assert.Contains(evaluation.Findings, finding => finding.Contains("entry " + parent.AtomId + " handwritten status", StringComparison.Ordinal));
        evaluatedParent = evaluation.Entries.Single(item => item.Entry.AtomId == parent.AtomId);
        Assert.Equal("partial-open", StateName(evaluatedParent.DerivedStatus));
        Assert.Contains(evaluatedParent.Gaps, gap => gap.Code == "chain-migration-incomplete" && gap.Detail == children[0]);
    }
}
