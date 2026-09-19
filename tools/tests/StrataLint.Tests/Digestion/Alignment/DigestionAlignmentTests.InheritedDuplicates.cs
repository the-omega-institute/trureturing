using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    // Two lanes (an ingest and a cover) can each land one copy of the same records; the
    // merged tree then carries every record twice. Such duplicates are base-owned data:
    // admission must not judge the clause chain of a duplicated parent, whose duplicated
    // child would otherwise be reported as absent from the global inventory.
    [Fact]
    public void AdmissionDoesNotJudgeClauseChainOfBaselineInheritedDuplicates()
    {
        var fixture = SelfContainedClauseChain();
        var ledger = ChainLedger(fixture, fixture.Parent, fixture.Children);
        var source = Assert.Single(ledger.RequireDigestionSources());
        var duplicated = ledger.WithDigestionSources(
        [
            source with { Entries = [.. source.Entries, .. source.Entries] },
        ]);
        var snapshot = Snapshot(
            fixture.CurrentSourceBytes,
            fixture.ChildCaptures.Prepend(fixture.ParentCapture));

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            duplicated,
            snapshot,
            DigestionTestSupport.AcceptedLean(Array.Empty<string>()),
            baselineDocument: duplicated,
            baselineSnapshot: snapshot,
            changes: RawChangeSet.Create(["docs/source.md"]));

        Assert.True(
            !evaluation.Findings.Any(static finding =>
                finding.Contains("malformed clause chain", StringComparison.Ordinal)),
            string.Join(" | ", evaluation.Findings));
        Assert.Empty(evaluation.Entries);
        Assert.Equal(
            fixture.Children.Select(static child => child.AtomId).Prepend(fixture.Parent.AtomId)
                .Select(static atomId => $"duplicate atom_id inherited from baseline (not judged): {atomId}")
                .Order(StringComparer.Ordinal),
            evaluation.Observations
                .Where(static item => item.StartsWith("duplicate atom_id", StringComparison.Ordinal))
                .Order(StringComparer.Ordinal));
    }
}
