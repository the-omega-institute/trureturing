using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    public static IEnumerable<object[]> ClassificationCases()
    {
        foreach (var branch in new[] { "current-new-coverage", "current-new-receipts", "current-new-status",
            "current-changed", "current-deleted", "planned-covered-disappeared", "planned-covered-cleared",
            "planned-rewrite", "planned-new-coverage", "planned-new-receipts", "planned-new-status", "changed-covered" })
        foreach (var selection in new[] { "beta", "alpha", "all" })
            yield return [branch, selection];
    }

    [Theory]
    [MemberData(nameof(ClassificationCases))]
    public void IngestScope_ClassifierRespectsSelection_CurrentAndPlanned(string branch, string selection)
    {
        var baseline = Ledger();
        var alpha = baseline.RequireDigestionSources()[0];
        var entry = alpha.Entries[0];
        var beta = baseline.RequireDigestionSources()[1];
        var covered = entry with { Coverage = [new("D5/S0/Carrier/Alpha.a", null)] };
        var withReceipt = entry with { Receipts = entry.Receipts with { UnresolvedSubitems = ["obligation"] } };
        var partial = entry with { ProjectedStatus = new(DigestionMigrationState.Partial, DigestionTruthState.Open) };
        var current = baseline;
        var planned = baseline;
        var changes = RawChangeSet.Create(Array.Empty<string>());
        string witness;
        switch (branch)
        {
            case "current-new-coverage":
            case "current-new-receipts":
            case "current-new-status":
                baseline = baseline.WithDigestionSources([alpha with { Entries = [] }, beta]);
                current = current.WithDigestionSources([alpha with
                {
                    Entries = [branch == "current-new-coverage" ? covered : branch == "current-new-receipts" ? withReceipt : partial],
                }, beta]);
                witness = branch == "current-new-coverage" ? "is coverage-bearing"
                    : branch == "current-new-receipts" ? "carries receipts" : "projected status is not residual-open";
                break;
            case "current-changed":
                current = current.WithDigestionSources([alpha with { Entries = [withReceipt] }, beta]);
                witness = "changed status-authority inputs";
                break;
            case "current-deleted":
                current = current.WithDigestionSources([alpha with { Entries = [] }, beta]);
                witness = "removed";
                break;
            case "planned-covered-disappeared":
            case "planned-covered-cleared":
                current = current.WithDigestionSources([alpha with { Entries = [covered] }, beta]);
                planned = planned.WithDigestionSources([alpha with
                {
                    Entries = branch == "planned-covered-disappeared" ? [] : [entry],
                }, beta]);
                witness = branch == "planned-covered-disappeared" ? "disappeared from plan" : "coverage was cleared in plan";
                break;
            case "planned-rewrite":
                planned = planned.WithDigestionSources([alpha with { Entries = [withReceipt] }, beta]);
                witness = "planned rewrite of existing entry";
                break;
            case "planned-new-coverage":
            case "planned-new-receipts":
            case "planned-new-status":
                current = current.WithDigestionSources([alpha with { Entries = [] }, beta]);
                planned = planned.WithDigestionSources([alpha with
                {
                    Entries = [branch == "planned-new-coverage" ? covered : branch == "planned-new-receipts" ? withReceipt : partial],
                }, beta]);
                witness = branch == "planned-new-coverage" ? "is coverage-bearing"
                    : branch == "planned-new-receipts" ? "carries receipts" : "projected status is not residual-open";
                break;
            case "changed-covered":
                current = current.WithDigestionSources([alpha with { Entries = [covered] }, beta]);
                planned = current;
                baseline = current;
                changes = RawChangeSet.Create(["D5/S0/Carrier/Alpha.lean"]);
                witness = "changed status-authority inputs";
                break;
            default:
                throw new ArgumentOutOfRangeException(nameof(branch));
        }
        var sourceIds = selection == "all" ? null : ImmutableHashSet.Create(StringComparer.Ordinal, selection);
        var classification = branch.StartsWith("current-", StringComparison.Ordinal)
            ? IngestTruthAlignmentClassifier.ClassifyCurrent(LeanReportInputState.Unchanged, current, baseline, sourceIds)
            : IngestTruthAlignmentClassifier.ClassifyPlanned(current, baseline, planned,
                EmptyAlignment(planned), DigestionEvaluationScope.ChangedSet, changes, sourceIds);
        Assert.Equal(selection == "beta", classification.IsUncoveredOnly);
        if (selection == "beta") Assert.Null(classification.Witness);
        else
        {
            Assert.Contains(entry.AtomId, classification.Witness, StringComparison.Ordinal);
            Assert.Contains(witness, classification.Witness, StringComparison.Ordinal);
        }
    }

    [Theory]
    [InlineData("beta")]
    [InlineData("alpha")]
    public void IngestScope_LeanReportInputClosureGuardRemainsGlobal(string sourceId)
    {
        var document = Ledger();
        var classification = IngestTruthAlignmentClassifier.ClassifyCurrent(
            LeanReportInputState.Changed, document, document,
            ImmutableHashSet.Create(StringComparer.Ordinal, sourceId));
        Assert.False(classification.IsUncoveredOnly);
        Assert.Equal("Lean report input closure changed", classification.Witness);
        var fixture = Fixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var arguments = Arguments(sourceId);
        arguments[3] = "changed";
        var result = Environment(fixture, temporary).Ingest(arguments);
        Assert.Contains("INGEST_TRUTH_ALIGNMENT_REQUIRED Lean report input closure changed", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
    }
}
