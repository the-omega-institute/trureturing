using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    public static IEnumerable<object[]> ObservationCases()
    {
        foreach (var branch in new[]
                 {
                     "current-only", "current-changed", "current-deleted",
                     "planned-covered-disappeared", "planned-covered-cleared", "planned-rewrite",
                 })
        foreach (var selection in new[] { "beta", "alpha", "all" })
            yield return [branch, selection];
    }

    [Theory]
    [MemberData(nameof(ObservationCases))]
    public void IngestScope_ObserverRespectsSelection_CurrentAndPlanned(
        string branch,
        string selection)
    {
        var baseline = Ledger();
        var alpha = baseline.RequireDigestionSources()[0];
        var entry = alpha.Entries[0];
        var beta = baseline.RequireDigestionSources()[1];
        var covered = entry with { Coverage = [new("D5/S0/Carrier/Alpha.a", null)] };
        var withReceipt = entry with
        {
            Receipts = entry.Receipts with { UnresolvedSubitems = ["obligation"] },
        };
        var current = baseline;
        var planned = baseline;
        string expectedKind;
        switch (branch)
        {
            case "current-only":
                baseline = baseline.WithDigestionSources([alpha with { Entries = [] }, beta]);
                current = current.WithDigestionSources([alpha with { Entries = [covered] }, beta]);
                expectedKind = "current-vs-base-changed";
                break;
            case "current-changed":
                current = current.WithDigestionSources([alpha with { Entries = [withReceipt] }, beta]);
                expectedKind = "current-vs-base-changed";
                break;
            case "current-deleted":
                current = current.WithDigestionSources([alpha with { Entries = [] }, beta]);
                expectedKind = "removed";
                break;
            case "planned-covered-disappeared":
            case "planned-covered-cleared":
                current = current.WithDigestionSources([alpha with { Entries = [covered] }, beta]);
                planned = planned.WithDigestionSources([alpha with
                {
                    Entries = branch == "planned-covered-disappeared" ? [] : [entry],
                }, beta]);
                expectedKind = branch == "planned-covered-disappeared"
                    ? "covered-disappeared"
                    : "covered-cleared";
                break;
            case "planned-rewrite":
                planned = planned.WithDigestionSources([alpha with { Entries = [withReceipt] }, beta]);
                expectedKind = "planned-rewrite";
                break;
            default:
                throw new ArgumentOutOfRangeException(nameof(branch));
        }

        var sourceIds = selection == "all"
            ? null
            : ImmutableHashSet.Create(StringComparer.Ordinal, selection);
        var observations = branch.StartsWith("current-", StringComparison.Ordinal)
            ? IngestPreservedExistingObserver.ObserveCurrent(current, baseline, sourceIds)
            : IngestPreservedExistingObserver.ObservePlanned(current, planned, sourceIds);

        if (selection == "beta") Assert.Empty(observations);
        else Assert.Contains(observations, observation =>
            observation.AtomId == entry.AtomId
            && observation.SourceId == "alpha"
            && observation.Kind == expectedKind);
    }

    [Theory]
    [InlineData("beta")]
    [InlineData("alpha")]
    public void IngestScope_LeanReportInputClosureGuardIsRetired(string sourceId)
    {
        var fixture = Fixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var environment = Environment(
            fixture,
            temporary,
            RawChangeSet.Create(["D5/S0/Carrier/Ring.lean"]));

        var result = environment.Ingest(Arguments(sourceId));
        var retired = environment.Ingest(
            ["--base", "baseline", "--report-input-state", "changed", "--source", sourceId]);

        Assert.True(result.Success, result.Error);
        Assert.False(retired.Success);
        Assert.Contains("USAGE:", retired.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("INGEST_TRUTH_ALIGNMENT_REQUIRED", retired.Error, StringComparison.Ordinal);
    }
}
