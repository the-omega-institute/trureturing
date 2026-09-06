using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    [Fact]
    public void AlignDigestionStatus_DeduplicatedClauseParentStillResolvesToZeroLedgerEntries()
    {
        var parent = Atom(ClauseText);
        var empty = TwoSourceLedger(
            EmptySource("alpha", AlphaPath),
            EmptySource("beta", BetaPath));
        var fixture = RobustFixture(empty, empty, ClauseText, ClauseText);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath, BetaPath])).AlignDigestionStatus(
                ["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains(
            $"INGEST_INVALID ingest clause plan parent {parent.Fingerprints.RawSha256} "
                + "resolves to 0 ledger entries",
            result.Error,
            StringComparison.Ordinal);
        Assert.DoesNotContain("clause-parent-deduplicated", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestClausePlan_DeduplicatedParentIsSkippedWithinOneRun()
    {
        var parent = Atom(ClauseText);
        var clausePlan = Assert.IsType<DigestionClausePlan>(
            DigestionDecomposition.PlanClauses(parent));
        var empty = TwoSourceLedger(
            EmptySource("alpha", AlphaPath),
            EmptySource("beta", BetaPath));
        var fixture = RobustFixture(empty, empty, ClauseText, ClauseText);
        var alphaText = fixture.Files[AlphaPath];
        var betaText = fixture.Files[BetaPath];
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath, BetaPath])).Ingest(Arguments());

        Assert.True(result.Success, result.Error);
        var document = BackfillInventoryLoader.Load(Decode(Overlay(temporary, fixture)));
        var alpha = document.RequireDigestionSources().Single(static source => source.SourceId == "alpha");
        var beta = document.RequireDigestionSources().Single(static source => source.SourceId == "beta");
        var parentId = parent.Fingerprints.RawSha256["sha256:".Length..];
        var parentEntry = Assert.Single(alpha.Entries, entry => entry.AtomId == parentId);
        Assert.Equal(clausePlan.Children.Length, parentEntry.Receipts.ChainAtoms.Length);
        Assert.All(parentEntry.Receipts.ChainAtoms, childId =>
            Assert.Single(alpha.Entries, entry => entry.AtomId == childId));
        Assert.Empty(beta.Entries);
        Assert.Equal(1 + clausePlan.Children.Length, alpha.Entries.Length);
        Assert.Equal(alphaText, fixture.Files[AlphaPath]);
        Assert.Equal(betaText, fixture.Files[BetaPath]);
        AssertObservation(result, parentId, "beta", "clause-parent-deduplicated");
        Assert.Single(PreservedRows(result), row => row.EndsWith(
            "kind=clause-parent-deduplicated", StringComparison.Ordinal));
    }

    [Fact]
    public void IngestClausePlan_DeduplicatedParentIsSkippedAcrossRuns()
    {
        var parent = Atom(ClauseText);
        var empty = TwoSourceLedger(
            EmptySource("alpha", AlphaPath),
            EmptySource("beta", BetaPath));
        var fixture = RobustFixture(empty, empty, ClauseText, ClauseText);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var first = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath])).Ingest(Arguments("alpha"));
        Assert.True(first.Success, first.Error);
        var afterFirst = DirectoryLedgerTestSupport.OverlayRepositoryFiles(temporary, fixture.Files);
        fixture.Files.Clear();
        foreach (var item in afterFirst) fixture.Files.Add(item.Key, item.Value);
        var beforeSecond = ExistingLedgerFiles(fixture.Files);

        var second = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([BetaPath])).Ingest(Arguments("beta"));

        Assert.True(second.Success, second.Error);
        var afterSecond = Overlay(temporary, fixture);
        AssertExistingLedgerFilesUnchanged(beforeSecond, afterSecond);
        var document = BackfillInventoryLoader.Load(Decode(afterSecond));
        var alpha = document.RequireDigestionSources().Single(static source => source.SourceId == "alpha");
        var beta = document.RequireDigestionSources().Single(static source => source.SourceId == "beta");
        var parentId = parent.Fingerprints.RawSha256["sha256:".Length..];
        Assert.Single(alpha.Entries, entry => entry.AtomId == parentId);
        Assert.Empty(beta.Entries);
        AssertObservation(second, parentId, "beta", "clause-parent-deduplicated");
        Assert.Single(PreservedRows(second));
    }
}
