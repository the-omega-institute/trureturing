using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

public sealed class DigestionFrontierViewsAndCorpusTests
{
    private static readonly Lazy<CorpusFixture> Corpus = new(LoadCorpus);

    [Fact]
    public void ReadinessCandidatesSummaryAndStatusJsonAgreeOnFrontierCounts()
    {
        var fixture = DigestionFrontierFixture.Create();
        var readiness = DigestionReadinessQuery.Classify(fixture.Projection);
        var candidatesText = DigestFormalizeCandidates.Render(
            fixture.Projection,
            fixture.Snapshot,
            fixture.Document,
            selectedAtomId: null,
            retryDispositions: false);
        var summary = DigestResidualSummary.Render(fixture.Evaluation, fixture.Projection);
        var statusText = DigestStatusCommand.RenderJson(fixture.Evaluation, fixture.Projection);

        Assert.Equal(fixture.Projection.Total.ResidualOpen, readiness.Length);
        Assert.Equal(fixture.Projection.Total.Quarantined, readiness.Count(static item => item.Action == "quarantined"));
        Assert.Equal(
            fixture.Projection.Total.Withheld,
            readiness.Count(static item => item.Action is "withheld" or "refresh-stale"));
        Assert.Equal(fixture.Projection.Total.ChainChild, readiness.Count(static item => item.Action == "chain-child"));
        Assert.Equal(fixture.Projection.Total.NotFormalizable, readiness.Count(static item => item.Action == "not-formalizable"));
        Assert.Equal(
            fixture.Projection.Total.FormalizableClaim,
            readiness.Count(static item => item.Action is "close-chain" or "deposit"));

        using var candidates = JsonDocument.Parse(candidatesText);
        Assert.Equal(
            fixture.Projection.Total.FormalizationFrontier,
            candidates.RootElement.GetProperty("candidates").GetArrayLength());
        Assert.Equal(
            fixture.Projection.Total.Quarantined,
            candidates.RootElement.GetProperty("quarantined").GetArrayLength());
        Assert.Equal(
            fixture.Projection.Total.Withheld,
            candidates.RootElement.GetProperty("withheld").GetArrayLength());

        Assert.Contains("## frontier", summary, StringComparison.Ordinal);
        Assert.Contains("- residual_open: 8", summary, StringComparison.Ordinal);
        Assert.Contains("- formalization_frontier: 2", summary, StringComparison.Ordinal);
        Assert.Contains("- quarantined: 1", summary, StringComparison.Ordinal);
        Assert.Contains("- withheld: 2", summary, StringComparison.Ordinal);
        Assert.Contains("- chain_child: 2", summary, StringComparison.Ordinal);
        Assert.Contains("- not_formalizable: 1", summary, StringComparison.Ordinal);
        Assert.Contains("- formalizable_claim: 2", summary, StringComparison.Ordinal);

        using var status = JsonDocument.Parse(statusText);
        var total = status.RootElement.GetProperty("frontier").GetProperty("total");
        Assert.Equal(fixture.Projection.Total.ResidualOpen, total.GetProperty("residual_open").GetInt32());
        Assert.Equal(fixture.Projection.Total.FormalizationFrontier, total.GetProperty("formalization_frontier").GetInt32());
        Assert.Equal(fixture.Projection.Total.Quarantined, total.GetProperty("quarantined").GetInt32());
        Assert.Equal(fixture.Projection.Total.Withheld, total.GetProperty("withheld").GetInt32());
        Assert.Equal(fixture.Projection.Total.ChainChild, total.GetProperty("chain_child").GetInt32());
        Assert.Equal(fixture.Projection.Total.NotFormalizable, total.GetProperty("not_formalizable").GetInt32());
        Assert.Equal(fixture.Projection.Total.FormalizableClaim, total.GetProperty("formalizable_claim").GetInt32());
        Assert.Equal(2, status.RootElement.GetProperty("frontier").GetProperty("per_source").GetArrayLength());
    }

    [Fact]
    public void StatusJsonEmitsPerEntryDispositionAndOrthogonalChainFacts()
    {
        var fixture = DigestionFrontierFixture.Create();

        using var status = JsonDocument.Parse(
            DigestStatusCommand.RenderJson(fixture.Evaluation, fixture.Projection));
        var entries = status.RootElement.GetProperty("frontier").GetProperty("entries");
        Assert.Equal(fixture.Projection.Total.ResidualOpen, entries.GetArrayLength());
        var quarantinedChainChild = entries.EnumerateArray().Single(entry =>
            entry.GetProperty("atom_id").GetString() == DigestionFrontierFixture.QuarantinedId);

        Assert.Equal("quarantined", quarantinedChainChild.GetProperty("primary_disposition").GetString());
        Assert.Equal("missing-prerequisite", quarantinedChainChild.GetProperty("primary_detail").GetString());
        Assert.Equal("theorem", quarantinedChainChild.GetProperty("kind_label").GetString());
        Assert.True(quarantinedChainChild.GetProperty("is_chain_child").GetBoolean());
        Assert.Equal(
            [DigestionFrontierFixture.ChainParentId],
            quarantinedChainChild.GetProperty("parent_atom_ids")
                .EnumerateArray()
                .Select(static parent => parent.GetString()));
    }

    [Fact]
    public void CurrentCorpusHasNoUnresolvedKindsAndPartitionsEveryResidualOpenEntry()
    {
        var corpus = Corpus.Value;

        Assert.All(corpus.Ledger.RequireDigestionEntries(), entry =>
        {
            corpus.ContentKinds.TryGetValue(entry.AtomId, out var kind);
            _ = DigestionContentDisposition.Resolve(kind);
        });
        Assert.Equal(
            corpus.Evaluation.Entries.Count(static item =>
                item.DerivedStatus.Migration == DigestionMigrationState.Residual
                && item.DerivedStatus.Truth == DigestionTruthState.Open),
            corpus.Projection.Total.ResidualOpen);
        Assert.Equal(
            corpus.Projection.Total.ResidualOpen,
            corpus.Projection.Total.Quarantined
                + corpus.Projection.Total.Withheld
                + corpus.Projection.Total.ChainChild
                + corpus.Projection.Total.NotFormalizable
                + corpus.Projection.Total.FormalizableClaim);
    }

    private static CorpusFixture LoadCorpus()
    {
        var root = TestRepositoryLayout.FindRoot();
        var raw = new GitRepositoryGateway(root).ReadCurrent();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var ledger = BackfillInventoryLoader.Load(snapshot);
        var evaluation = new DigestionLedgerEvaluation(
            ledger.RequireDigestionEntries()
                .Select(static entry => new DigestionEntryEvaluation(
                    entry,
                    DigestionReceiptAlignment.Seen,
                    entry.ProjectedStatus,
                    false,
                    []))
                .ToImmutableArray(),
            []);
        var contentKinds = DigestionContentKindResolver.Resolve(snapshot, ledger);
        var projection = DigestionFrontierProjection.Create(ledger, evaluation, contentKinds);
        return new CorpusFixture(ledger, evaluation, contentKinds, projection);
    }

    private sealed record CorpusFixture(
        BackfillInventoryDocument Ledger,
        DigestionLedgerEvaluation Evaluation,
        IReadOnlyDictionary<string, string> ContentKinds,
        DigestionFrontierProjection Projection);
}
