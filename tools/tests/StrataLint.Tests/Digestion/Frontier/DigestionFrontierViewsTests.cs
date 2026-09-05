using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionFrontierViewsAndCorpusTests
{
    [Fact]
    public void ReadinessCandidatesSummaryAndStatusJsonAgreeOnFrontierCounts()
    {
        var fixture = DigestionFrontierFixture.Create();
        var readiness = DigestionReadinessQuery.Classify(fixture.Projection);
        var candidatesText = DigestFormalizeCandidates.Render(
            fixture.Projection,
            fixture.Snapshot,
            fixture.Document,
            selectedAtomId: null);
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

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MalformedStatusMarkerIsWithheldByFrontierAndCandidatesInEveryRetryMode(
        bool retryDispositions)
    {
        var marker = DigestionAtomStatusMarker.Parse(
            Encoding.UTF8.GetBytes("**定理 1.1**〔closed"));
        Assert.Equal(DigestionAtomStatusMarkerKind.Malformed, marker.Kind);
        var fixture = DigestionFrontierFixture.Create(
            retryDispositions,
            claimStatusMarker: marker);

        using var candidates = RenderCandidates(fixture);

        Assert.Equal(1, fixture.Projection.Total.FormalizationFrontier);
        var expectedWithheld = retryDispositions ? 2 : 3;
        Assert.Equal(expectedWithheld, fixture.Projection.Total.Withheld);
        Assert.Equal(1, candidates.RootElement.GetProperty("candidates").GetArrayLength());
        Assert.Equal(
            expectedWithheld,
            candidates.RootElement.GetProperty("withheld").GetArrayLength());
        var withheld = candidates.RootElement.GetProperty("withheld").EnumerateArray()
            .Single(item => item.GetProperty("atom_id").GetString() == DigestionFrontierFixture.ClaimId);
        Assert.Equal("malformed-status-marker", withheld.GetProperty("withhold_reason").GetString());
        var projected = fixture.Projection.Entries.Single(
            item => item.Entry.AtomId == DigestionFrontierFixture.ClaimId);
        Assert.Equal(DigestionFrontierDisposition.Withheld, projected.PrimaryDisposition);
        Assert.Equal("malformed-status-marker", projected.PrimaryDetail);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void QualifiedClosedStatusMarkerIsWithheldByFrontierAndCandidatesInEveryRetryMode(
        bool retryDispositions)
    {
        var marker = DigestionAtomStatusMarker.Parse(
            Encoding.UTF8.GetBytes("**定理 1.1**〔closed;数值证书〕。claim。"));
        Assert.Equal(DigestionAtomStatusMarkerKind.Valid, marker.Kind);
        var fixture = DigestionFrontierFixture.Create(
            retryDispositions,
            claimStatusMarker: marker);

        using var candidates = RenderCandidates(fixture);

        Assert.Equal(1, fixture.Projection.Total.FormalizationFrontier);
        var expectedWithheld = retryDispositions ? 2 : 3;
        Assert.Equal(expectedWithheld, fixture.Projection.Total.Withheld);
        Assert.Equal(1, candidates.RootElement.GetProperty("candidates").GetArrayLength());
        Assert.Equal(
            expectedWithheld,
            candidates.RootElement.GetProperty("withheld").GetArrayLength());
        var withheld = candidates.RootElement.GetProperty("withheld").EnumerateArray()
            .Single(item => item.GetProperty("atom_id").GetString() == DigestionFrontierFixture.ClaimId);
        Assert.Equal("qualified-closed-status", withheld.GetProperty("withhold_reason").GetString());
        Assert.Equal("数值证书", withheld.GetProperty("status_qualifier").GetString());
        var projected = fixture.Projection.Entries.Single(
            item => item.Entry.AtomId == DigestionFrontierFixture.ClaimId);
        Assert.Equal(DigestionFrontierDisposition.Withheld, projected.PrimaryDisposition);
        Assert.Equal("qualified-closed-status", projected.PrimaryDetail);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MalformedStatusMarkerPrecedesChainChildInEveryRetryMode(bool retryDispositions)
    {
        var marker = DigestionAtomStatusMarker.Parse(
            Encoding.UTF8.GetBytes("**定理 1.1**〔closed"));
        var fixture = DigestionFrontierFixture.Create(
            retryDispositions,
            chainChildStatusMarker: marker);

        var projected = fixture.Projection.Entries.Single(
            item => item.Entry.AtomId == DigestionFrontierFixture.ChainChildId);

        Assert.True(projected.IsChainChild);
        Assert.Equal(DigestionFrontierDisposition.Withheld, projected.PrimaryDisposition);
        Assert.Equal("malformed-status-marker", projected.PrimaryDetail);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MalformedStatusMarkerPrecedesNotFormalizableKindInEveryRetryMode(
        bool retryDispositions)
    {
        var marker = DigestionAtomStatusMarker.Parse(
            Encoding.UTF8.GetBytes("**定义 1.1**〔closed"));
        var fixture = DigestionFrontierFixture.Create(
            retryDispositions,
            structuralStatusMarker: marker);

        var projected = fixture.Projection.Entries.Single(
            item => item.Entry.AtomId == DigestionFrontierFixture.StructuralId);

        Assert.Equal(DigestionContentRole.NotFormalizable, projected.ContentRole);
        Assert.Equal(DigestionFrontierDisposition.Withheld, projected.PrimaryDisposition);
        Assert.Equal("malformed-status-marker", projected.PrimaryDetail);
    }

    [Theory]
    [InlineData(false, 2, 2)]
    [InlineData(true, 3, 1)]
    public void RetryCoverDispositionUsesTheSameFrontierAsCandidates(
        bool retryDispositions,
        int expectedFrontier,
        int expectedWithheld)
    {
        var fixture = DigestionFrontierFixture.Create(
            retryDispositions,
            coverKind: "theorem");

        using var candidates = RenderCandidates(fixture);

        Assert.Equal(expectedFrontier, fixture.Projection.Total.FormalizationFrontier);
        Assert.Equal(expectedWithheld, fixture.Projection.Total.Withheld);
        Assert.Equal(
            expectedFrontier,
            candidates.RootElement.GetProperty("candidates").GetArrayLength());
        Assert.Equal(
            expectedWithheld,
            candidates.RootElement.GetProperty("withheld").GetArrayLength());
        var candidateIds = candidates.RootElement.GetProperty("candidates").EnumerateArray()
            .Select(static item => item.GetProperty("atom_id").GetString())
            .ToArray();
        Assert.Equal(
            retryDispositions,
            candidateIds.Contains(DigestionFrontierFixture.CoverWithheldId, StringComparer.Ordinal));
    }

    [Fact]
    public void FormalizeCandidatesRejectUnknownDisposition()
    {
        var fixture = DigestionFrontierFixture.Create();
        var entry = fixture.Projection.Entries[0] with
        {
            PrimaryDisposition = (DigestionFrontierDisposition)99,
        };

        var error = Assert.Throws<InvalidOperationException>(() =>
            DigestFormalizeCandidates.Project(entry, fixture.Snapshot));

        Assert.Equal("unsupported disposition 99", error.Message);
    }

    [Fact]
    public void ReadinessRejectsUnknownDisposition()
    {
        var entry = DigestionFrontierFixture.Create().Projection.Entries[0] with
        {
            PrimaryDisposition = (DigestionFrontierDisposition)99,
        };

        var error = Assert.Throws<InvalidOperationException>(() =>
            DigestionReadinessQuery.ClassifyEntry(entry));

        Assert.Equal("unsupported disposition 99", error.Message);
    }

    [Fact]
    public void ResidualSummaryRejectsUnknownDisposition()
    {
        var error = Assert.Throws<InvalidOperationException>(() =>
            DigestResidualSummary.ClassifyDisposition((DigestionFrontierDisposition)99));

        Assert.Equal("unsupported disposition 99", error.Message);
    }

    private static JsonDocument RenderCandidates(
        DigestionFrontierFixture fixture) => JsonDocument.Parse(DigestFormalizeCandidates.Render(
            fixture.Projection,
            fixture.Snapshot,
            fixture.Document,
            selectedAtomId: null));
}
