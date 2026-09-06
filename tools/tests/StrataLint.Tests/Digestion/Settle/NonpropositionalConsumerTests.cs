using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.NonpropositionalTestSupport;

namespace StrataLint.Tests;

public sealed class NonpropositionalConsumerTests
{
    [Fact]
    public void NonpropositionalIsAbsentFromResidualAndFormalizationFrontierButRendersInStatus()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        fixture = fixture.WithEntries([entry]);
        var evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            fixture.Ledger, Decode(WithCas(fixture)), DigestionTestSupport.AcceptedLean(Array.Empty<string>()));
        var frontier = DigestionFrontierProjection.Create(fixture.Ledger, evaluation,
            new Dictionary<string, string> { [entry.AtomId] = "theorem" }, false);
        Assert.Empty(frontier.Entries);
        Assert.Equal(0, frontier.Total.ResidualOpen);
        Assert.Equal(0, frontier.Total.FormalizationFrontier);
        Assert.Empty(DigestionReadinessQuery.Classify(frontier));
        Assert.DoesNotContain(entry.AtomId, DigestResidualSummary.Render(evaluation, frontier), StringComparison.Ordinal);
        Assert.Contains(State, DigestStatusCommand.RenderText(evaluation), StringComparison.Ordinal);
        var json = DigestStatusCommand.RenderJson(evaluation, frontier, new DigestAtomAge(
            new Dictionary<string, DigestAgeRecord>(), new DigestAgeHistogram("all", 0, null,
                new Dictionary<string, int>(), new Dictionary<string, IReadOnlyDictionary<string, int>>()), []));
        using var parsed = JsonDocument.Parse(json);
        Assert.Contains("\"migration\": \"nonpropositional\"", json, StringComparison.Ordinal);
        Assert.Contains("\"truth\": \"inapplicable\"", json, StringComparison.Ordinal);
    }
}
