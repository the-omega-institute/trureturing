using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.UpstreamTestSupport;

namespace StrataLint.Tests;

public sealed class UpstreamConsumerTests
{
    [Theory]
    [InlineData("settle", "--request")]
    [InlineData("settle", "--clear")]
    [InlineData("quarantine", "--request")]
    [InlineData("quarantine", "--clear")]
    public void SiblingWritersRejectUpstreamWithoutWrites(string verb, string option)
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        fixture = fixture.WithEntries([entry]);
        var raw = WithCas(fixture);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, raw);
        using var temporary = new TemporaryDirectory();
        foreach (var file in raw.Entries)
        {
            var path = Path.Combine(temporary.Path, file.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, file.Bytes.ToArray());
        }
        var shardPath = Path.Combine(temporary.Path, PathFor(entry));
        var before = File.ReadAllBytes(shardPath);
        var request = $"atom_id = '{entry.AtomId}'\njustification = 'Reason'\n" + (verb == "settle"
            ? "previous_atom_id = 'source-boundary'\nnext_atom_id = 'source-boundary'\n"
            : "blocker_class = 'missing-prerequisite'\nreentry_condition = 'Supply proof'\n");
        var writes = 0;
        void ApplyUpdates(string root, RawRepositorySnapshot current, ImmutableArray<IngestCommand.LedgerUpdate> updates)
        {
            writes++;
            IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates);
        }
        var args = new[] { option, option == "--clear" ? entry.AtomId : "request.toml", "--base", "baseline" };
        var result = verb == "settle"
            ? SettleAtomCommand.Run(temporary.Path, gateway, args, BackfillInventoryWriter.WriteAtom,
                (_, _) => [.. Encoding.UTF8.GetBytes(request)], ApplyUpdates)
            : QuarantineAtomCommand.Run(temporary.Path, gateway, args, BackfillInventoryWriter.WriteAtom,
                (_, _) => [.. Encoding.UTF8.GetBytes(request)], ApplyUpdates);
        Assert.False(result.Success);
        Assert.Empty(result.Output);
        var errorPrefix = verb == "settle" ? "SETTLE_INVALID" : "QUARANTINE_INVALID";
        Assert.Equal($"{errorPrefix} UPSTREAM_PRESENT atom_id={entry.AtomId}\n", result.Error);
        Assert.Equal(0, writes);
        Assert.Equal(before, File.ReadAllBytes(shardPath));
    }

    [Fact]
    public void DecompositionRefusesUpstreamParent()
    {
        var fixture = new DecomposeFixture();
        var parent = Settled(fixture.Parent);
        var plan = DigestionDecomposition.Plan(parent, DecomposeFixture.Atom(DecomposeFixture.Bold).RawBytes,
            AtomizerRegistry.Require(DecomposeFixture.Dialect).Atomize, fixture.Rules)!;
        Assert.Contains("UPSTREAM_PRESENT", Assert.Throws<FormatException>(() =>
            DigestionDecomposition.Materialize(parent, plan, new Dictionary<string, DigestionLedgerEntry>())).Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void UpstreamIsOutsideFrontierAndFormalizableDenominatorAndCountedSeparately()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = Settled(fixture.Ledger.RequireDigestionEntries().Single());
        fixture = fixture.WithEntries([entry]);
        var snapshot = Decode(WithCas(fixture));
        foreach (var evaluation in new[] {
            DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
                fixture.Ledger, snapshot, DigestionTestSupport.AcceptedLean(Array.Empty<string>())),
            DigestionStatusEvaluator.EvaluateUncovered(DigestionEvaluationScope.FullScan, fixture.Ledger, snapshot) })
        {
            var frontier = DigestionFrontierProjection.Create(fixture.Ledger, evaluation,
                new Dictionary<string, string> { [entry.AtomId] = "theorem" }, false);
            Assert.Empty(frontier.Entries);
            Assert.Equal(0, frontier.Total.FormalizationFrontier);
            Assert.Equal(0, frontier.Total.FormalizableClaim);
            Assert.Empty(DigestionReadinessQuery.Classify(frontier));
            Assert.Contains("STATUS_COUNT upstream-closed=1", DigestStatusCommand.RenderText(evaluation), StringComparison.Ordinal);
            using var json = JsonDocument.Parse(DigestStatusCommand.RenderJson(evaluation, frontier, new DigestAtomAge(
                new Dictionary<string, DigestAgeRecord>(), new DigestAgeHistogram("all", 0, null,
                    new Dictionary<string, int>(), new Dictionary<string, IReadOnlyDictionary<string, int>>()), [])));
            var counts = json.RootElement.GetProperty("status_counts");
            Assert.Equal(1, counts.GetProperty("upstream_closed").GetInt32());
            foreach (var name in new[] { "residual_open", "partial_closed", "absorbed_closed", "nonpropositional_inapplicable" })
                Assert.Equal(0, counts.GetProperty(name).GetInt32());
            Assert.Equal(0, json.RootElement.GetProperty("formalizable_total").GetInt32());
        }
    }

    [Fact]
    public void ScribeNarrativeRejectsUpstreamStateVocabulary()
    {
        Assert.Contains(ScribeNarrativeScanner.Scan("var text = \"upstream-closed\";"),
            item => item.Class == "DigestionLedgerReference");
    }
}
