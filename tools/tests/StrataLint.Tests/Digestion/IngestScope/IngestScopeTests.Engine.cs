using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{

    [Fact]
    public void IngestScope_WriteSetLimitedToSelectedSourcesAndNewCas()
    {
        const string alphaText = "## Claim 10\n\n- Alpha first.\n- Alpha second.\n";
        const string betaText = "## Claim 20\n\n- Beta first.\n- Shared fact.\n";
        var betaAtom = Atom(betaText);
        var clausePlan = Assert.IsType<DigestionClausePlan>(DigestionDecomposition.PlanClauses(betaAtom));
        var reused = clausePlan.Children[1];
        var alpha = Source("alpha", AlphaPath, alphaText);
        var sharedEntry = DigestionTestSupport.Entry(reused, reused.Fingerprints.RawSha256[7..],
            AtomizerRegistry.GenericId, sourceId: "alpha", sourcePath: AlphaPath);
        alpha = alpha with { Entries = alpha.Entries.Add(sharedEntry), AcknowledgedStale = [sharedEntry.AtomId] };
        var document = BackfillInventoryDocument.Create([alpha, Source("beta", BetaPath, betaText, false)], []);
        var fixture = Fixture(document, alphaText, betaText);
        foreach (var files in new[] { fixture.Files, fixture.Baseline }) AddCas(files, reused);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = Raw(fixture.Files);
        var result = Environment(fixture, temporary).Ingest(Arguments("beta"));
        Assert.True(result.Success, result.Error);
        var after = Raw(DirectoryLedgerTestSupport.OverlayRepositoryFiles(temporary, fixture.Files));
        var updates = IngestCommand.LedgerUpdates(before, after);
        Assert.Equal(2, updates.Length);
        Assert.All(updates, static item => Assert.StartsWith(SourcePrefix("beta"), item.Path, StringComparison.Ordinal));
        Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));
        var entries = BackfillInventoryLoader.Load(Decode(after)).RequireDigestionEntries();
        var parent = entries.Single(entry => entry.AtomId == betaAtom.Fingerprints.RawSha256[7..]);
        Assert.Contains(sharedEntry.AtomId, parent.Receipts.ChainAtoms);
        Assert.Equal("alpha", entries.Single(entry => entry.AtomId == sharedEntry.AtomId).SourceId);
        var newCasPaths = after.Entries.Where(static item => DigestionCasStore.IsCanonicalPath(item.Path))
            .Select(static item => item.Path).Except(before.Entries.Select(static item => item.Path), StringComparer.Ordinal)
            .Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(new[] { DigestionCasStore.Capture(betaAtom.RawBytes.AsSpan()).RelativePath,
            DigestionCasStore.Capture(clausePlan.Children[0].RawBytes.AsSpan()).RelativePath }.Order().ToArray(), newCasPaths);
    }
}
