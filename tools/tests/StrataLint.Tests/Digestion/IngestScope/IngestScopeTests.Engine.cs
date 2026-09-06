using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void IngestScope_UnselectedAtomizerNeverCalled_IncludingProjectionPass(
        bool contentKinds, bool unselectedDelta)
    {
        var fixture = Fixture();
        var document = BackfillInventoryLoader.Load(Snapshot(fixture.Files));
        var counts = new Dictionary<string, int>(StringComparer.Ordinal) { ["alpha"] = 0, ["beta"] = 0 };
        TheoryAtomizer atomizer = (bytes, rules) =>
        {
            counts[bytes.SequenceEqual(Encoding.UTF8.GetBytes(AlphaText)) ? "alpha" : "beta"]++;
            return GenericAtomizer.Atomize(bytes, rules);
        };
        TheoryAtomizerWithContentKinds contentAtomizer = (bytes, rules, kinds) =>
        {
            counts[bytes.SequenceEqual(Encoding.UTF8.GetBytes(AlphaText)) ? "alpha" : "beta"]++;
            return GenericAtomizer.AtomizeWithContentKinds(bytes, rules, kinds);
        };
        Func<string, TheoryAtomizer>? resolver = contentKinds ? null : _ => atomizer;
        Func<string, TheoryAtomizerWithContentKinds>? contentResolver = contentKinds ? _ => contentAtomizer : null;
        var changes = RawChangeSet.Create(unselectedDelta ? [AlphaPath] : []);
        var plan = Plan(document, Snapshot(fixture.Files), document, BetaOnly, changes, resolver, contentResolver);
        Assert.Equal(0, counts["alpha"]);
        Assert.Equal(1, counts["beta"]);
        Assert.Same(document.RequireDigestionSources()[0], plan.Document.RequireDigestionSources()[0]);

        var evaluation = DigestionStatusEvaluator.EvaluateUncovered(
            DigestionEvaluationScope.FullScan, plan.Document, Snapshot(fixture.Files), document,
            sourceIds: BetaOnly, changes: changes, atomizerResolver: resolver,
            contentKindAtomizerResolver: contentResolver);
        Assert.Empty(evaluation.Findings);
        Assert.Equal(0, counts["alpha"]);
        Assert.Equal(2, counts["beta"]);
        Assert.All(evaluation.Entries, static item => Assert.Equal("beta", item.Entry.SourceId));
    }

    [Theory]
    [InlineData("conflict-marker")]
    [InlineData("content-wide-replacement")]
    public void IngestScope_UnselectedPrepassesSkipped(string prepass)
    {
        var fixture = Fixture();
        var baseline = Ledger();
        var current = baseline;
        string witness;
        if (prepass == "conflict-marker")
        {
            fixture.Files[AlphaPath] += "<<<<<<< unresolved\n";
            witness = DigestionSourceConflictMarkers.DiagnosticCode;
        }
        else
        {
            var alpha = baseline.RequireDigestionSources()[0];
            fixture.Files[AlphaPath] = "# Header\n\n" + AlphaText;
            var bytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(fixture.Files[AlphaPath]));
            var opaque = DigestionAtom.FromFrozenCas(bytes, DigestionFingerprint.ComputeOpaque(bytes.AsSpan()));
            var old = DigestionTestSupport.Entry(opaque, opaque.Fingerprints.RawSha256[7..],
                AtomizerRegistry.NoAtomizerId, sourceId: "alpha", sourcePath: AlphaPath);
            baseline = baseline.WithDigestionSources([
                alpha with { Atomizer = AtomizerRegistry.NoAtomizerId, Entries = [old] },
                baseline.RequireDigestionSources()[1],
            ]);
            current = current.WithDigestionSources([alpha with { Entries = [old with
            {
                Atomizer = AtomizerRegistry.GenericId,
                Fingerprints = old.Fingerprints with { NormalizedSha256 = "sha256:" + new string('f', 64) },
            }] }, current.RequireDigestionSources()[1]]);
            witness = "content-wide replacement receipt identity changed or disappeared";
            fixture.Files.Remove(DigestionCasStore.Capture(Atom(AlphaText).RawBytes.AsSpan()).RelativePath);
            AddCas(fixture.Files, opaque);
        }
        fixture.Files[BetaPath] += Addition;
        var snapshot = Snapshot(fixture.Files);
        var plan = Plan(current, snapshot, baseline, BetaOnly, RawChangeSet.Create([AlphaPath, BetaPath]));
        Assert.Equal(1, plan.ResidualOpenAdded);
        Assert.Empty(plan.Alignment.Findings);
        Assert.Same(current.RequireDigestionSources()[0], plan.Document.RequireDigestionSources()[0]);
        var error = Assert.Throws<FormatException>(() => Plan(current, snapshot, baseline,
            ImmutableHashSet.Create(StringComparer.Ordinal, "alpha")));
        Assert.Contains(witness, error.Message, StringComparison.Ordinal);

        if (prepass == "conflict-marker")
        {
            using var temporary = new TemporaryDirectory();
            WriteFixture(temporary, fixture);
            var result = Environment(fixture, temporary).Ingest(Arguments("beta"));
            Assert.True(result.Success, result.Error);
        }
    }

    [Fact]
    public void IngestScope_UnselectedUnchainedClauseParentNotMaterialized_SelectedIs()
    {
        const string alphaText = "## Claim 10\n\n- Alpha first.\n- Alpha second.\n";
        const string betaText = "## Claim 20\n\n- Beta first.\n- Beta second.\n";
        var document = BackfillInventoryDocument.Create([
            Source("alpha", AlphaPath, alphaText), Source("beta", BetaPath, betaText),
        ], []);
        var fixture = Fixture(document, alphaText, betaText);
        var plan = Plan(document, Snapshot(fixture.Files), document, BetaOnly);
        var alpha = plan.Document.RequireDigestionSources()[0];
        var beta = plan.Document.RequireDigestionSources()[1];
        Assert.Same(document.RequireDigestionSources()[0], alpha);
        Assert.Empty(Assert.Single(alpha.Entries).Receipts.ChainAtoms);
        Assert.Equal(3, beta.Entries.Length);
        Assert.Equal(2, beta.Entries.Single(entry => entry.AtomId == Atom(betaText).Fingerprints.RawSha256[7..])
            .Receipts.ChainAtoms.Length);
        Assert.Equal(2, plan.CasObjects.Length);
        Assert.All(plan.Alignment.ClausePlans, static item => Assert.Equal("beta", item.SourceId));
    }

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
