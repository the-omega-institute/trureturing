using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    [Theory]
    [InlineData("beta")]
    [InlineData("alpha")]
    [InlineData("all")]
    public void IngestScope_ConflictMarkerPrepassRespectsSelectedSource_ProductionPath(string selector)
    {
        var fixture = Fixture();
        fixture.Files[AlphaPath] += "<<<<<<< HEAD\nconflicted text\n=======\nother text\n>>>>>>> incoming\n";
        fixture.Files[BetaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(fixture, temporary).Ingest(
            selector == "all" ? Arguments() : Arguments(selector));

        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        if (selector == "beta")
        {
            Assert.True(result.Success, result.Error);
            Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));
            var beforePaths = before.Entries.Select(static entry => entry.Path).ToHashSet(StringComparer.Ordinal);
            Assert.Equal(Image(before), Image(RawRepositorySnapshot.Create(
                after.Entries.Where(entry => beforePaths.Contains(entry.Path)))));
            var addedId = Atom(Addition).Fingerprints.RawSha256["sha256:".Length..];
            Assert.Equal(new[]
            {
                DigestionCasStore.RootPath + addedId,
                SourcePrefix("beta") + "residual-open/" + addedId + ".yaml",
            }.Order(StringComparer.Ordinal), after.Entries
                .Where(entry => !beforePaths.Contains(entry.Path)).Select(static entry => entry.Path)
                .Order(StringComparer.Ordinal));
        }
        else
        {
            Assert.False(result.Success);
            Assert.Contains("INGEST-CONFLICT-MARKER-001", result.Error, StringComparison.Ordinal);
            Assert.Contains(AlphaPath + ":5", result.Error, StringComparison.Ordinal);
            Assert.Equal(Image(before), Image(after));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Ingest_UnselectedSourceAtomizerNeverCalledInAnyPass(bool contentKinds)
    {
        var document = Ledger();
        var fixture = RobustFixture(document, document);
        fixture.Files[BetaPath] += Addition;
        var calls = new Dictionary<string, int>(StringComparer.Ordinal)
        {
            ["alpha"] = 0,
            ["beta"] = 0,
        };
        string SourceFor(ReadOnlySpan<byte> bytes) =>
            bytes.SequenceEqual(Encoding.UTF8.GetBytes(AlphaText)) ? "alpha" : "beta";
        TheoryAtomizer atomizer = (bytes, rules) =>
        {
            calls[SourceFor(bytes)]++;
            return GenericAtomizer.Atomize(bytes, rules);
        };
        TheoryAtomizerWithContentKinds contentAtomizer = (bytes, rules, kinds) =>
        {
            calls[SourceFor(bytes)]++;
            return GenericAtomizer.AtomizeWithContentKinds(bytes, rules, kinds);
        };
        var dependencies = contentKinds
            ? new ReportFreeIngestDependencies(
                ContentKindAtomizerResolver: _ => contentAtomizer)
            : new ReportFreeIngestDependencies(AtomizerResolver: _ => atomizer);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath, BetaPath]),
            dependencies).Ingest(Arguments("beta"));

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, calls["alpha"]);
        Assert.Equal(1, calls["beta"]);
    }

    [Fact]
    public void IngestScope_UnselectedContentWideReplacementPrepassSkipped_ProductionPath()
    {
        var original = Ledger();
        var alpha = original.RequireDigestionSources()[0];
        var alphaText = "# Header\n\n" + AlphaText;
        var bytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(alphaText));
        var opaque = DigestionAtom.FromFrozenCas(
            bytes,
            DigestionFingerprint.ComputeOpaque(bytes.AsSpan()));
        var old = DigestionTestSupport.Entry(
            opaque,
            opaque.Fingerprints.RawSha256["sha256:".Length..],
            AtomizerRegistry.NoAtomizerId,
            sourceId: "alpha",
            sourcePath: AlphaPath);
        var baseline = original.WithDigestionSources(
        [
            alpha with { Atomizer = AtomizerRegistry.NoAtomizerId, Entries = [old] },
            original.RequireDigestionSources()[1],
        ]);
        var current = original.WithDigestionSources(
        [
            alpha with
            {
                Entries =
                [
                    old with
                    {
                        Atomizer = AtomizerRegistry.GenericId,
                        Fingerprints = old.Fingerprints with
                        {
                            NormalizedSha256 = "sha256:" + new string('f', 64),
                        },
                    },
                ],
            },
            original.RequireDigestionSources()[1],
        ]);
        var fixture = RobustFixture(current, baseline, alphaText, BetaText);
        AddCas(fixture.Files, opaque);
        AddCas(fixture.Baseline, opaque);
        fixture.Files[BetaPath] += Addition;
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath, BetaPath])).Ingest(Arguments("beta"));

        Assert.True(result.Success, result.Error);
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));
    }

    [Fact]
    public void IngestScope_UnselectedUnchainedClauseParentNotMaterialized_SelectedIs_ProductionPath()
    {
        const string alphaText = "## Claim 10\n\n- Alpha first.\n- Alpha second.\n";
        const string betaText = "## Claim 20\n\n- Beta first.\n- Beta second.\n";
        var alpha = Source("alpha", AlphaPath, alphaText);
        var document = TwoSourceLedger(
            alpha,
            Source("beta", BetaPath, betaText, populated: false));
        var fixture = RobustFixture(document, document, alphaText, betaText);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var before = DirectoryLedgerTestSupport.ReadRepository(temporary);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath, BetaPath])).Ingest(Arguments("beta"));

        Assert.True(result.Success, result.Error);
        var after = DirectoryLedgerTestSupport.ReadRepository(temporary);
        Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));
        var sources = BackfillInventoryLoader.Load(Decode(after)).RequireDigestionSources();
        var afterAlpha = sources.Single(static source => source.SourceId == "alpha");
        var afterBeta = sources.Single(static source => source.SourceId == "beta");
        Assert.Empty(Assert.Single(afterAlpha.Entries).Receipts.ChainAtoms);
        var betaParentId = Atom(betaText).Fingerprints.RawSha256["sha256:".Length..];
        var betaParent = Assert.Single(afterBeta.Entries, entry => entry.AtomId == betaParentId);
        Assert.Equal(2, betaParent.Receipts.ChainAtoms.Length);
        Assert.Equal(3, afterBeta.Entries.Length);
    }
}
