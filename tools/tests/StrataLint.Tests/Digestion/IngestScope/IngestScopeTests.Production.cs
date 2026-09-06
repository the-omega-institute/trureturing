using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    public static IEnumerable<object[]> ProductionClassificationCases()
    {
        foreach (var branch in new[] { "current", "planned" })
        foreach (var selection in new[] { "beta", "alpha", "all" })
            yield return [branch, selection];
    }

    [Fact]
    public void IngestScope_UnselectedAtomizerNeverCalled_IncludingProjectionPass_ProductionPath()
    {
        var document = TwoSourceLedger(
            EmptySource("alpha", AlphaPath) with { Atomizer = AtomizerRegistry.WmId },
            Source("beta", BetaPath, BetaText));
        var fixture = RobustFixture(document, document);
        fixture.Files[BetaPath] += Addition;
        var before = Raw(fixture.Files);
        using var unselectedRoot = new TemporaryDirectory();
        WriteFixture(unselectedRoot, fixture);

        var unselected = Environment(
            fixture,
            unselectedRoot,
            RawChangeSet.Create([AlphaPath, BetaPath])).Ingest(Arguments("beta"));

        Assert.True(unselected.Success, unselected.Error);
        Assert.DoesNotContain("INGEST_FALLBACK source=alpha", unselected.Output, StringComparison.Ordinal);
        var after = Overlay(unselectedRoot, fixture);
        Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));

        using var selectedRoot = new TemporaryDirectory();
        WriteFixture(selectedRoot, fixture);
        var selected = Environment(
            fixture,
            selectedRoot,
            RawChangeSet.Create([AlphaPath])).Ingest(Arguments("alpha"));
        Assert.True(selected.Success, selected.Error);
        Assert.Contains("INGEST_FALLBACK source=alpha", selected.Output, StringComparison.Ordinal);
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
        var before = Raw(fixture.Files);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath, BetaPath])).Ingest(Arguments("beta"));

        Assert.True(result.Success, result.Error);
        var after = Overlay(temporary, fixture);
        Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));
        Assert.DoesNotContain(PreservedRows(result), static row =>
            row.Contains(" source=alpha ", StringComparison.Ordinal));
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
        var before = Raw(fixture.Files);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AlphaPath, BetaPath])).Ingest(Arguments("beta"));

        Assert.True(result.Success, result.Error);
        var after = Overlay(temporary, fixture);
        Assert.Equal(Image(before, SourcePrefix("alpha")), Image(after, SourcePrefix("alpha")));
        var sources = BackfillInventoryLoader.Load(Decode(after)).RequireDigestionSources();
        var afterAlpha = sources.Single(static source => source.SourceId == "alpha");
        var afterBeta = sources.Single(static source => source.SourceId == "beta");
        Assert.Empty(Assert.Single(afterAlpha.Entries).Receipts.ChainAtoms);
        var betaParentId = Atom(betaText).Fingerprints.RawSha256["sha256:".Length..];
        var betaParent = Assert.Single(afterBeta.Entries, entry => entry.AtomId == betaParentId);
        Assert.Equal(2, betaParent.Receipts.ChainAtoms.Length);
        Assert.Equal(3, afterBeta.Entries.Length);
        AssertNoObservation(result, Assert.Single(alpha.Entries).AtomId, "alpha", "planned-rewrite");
    }

    [Theory]
    [MemberData(nameof(ProductionClassificationCases))]
    public void IngestScope_ClassifierRespectsSelection_CurrentAndPlanned(
        string branch,
        string selection)
    {
        RuleFixture fixture;
        RawChangeSet changes;
        string atomId;
        string expectedKind;
        if (branch == "current")
        {
            var baseline = Ledger();
            var alpha = baseline.RequireDigestionSources()[0];
            var entry = Assert.Single(alpha.Entries);
            var changed = entry with
            {
                Receipts = entry.Receipts with { UnresolvedSubitems = ["obligation"] },
            };
            var current = baseline.WithDigestionSources(
            [
                alpha with { Entries = [changed] },
                baseline.RequireDigestionSources()[1],
            ]);
            fixture = RobustFixture(current, baseline);
            changes = RawChangeSet.Create([AtomPath(changed)]);
            atomId = changed.AtomId;
            expectedKind = "current-vs-base-changed";
        }
        else if (branch == "planned")
        {
            var alpha = Source("alpha", AlphaPath, ClauseText);
            var document = TwoSourceLedger(alpha, Source("beta", BetaPath, BetaText));
            fixture = RobustFixture(document, document, ClauseText, BetaText);
            changes = RawChangeSet.Create([AlphaPath]);
            atomId = Assert.Single(alpha.Entries).AtomId;
            expectedKind = "planned-rewrite";
        }
        else
        {
            throw new ArgumentOutOfRangeException(nameof(branch));
        }

        var before = ExistingLedgerFiles(fixture.Files);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var arguments = selection == "all" ? Arguments() : Arguments(selection);

        var result = Environment(fixture, temporary, changes).Ingest(arguments);

        Assert.True(result.Success, result.Error);
        AssertExistingLedgerFilesUnchanged(before, Overlay(temporary, fixture));
        if (selection == "beta")
            AssertNoObservation(result, atomId, "alpha", expectedKind);
        else
            AssertObservation(result, atomId, "alpha", expectedKind);
    }
}
