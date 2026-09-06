using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    [Fact]
    public void IngestRobust_FullScanPreservesNonOrdinalCoverageAndAddsProbe()
    {
        var document = Ledger();
        var alpha = document.RequireDigestionSources()[0];
        var entry = alpha.Entries[0] with
        {
            Coverage =
            [
                new DigestionCoverageEdge("D5/S0/Carrier/Zeta.z", null),
                new DigestionCoverageEdge("D5/S0/Carrier/Alpha.a", null),
            ],
        };
        document = document.WithDigestionSources(
        [
            alpha with { Entries = [entry] },
            document.RequireDigestionSources()[1],
        ]);
        var fixture = Fixture(document);
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            files[AtomPath(entry)] = "# preserve non-canonical coverage order\r\n"
                + files[AtomPath(entry)].Replace("\n", "\r\n", StringComparison.Ordinal);
        }
        fixture.Files[BetaPath] += Addition;
        var before = ExistingLedgerFiles(fixture.Files);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(fixture, temporary).Ingest(Arguments());

        Assert.True(result.Success, result.Error);
        var after = Overlay(temporary, fixture);
        AssertExistingLedgerFilesUnchanged(before, after);
        Assert.Equal(2, BackfillInventoryLoader.Load(Decode(after)).RequireDigestionSources()
            .Single(static source => source.SourceId == "beta").Entries.Length);
        AssertNoObservation(result, entry.AtomId, "alpha", "planned-rewrite");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IngestRobust_ExistingUnchainedParentIsPreservedWithoutChildren_AllAndSource(
        bool sourceScoped)
    {
        var parent = Atom(ClauseText);
        var alpha = Source("alpha", AlphaPath, ClauseText);
        var ledger = TwoSourceLedger(alpha, Source("beta", BetaPath, BetaText));
        var fixture = Fixture(ledger, ClauseText, BetaText);
        var parentPath = AtomPath(Assert.Single(alpha.Entries));
        var beforeBytes = Encoding.UTF8.GetBytes(fixture.Files[parentPath]);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(fixture, temporary).Ingest(
            sourceScoped ? Arguments("alpha") : Arguments());

        Assert.True(result.Success, result.Error);
        var after = Overlay(temporary, fixture);
        var afterSource = BackfillInventoryLoader.Load(Decode(after)).RequireDigestionSources()
            .Single(static source => source.SourceId == "alpha");
        var afterParent = Assert.Single(afterSource.Entries);
        Assert.Equal(parent.Fingerprints.RawSha256["sha256:".Length..], afterParent.AtomId);
        Assert.Empty(afterParent.Receipts.ChainAtoms);
        Assert.Equal(beforeBytes, after.Entries.Single(item => item.Path == parentPath).Bytes.ToArray());
        AssertObservation(result, afterParent.AtomId, "alpha", "planned-rewrite");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IngestRobust_CurrentOnlyCoveredOrReceiptedEntryIsExisting(bool covered)
    {
        var atom = Atom(AlphaText);
        var entry = DigestionTestSupport.Entry(
            atom,
            atom.Fingerprints.RawSha256["sha256:".Length..],
            AtomizerRegistry.GenericId,
            coverageGids: covered ? ["D5/S0/Carrier/Alpha.a"] : [],
            receipts: covered
                ? null
                : new DigestionReceipts([], ["existing receipt"], [], null),
            sourceId: "alpha",
            sourcePath: AlphaPath);
        var current = TwoSourceLedger(
            Source("alpha", AlphaPath, AlphaText) with { Entries = [entry] },
            Source("beta", BetaPath, BetaText));
        var baseline = TwoSourceLedger(
            EmptySource("alpha", AlphaPath),
            Source("beta", BetaPath, BetaText));
        var fixture = RobustFixture(current, baseline);
        var before = ExistingLedgerFiles(fixture.Files);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AtomPath(entry)])).Ingest(Arguments());

        Assert.True(result.Success, result.Error);
        AssertExistingLedgerFilesUnchanged(before, Overlay(temporary, fixture));
        AssertObservation(result, entry.AtomId, "alpha", "current-vs-base-changed");
    }

    [Fact]
    public void IngestRobust_CurrentVsBaseChangesAreObservedWithoutWrites()
    {
        const string gid = "D5/S0/Carrier/Shared.fact";
        var alphaAtom = Atom(AlphaText);
        var betaAtom = Atom(BetaText);
        DigestionLedgerEntry EntryFor(
            DigestionAtom atom,
            string sourceId,
            string sourcePath,
            bool covered) => DigestionTestSupport.Entry(
                atom,
                atom.Fingerprints.RawSha256["sha256:".Length..],
                AtomizerRegistry.GenericId,
                coverageGids: covered ? [gid] : [],
                sourceId: sourceId,
                sourcePath: sourcePath);
        var current = TwoSourceLedger(
            Source("alpha", AlphaPath, AlphaText) with
            {
                Entries = [EntryFor(alphaAtom, "alpha", AlphaPath, covered: false)],
            },
            Source("beta", BetaPath, BetaText) with
            {
                Entries = [EntryFor(betaAtom, "beta", BetaPath, covered: true)],
            });
        var baseline = TwoSourceLedger(
            Source("alpha", AlphaPath, AlphaText) with
            {
                Entries = [EntryFor(alphaAtom, "alpha", AlphaPath, covered: true)],
            },
            Source("beta", BetaPath, BetaText) with
            {
                Entries = [EntryFor(betaAtom, "beta", BetaPath, covered: false)],
            });
        var fixture = RobustFixture(current, baseline);
        var before = ExistingLedgerFiles(fixture.Files);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create(current.RequireDigestionEntries().Select(AtomPath))).Ingest(Arguments());

        Assert.True(result.Success, result.Error);
        AssertExistingLedgerFilesUnchanged(before, Overlay(temporary, fixture));
        AssertObservation(result, current.RequireDigestionSources()[0].Entries[0].AtomId,
            "alpha", "current-vs-base-changed");
        AssertObservation(result, current.RequireDigestionSources()[1].Entries[0].AtomId,
            "beta", "current-vs-base-changed");
    }

    [Fact]
    public void IngestRobust_RemovedBaselineAtomStaysAbsentWhenSourceStillEmitsIt()
    {
        var baseline = TwoSourceLedger(
            Source("alpha", AlphaPath, ClauseText),
            Source("beta", BetaPath, BetaText));
        var current = TwoSourceLedger(
            EmptySource("alpha", AlphaPath),
            baseline.RequireDigestionSources()[1]);
        var removed = Assert.Single(baseline.RequireDigestionSources()[0].Entries);
        var fixture = RobustFixture(current, baseline, ClauseText, BetaText);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AtomPath(removed)])).Ingest(Arguments());

        Assert.True(result.Success, result.Error);
        var after = BackfillInventoryLoader.Load(Decode(Overlay(temporary, fixture)));
        Assert.DoesNotContain(after.RequireDigestionEntries(), entry => entry.AtomId == removed.AtomId);
        AssertObservation(result, removed.AtomId, "alpha", "removed");
    }

    [Fact]
    public void IngestRobust_CoveredDisappearedAndClearedAreObserved()
    {
        var baseline = Ledger();
        var entry = baseline.RequireDigestionSources()[0].Entries[0] with
        {
            Coverage = [new DigestionCoverageEdge("D5/S0/Carrier/Alpha.a", null)],
        };
        var current = baseline.WithDigestionSources(
        [
            baseline.RequireDigestionSources()[0] with { Entries = [entry] },
            baseline.RequireDigestionSources()[1],
        ]);
        var fixture = RobustFixture(current, baseline);
        var before = ExistingLedgerFiles(fixture.Files);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([AtomPath(entry), AlphaPath])).Ingest(Arguments());

        Assert.True(result.Success, result.Error);
        AssertExistingLedgerFilesUnchanged(before, Overlay(temporary, fixture));
        AssertObservation(result, entry.AtomId, "alpha", "current-vs-base-changed");

        var source = current.RequireDigestionSources()[0];
        var disappeared = current.WithDigestionSources(
            [source with { Entries = [] }, current.RequireDigestionSources()[1]]);
        var cleared = current.WithDigestionSources(
            [source with { Entries = [entry with { Coverage = [] }] }, current.RequireDigestionSources()[1]]);
        Assert.Contains(
            IngestPreservedExistingObserver.ObservePlanned(current, disappeared),
            observation => observation.AtomId == entry.AtomId
                && observation.Kind == "covered-disappeared");
        Assert.Contains(
            IngestPreservedExistingObserver.ObservePlanned(current, cleared),
            observation => observation.AtomId == entry.AtomId
                && observation.Kind == "covered-cleared");
        AssertSummaryCountMatchesRows(result);
    }

    [Fact]
    public void IngestRobust_AcknowledgmentAndGenreOnlyDifferencesAreObservedAndMetadataPreserved()
    {
        var baseline = Ledger();
        var alpha = baseline.RequireDigestionSources()[0];
        var atomId = Assert.Single(alpha.Entries).AtomId;
        var current = baseline.WithDigestionSources(
        [
            alpha with
            {
                AcknowledgedStale = [atomId],
                GenreRegistryProjection = GenreRegistryProjection.Available(
                    GenreRegistryCheck.Collected(["unregistered-test-genre"])),
            },
            baseline.RequireDigestionSources()[1],
        ]);
        var fixture = RobustFixture(current, baseline);
        var metadataPath = SourcePrefix("alpha") + "source.toml";
        var metadata = fixture.Files[metadataPath];
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(
            fixture,
            temporary,
            RawChangeSet.Create([metadataPath])).Ingest(Arguments());

        Assert.True(result.Success, result.Error);
        Assert.Equal(metadata, Encoding.UTF8.GetString(Overlay(temporary, fixture).Entries
            .Single(item => item.Path == metadataPath).Bytes.AsSpan()));
        AssertObservation(result, atomId, "alpha", "acknowledged-stale-changed");
        AssertObservation(result, atomId, "alpha", "genre-projection-changed");
    }

    [Fact]
    public void IngestRobust_AllObservationsAreDeterministicAndCountMatchesRows()
    {
        var baseline = Ledger();
        var alpha = baseline.RequireDigestionSources()[0];
        var entry = Assert.Single(alpha.Entries);
        var current = baseline.WithDigestionSources(
        [
            alpha with
            {
                Entries = [entry with { Receipts = entry.Receipts with { UnresolvedSubitems = ["changed"] } }],
                AcknowledgedStale = [entry.AtomId],
            },
            baseline.RequireDigestionSources()[1],
        ]);
        var fixture = RobustFixture(current, baseline);
        string[]? firstRows = null;
        for (var iteration = 0; iteration < 2; iteration++)
        {
            using var temporary = new TemporaryDirectory();
            WriteFixture(temporary, fixture);
            var result = Environment(fixture, temporary).Ingest(Arguments());
            Assert.True(result.Success, result.Error);
            var rows = PreservedRows(result);
            Assert.NotEmpty(rows);
            Assert.Equal(rows.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal), rows);
            AssertSummaryCountMatchesRows(result);
            if (firstRows is null) firstRows = rows;
            else Assert.Equal(firstRows, rows);
        }
    }

    [Fact]
    public void IngestRobust_WriteSet_IsAdditionsOnly()
    {
        var fixture = Fixture();
        fixture.Files[BetaPath] += Addition;
        var before = ExistingLedgerFiles(fixture.Files);
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);

        var result = Environment(fixture, temporary).Ingest(Arguments());

        Assert.True(result.Success, result.Error);
        var after = Overlay(temporary, fixture);
        AssertExistingLedgerFilesUnchanged(before, after);
        var added = after.Entries.Where(item => !fixture.Files.ContainsKey(item.Path)).ToArray();
        Assert.NotEmpty(added);
        Assert.All(added, static item => Assert.True(
            DigestionCasStore.IsCanonicalPath(item.Path)
            || item.Path.Contains("/residual-open/", StringComparison.Ordinal),
            $"unexpected append-only path: {item.Path}"));
    }

    [Fact]
    public void IngestRobust_StillFailsOnUnknownSourceIdCollisionNewCasIntegrityAndWriteSetBound()
    {
        var fixture = Fixture();
        using var unknownRoot = new TemporaryDirectory();
        WriteFixture(unknownRoot, fixture);
        var unknown = Environment(fixture, unknownRoot).Ingest(Arguments("missing-source"));
        Assert.False(unknown.Success);

        const string collidingPath = "docs/develop/theory/ALPHA_.md";
        fixture.Files[collidingPath] = Addition;
        using var collisionRoot = new TemporaryDirectory();
        WriteFixture(collisionRoot, fixture);
        var collision = Environment(fixture, collisionRoot).Ingest(Arguments(collidingPath));
        Assert.False(collision.Success);
        Assert.Contains("collid", collision.Error, StringComparison.Ordinal);

        var atom = Atom(Addition);
        var collidingAtomId = atom.Fingerprints.RawSha256["sha256:".Length..];
        var otherAtom = Atom(BetaText);
        var mismatchedEntry = DigestionTestSupport.Entry(
            otherAtom,
            collidingAtomId,
            AtomizerRegistry.GenericId,
            sourceId: "alpha",
            sourcePath: AlphaPath);
        var mismatched = TwoSourceLedger(
            Source("alpha", AlphaPath, Addition) with { Entries = [mismatchedEntry] },
            Source("beta", BetaPath, BetaText));
        var mismatchFixture = RobustFixture(mismatched, mismatched, Addition, BetaText);
        AddCas(mismatchFixture.Files, otherAtom);
        AddCas(mismatchFixture.Baseline, otherAtom);
        using var atomCollisionRoot = new TemporaryDirectory();
        WriteFixture(atomCollisionRoot, mismatchFixture);
        var atomCollision = Environment(
            mismatchFixture,
            atomCollisionRoot,
            RawChangeSet.Create([AlphaPath])).Ingest(Arguments("alpha"));
        Assert.False(atomCollision.Success);
        Assert.Contains("ingest atom id collision", atomCollision.Error, StringComparison.Ordinal);

        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var tampered = RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText(capture.RelativePath, "tampered bytes"),
        ]);
        var casEntry = DigestionTestSupport.Entry(
            atom,
            atom.Fingerprints.RawSha256["sha256:".Length..],
            AtomizerRegistry.GenericId);
        var casEvaluation = DigestionCasStore.Evaluate(
            DigestionTestSupport.Document(AtomizerRegistry.GenericId, [casEntry]),
            Decode(tampered),
            RawChangeSet.Create([capture.RelativePath]));
        Assert.Contains(casEvaluation.Findings, static finding =>
            finding.Contains("CAS blob hash mismatch", StringComparison.Ordinal));

        var currentRaw = Raw(fixture.Files);
        var currentDocument = BackfillInventoryLoader.Load(Decode(currentRaw));
        var alphaSource = currentDocument.RequireDigestionSources()
            .Single(static source => source.SourceId == "alpha");
        var addedEntry = DigestionTestSupport.Entry(
            atom,
            atom.Fingerprints.RawSha256["sha256:".Length..],
            AtomizerRegistry.GenericId,
            sourceId: "alpha",
            sourcePath: AlphaPath);
        var replacement = currentDocument.WithDigestionSources(
            currentDocument.RequireDigestionSources().Select(source =>
                source.SourceId == "alpha"
                    ? alphaSource with { Entries = alphaSource.Entries.Add(addedEntry) }
                    : source).ToImmutableArray());
        var outside = IngestCommand.ReplaceLedger(currentRaw, currentDocument, replacement);
        Assert.Throws<InvalidOperationException>(() =>
            IngestCommand.LedgerUpdates(currentRaw, outside, BetaOnly));

        var existingPath = AtomPath(Assert.Single(alphaSource.Entries));
        Assert.Throws<InvalidOperationException>(() => IngestCommand.RequireAppendOnlyWriteSet(
            currentRaw,
            currentDocument,
            currentDocument,
            [new IngestCommand.LedgerUpdate(
                existingPath,
                ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("forbidden rewrite")))],
            [],
            ImmutableHashSet<string>.Empty));
    }

    [Fact]
    public void IngestRobust_LeanClosureGuardRetired()
    {
        var fixture = Fixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var environment = Environment(
            fixture,
            temporary,
            RawChangeSet.Create(["D5/S0/Carrier/Ring.lean"]));

        var accepted = environment.Ingest(["--base", "baseline"]);
        var retiredArgument = environment.Ingest(
            ["--base", "baseline", "--report-input-state", "changed"]);

        Assert.True(accepted.Success, accepted.Error);
        Assert.False(retiredArgument.Success);
        Assert.Contains("USAGE:", retiredArgument.Error, StringComparison.Ordinal);
        Assert.DoesNotContain("INGEST_TRUTH_ALIGNMENT_REQUIRED", retiredArgument.Error, StringComparison.Ordinal);
    }
}
