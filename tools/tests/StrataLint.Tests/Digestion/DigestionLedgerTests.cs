using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void CasBackedLegacyBoundaryDoesNotContributeSourceOrBoundaryGaps()
    {
        var source = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(source, DigestionTestSupport.Rules).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var document = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Open);
        var snapshot = Snapshot((captured.RelativePath, captured.Bytes.ToArray()));

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, status.Alignment);
        Assert.DoesNotContain(status.Gaps, static gap => gap.Code == "source-missing");
    }

    [Fact]
    public void CasBackedNoAtomizerEntryIsSeenWithoutReplayingItsSpecificationSource()
    {
        var source = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var atom = new DigestionAtom(
            0,
            source.Length,
            ImmutableArray.CreateRange(source),
            DigestionFingerprint.Compute(source),
            ImmutableArray<DigestionContext>.Empty);
        var captured = DigestionCasStore.Capture(source);
        var document = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Open,
            atomizer: AtomizerRegistry.NoAtomizerId);
        var snapshot = Snapshot((captured.RelativePath, captured.Bytes.ToArray()));

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, status.Alignment);
        Assert.DoesNotContain(status.Gaps, static gap => gap.Code == "source-missing");
    }

    [Fact]
    public void IngestRejectsACasBackedNoAtomizerBoundaryWithoutItsCasBlob()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var atom = new DigestionAtom(
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            ImmutableArray<DigestionContext>.Empty);
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Open,
            atomizer: AtomizerRegistry.NoAtomizerId);

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes)),
            ledger));

        Assert.Contains("CAS blob is missing", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestKeepsCasBackedNoAtomizerEntryByteIdempotent()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var atom = new DigestionAtom(
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            ImmutableArray<DigestionContext>.Empty);
        var ledger = Ledger(
            atom,
            DigestionMigrationState.Partial,
            DigestionTruthState.Open,
            atomizer: AtomizerRegistry.NoAtomizerId);

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes), CasFile(atom)),
            ledger);
        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        var migrated = first.Document;

        var migratedEntry = Assert.Single(migrated.RequireDigestionEntries());
        Assert.Equal(atom.Fingerprints.RawSha256, migratedEntry.CasRef);
        Assert.Empty(first.CasObjects);

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(
                ("docs/source.md", sourceBytes),
                CasFile(atom)),
            ledger);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes, secondBytes);
    }

    [Fact]
    public void IngestDoesNotReclassifyAnOpenGenreWhenRawShaDiffers()
    {
        var originalBytes = Encoding.UTF8.GetBytes(
            "## 未登记体 40.2\n\nopen。\n");
        var changedBytes = Encoding.UTF8.GetBytes(
            "## 定理 40.2\n\nchanged。\n");
        var originalAtom = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            originalBytes,
            TheoryAtomizerRules.None).Claims);
        var changedAtom = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            changedBytes,
            TheoryAtomizerRules.None).Claims);
        var originalId = originalAtom.Fingerprints.RawSha256["sha256:".Length..];
        var changedId = changedAtom.Fingerprints.RawSha256["sha256:".Length..];
        var originalEntry = Entry(
            originalAtom,
            originalId,
            AtomizerRegistry.GenericId);
        var baseline = Document(AtomizerRegistry.GenericId, [originalEntry]);
        var originalCapture = DigestionCasStore.Capture(originalAtom.RawBytes.AsSpan());

        var plan = DigestionIngestor.Plan(
            baseline,
            Snapshot(
                ("docs/source.md", changedBytes),
                (originalCapture.RelativePath, originalCapture.Bytes.ToArray())),
            baseline);
        var entries = Assert.Single(plan.Document.RequireDigestionSources()).Entries;
        var currentKinds = AtomizerRegistry.ResolveContentKinds(
            AtomizerRegistry.GenericId,
            changedBytes,
            TheoryAtomizerRules.None);

        Assert.NotEqual(originalId, changedId);
        var preserved = Assert.Single(entries, entry => entry.AtomId == originalId);
        Assert.Equal(originalEntry.SourceId, preserved.SourceId);
        Assert.Equal(originalEntry.SourcePath, preserved.SourcePath);
        Assert.Equal(originalEntry.Atomizer, preserved.Atomizer);
        Assert.Equal(originalEntry.Fingerprints, preserved.Fingerprints);
        Assert.Equal(originalEntry.ProjectedStatus, preserved.ProjectedStatus);
        Assert.Equal(originalEntry.CasRef, preserved.CasRef);
        Assert.Empty(preserved.CoverageGids);
        Assert.Empty(preserved.Coverage);
        Assert.Empty(preserved.Receipts.Scribe);
        Assert.Empty(preserved.Receipts.UnresolvedSubitems);
        Assert.Empty(preserved.Receipts.ChainAtoms);
        Assert.Null(preserved.Receipts.TailAuthorization);
        Assert.Null(preserved.Receipts.Quarantine);
        Assert.Null(preserved.Receipts.CoverDisposition);
        Assert.Contains(entries, entry => entry.AtomId == changedId);
        Assert.False(currentKinds.ContainsKey(originalAtom.Fingerprints.RawSha256));
        Assert.Equal("定理", currentKinds[changedAtom.Fingerprints.RawSha256]);
        Assert.Equal(1, plan.ResidualOpenAdded);
    }

    [Fact]
    public void IngestOnboardsRegisteredEmptySourceAndRemainsByteIdempotent()
    {
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。first。\n\n**定理 1.2(B)**。second。\n");
        var atoms = AtomizerRegistry.Atomize(atomizerId, sourceBytes, DigestionTestSupport.Rules).Claims;
        var ledger = EmptyDocument(atomizerId);

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", sourceBytes)),
            ledger);
        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        var migrated = first.Document;
        var entries = Assert.Single(first.Document.RequireDigestionSources()).Entries;

        Assert.Equal(atoms.Length, first.ResidualOpenAdded);
        Assert.Equal(atoms.Length, entries.Length);
        Assert.Equal(atoms.Length, first.CasObjects.Length);
        Assert.Empty(first.Fallbacks);
        Assert.All(entries, static entry =>
        {
            Assert.Equal(entry.Fingerprints.RawSha256, entry.CasRef);
            Assert.Empty(entry.CoverageGids);
            Assert.Empty(entry.Coverage);
            Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
        });
        Assert.All(first.CasObjects, item => Assert.Contains(
            atoms,
            atom => atom.Fingerprints.RawSha256 == item.Reference
                && atom.RawBytes.AsSpan().SequenceEqual(item.Bytes.AsSpan())));

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, first.CasObjects),
            ledger);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes, secondBytes);
    }

    [Fact]
    public void UnchangedSingleClauseLedgerReplayRemainsByteIdentical()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。single clause。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var document = StructuralLedger(atom);
        var expected = DirectoryLedgerTestSupport.Image(document);

        var replay = DigestionIngestor.Plan(
            document,
            Snapshot(("docs/source.md", sourceBytes), CasFile(atom)),
            document);

        Assert.Equal(0, replay.ResidualOpenAdded);
        Assert.Empty(replay.CasObjects);
        Assert.Equal(expected, DirectoryLedgerTestSupport.Image(replay.Document));
    }

    [Fact]
    public void DanglingChainIdRetainsChainMigrationIncompleteGap()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。single clause。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var document = StructuralLedger(atom);
        var source = Assert.Single(document.RequireDigestionSources());
        var entry = Assert.Single(source.Entries);
        document = document.WithDigestionSources(
        [
            source with
            {
                Entries = [entry with { Receipts = entry.Receipts with { ChainAtoms = ["missing-child"] } }],
            },
        ]);

        var status = Assert.Single(DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            Snapshot(("docs/source.md", sourceBytes), CasFile(atom)),
            AcceptedLean(Array.Empty<string>()),
            baselineDocument: document).Entries);

        Assert.Contains(status.Gaps, gap =>
            gap.Code == "chain-migration-incomplete" && gap.Detail == "missing-child");
        Assert.False(status.Deletable);
    }

    [Fact]
    public void DerivedChainAbsorptionReachesFixedPointAcrossThreeLevels()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual fixed-point receipt\n");
        var atom = new DigestionAtom(
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            ImmutableArray<DigestionContext>.Empty);
        const string gid = "D5/S0/Carrier/Probe";
        const string targetPath = "D5/S0/Carrier/Probe.lean";
        var target = Encoding.UTF8.GetBytes(Lean(gid));
        var definition = Encoding.UTF8.GetBytes("scribe definition\n");
        var emission = Encoding.UTF8.GetBytes("# emitted narrative\n");
        var definitionHash = DigestionFingerprint.Compute(definition).RawSha256;
        var emissionHash = DigestionFingerprint.Compute(emission).RawSha256;
        var template = Ledger(
            atom,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            gid,
            new DigestionCoverageEdge(
                gid,
                TestModuleStatementId),
            new DigestionScribeReceipt(gid, definitionHash, emissionHash),
            atomizer: AtomizerRegistry.NoAtomizerId);
        var source = Assert.Single(template.RequireDigestionSources());
        var entry = Assert.Single(source.Entries);
        var chained = template.WithDigestionSources(
        [
            source with
            {
                Entries =
                [
                    entry with
                    {
                        AtomId = "chain-parent",
                        Receipts = entry.Receipts with { ChainAtoms = ["chain-middle"] },
                    },
                    entry with
                    {
                        AtomId = "chain-middle",
                        Receipts = entry.Receipts with { ChainAtoms = ["chain-leaf"] },
                    },
                    entry with { AtomId = "chain-leaf" },
                ],
            },
        ]);
        var record = new ScribeEmissionRecord(
            gid,
            ScribeEmissionAttestation.DefinitionPath(gid),
            definitionHash,
            ScribeEmissionAttestation.EmissionPath(gid),
            emissionHash);
        var rawEntries = new List<RawRepositoryEntry>
        {
            new("docs/source.md", ImmutableArray.CreateRange(sourceBytes)),
            new(CasFile(atom).Path, ImmutableArray.CreateRange(CasFile(atom).Bytes)),
            new(targetPath, ImmutableArray.CreateRange(target)),
            new(record.DefinitionPath, ImmutableArray.CreateRange(definition)),
            new(record.EmissionPath, ImmutableArray.CreateRange(emission)),
        };
        rawEntries.AddRange(FrozenLedgerFiles(targetPath, "probe").Select(static file =>
            new RawRepositoryEntry(file.Path, ImmutableArray.CreateRange(file.Bytes))));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(rawEntries))).Snapshot;

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            chained,
            snapshot,
            AcceptedLean(targetPath),
            VerifiedScribeEmissions.Create([record]),
            baselineDocument: chained);

        Assert.Equal(3, evaluation.Entries.Length);
        Assert.DoesNotContain(
            evaluation.Entries.SelectMany(static item => item.Gaps),
            static gap => gap.Code == "coverage-target-mismatch");
        Assert.All(evaluation.Entries, static item => Assert.Equal(
            DigestionMigrationState.Absorbed,
            item.DerivedStatus.Migration));
        Assert.DoesNotContain(evaluation.Entries.SelectMany(static item => item.Gaps), static gap =>
            gap.Code == "chain-migration-incomplete");
    }

    [Fact]
    public void IngestOnboardsRegisteredEmptySourceWithCoarseFallback()
    {
        const string sourcePath = "docs/develop/theory/non-utf8.bin";
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var sourceBytes = new byte[] { 0xff, 0x00, 0xfe };
        var ledger = Document(
            atomizerId,
            [],
            sourcePath: sourcePath,
            genreRegistryCheck: GenreRegistryCheck.Collected([]));

        var first = DigestionIngestor.Plan(
            ledger,
            Snapshot((sourcePath, sourceBytes)),
            ledger);
        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        var migrated = first.Document;

        var fallback = Assert.Single(first.Fallbacks);
        Assert.Equal("source", fallback.SourceId);
        Assert.Contains("Unicode", fallback.Reason, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(1, first.ResidualOpenAdded);
        var coarse = Assert.Single(first.Document.RequireDigestionEntries());
        Assert.Equal(DigestionFingerprint.ComputeOpaque(sourceBytes), coarse.Fingerprints);
        Assert.Equal(DigestionMigrationState.Residual, coarse.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, coarse.ProjectedStatus.Truth);
        var captured = Assert.Single(first.CasObjects);
        Assert.Equal(coarse.Fingerprints.RawSha256, coarse.CasRef);
        Assert.Equal(sourceBytes, captured.Bytes.ToArray());

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(first.CasObjects
                .Select(static item => (item.RelativePath, item.Bytes.ToArray()))
                .Prepend((sourcePath, sourceBytes))
                .ToArray()),
            ledger);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes, secondBytes);
    }
}
