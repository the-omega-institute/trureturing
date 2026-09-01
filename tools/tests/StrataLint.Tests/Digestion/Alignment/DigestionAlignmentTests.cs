using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void IngestFallsBackToOneWholeSourceAtomWhenBaselineHasNoEntries()
    {
        const string theoryPath = "docs/develop/theory/non-utf8.bin";
        var ledger = LedgerForPath(theoryPath, []);
        var opaqueBytes = new byte[] { 0xff, 0x00, 0xfe };
        var snapshot = Snapshot(opaqueBytes, sourcePath: theoryPath);

        var alignment = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Ingest);

        var plan = DigestionIngestor.Plan(
            ledger,
            snapshot,
            ledger);

        Assert.Empty(alignment.Findings);
        var fallback = Assert.Single(plan.Fallbacks);
        Assert.Equal("source", fallback.SourceId);
        Assert.Contains("Unicode", fallback.Reason, StringComparison.OrdinalIgnoreCase);
        var coarse = Assert.Single(plan.Document.RequireDigestionEntries());
        var captured = Assert.Single(plan.CasObjects);
        Assert.Equal(captured.Reference, coarse.CasRef);
        Assert.Equal(captured.Reference, coarse.Fingerprints.RawSha256);
        Assert.Equal(opaqueBytes, captured.Bytes.ToArray());

        var firstBytes = DirectoryLedgerTestSupport.Image(plan.Document);
        var migrated = plan.Document;
        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(
                opaqueBytes,
                plan.CasObjects,
                theoryPath),
            ledger);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Single(second.Fallbacks);
        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes, secondBytes);
    }

    [Fact]
    public void IngestDoesNotFallbackForInternalAtomizerFormatFailures()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var ledger = Ledger(
            [],
            CasEntry("old-receipt", oldAtom, oldCapture.Reference));

        var exception = Assert.Throws<FormatException>(() => DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(Encoding.UTF8.GetBytes("source"), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => throw new FormatException("invalid Markdown AST span")));

        Assert.Contains("invalid Markdown AST span", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRefusesStructuralCoarseFallbackWhenBaselineHasFineReceipt()
    {
        const string theoryPath = "docs/develop/theory/non-utf8.bin";
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var ledger = LedgerForPath(
                theoryPath,
                [],
                CasEntry("old-receipt", oldAtom, oldCapture.Reference));
        var opaqueBytes = new byte[] { 0xff, 0x00, 0xfe };
        var snapshot = Snapshot(opaqueBytes, [oldCapture], theoryPath);

        var alignment = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Ingest);

        var finding = Assert.Single(alignment.Findings);
        Assert.Contains("source source", finding, StringComparison.Ordinal);
        Assert.Contains("Unicode", finding, StringComparison.OrdinalIgnoreCase);
        Assert.Empty(alignment.Fallbacks);
        Assert.Empty(alignment.Residual);

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            ledger,
            snapshot,
            ledger));
        Assert.Contains(finding, exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestAllowsFallbackWhenBaselineContainsOnlyCoarseEntries()
    {
        var opaqueBytes = Encoding.UTF8.GetBytes("not a recognised claim\n");
        var coarseBytes = ImmutableArray.CreateRange(opaqueBytes);
        var coarse = new DigestionAtom(
            0,
            opaqueBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var captured = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var ledger = Ledger(
            [],
            CasEntry("coarse-receipt", coarse, captured.Reference));
        var snapshot = Snapshot(opaqueBytes, [captured]);

        var alignment = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Ingest);
        var first = DigestionIngestor.Plan(ledger, snapshot, ledger);

        Assert.Empty(alignment.Findings);
        Assert.Single(alignment.Fallbacks);
        Assert.Empty(alignment.Residual);
        Assert.Single(first.Fallbacks);
        Assert.Equal(0, first.ResidualOpenAdded);
        Assert.Empty(first.CasObjects);
    }

    [Fact]
    public void IngestCapturesSeenAndResidualAtomBytesAndRemainsByteIdempotent()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。seen。\n\n**定理 1.2(B)**。new。\n");
        var atoms = GictAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules).Claims;
        var seenCapture = DigestionCasStore.Capture(atoms[0].RawBytes.AsSpan());
        var ledger = Ledger([], Entry("seen-receipt", atoms[0]));

        var first = DigestionIngestor.Plan(ledger, Snapshot(sourceBytes, [seenCapture]), ledger);
        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        var migrated = first.Document;

        Assert.Equal(1, first.ResidualOpenAdded);
        Assert.Single(first.CasObjects);
        Assert.All(first.Document.RequireDigestionEntries(), static entry =>
        {
            Assert.NotNull(entry.CasRef);
            Assert.Equal(entry.Fingerprints.RawSha256, entry.CasRef);
        });
        Assert.All(first.CasObjects, item => Assert.Contains(
            atoms,
            atom => atom.Fingerprints.RawSha256 == item.Reference
                && atom.RawBytes.AsSpan().SequenceEqual(item.Bytes.AsSpan())));

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, first.CasObjects.Prepend(seenCapture)),
            ledger);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes, secondBytes);
    }

    [Fact]
    public void IngestUsesBareContentHashesForExistingAndNewAtoms()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。seen。\n\n**定理 1.2(B)**。new。\n");
        var atoms = GictAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules).Claims;
        var seenCapture = DigestionCasStore.Capture(atoms[0].RawBytes.AsSpan());
        var ledger = Ledger([], Entry("seen-receipt", atoms[0]));

        var plan = DigestionIngestor.Plan(ledger, Snapshot(sourceBytes, [seenCapture]), ledger);

        Assert.Equal(
            atoms.Select(AtomId).Order(StringComparer.Ordinal),
            plan.Document.RequireDigestionEntries()
                .Select(static entry => entry.AtomId)
                .Order(StringComparer.Ordinal));
    }

    [Fact]
    public void CasBackedReceiptDoesNotRequireSourceReconciliation()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var ledger = Ledger(
            [],
            CasEntry("cas-receipt", atom, captured.Reference));
        var raw = RawRepositorySnapshot.Create(
        [
            new RawRepositoryEntry(captured.RelativePath, captured.Bytes),
            new RawRepositoryEntry(
                TheoryAtomizerDataLoader.DataPath,
                ImmutableArray.CreateRange(DigestionTestSupport.RulesBytes)),
        ]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Admission);

        Assert.Empty(result.Findings);
        Assert.Empty(result.Residual);
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(AtomId(atom)));
    }

    [Fact]
    public void IngestCollapsesByteIdenticalOccurrencesToOneContentEntry()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var ledger = Ledger(
            [],
            CasEntry("old-receipt", oldAtom, oldCapture.Reference));
        var duplicateBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\n| κ | 1 |\n");

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(duplicateBytes, [oldCapture]),
            ledger);

        var added = plan.Document.RequireDigestionEntries()
            .Where(entry => entry.AtomId != AtomId(oldAtom))
            .ToArray();
        var entry = Assert.Single(added);
        Assert.Equal(entry.Fingerprints.RawSha256["sha256:".Length..], entry.AtomId);
        Assert.Equal(entry.Fingerprints.RawSha256, entry.CasRef);
        Assert.Single(plan.CasObjects);
    }

    [Fact]
    public void CasBackedAdmissionDoesNotReatomizeReceiptsWhenInputsMatchBaseline()
    {
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。raw。\n\n**定理 1.2(B)**。normalized。\n");
        var normalizedBytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n**定理 1.1(A)**。raw。\r\n\r\n**定理 1.2(B)**。normalized。\r\n");
        var current = GictAtomizer.Atomize(currentBytes, DigestionTestSupport.Rules);
        var normalized = GictAtomizer.Atomize(normalizedBytes, DigestionTestSupport.Rules);
        var rawCapture = DigestionCasStore.Capture(current.Claims[0].RawBytes.AsSpan());
        var normalizedCapture = DigestionCasStore.Capture(normalized.Claims[1].RawBytes.AsSpan());
        var ledger = Ledger(
            [],
            Entry("raw-receipt", current.Claims[0]),
            Entry("normalized-receipt", normalized.Claims[1]));
        var snapshot = Snapshot(currentBytes, [rawCapture, normalizedCapture]);
        var calls = 0;
        TheoryAtomizer atomizer = (bytes, _) =>
        {
            calls++;
            return GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        };
        var first = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Admission,
            _ => atomizer,
            baselineSnapshot: snapshot);

        Assert.Empty(first.Findings);
        Assert.Empty(first.Residual);
        Assert.Equal(DigestionReceiptAlignment.Seen, first.AlignmentFor(AtomId(current.Claims[0])));
        Assert.Equal(DigestionReceiptAlignment.Seen, first.AlignmentFor(AtomId(normalized.Claims[1])));
        Assert.Equal(0, calls);

        var second = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Admission,
            _ => atomizer,
            baselineSnapshot: snapshot);

        Assert.Empty(second.Findings);
        Assert.Equal(0, calls);
    }

    [Fact]
    public void CasBackedBoundaryAndStructuralReceiptsAreBothSeen()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。legacy。\n\n**定理 1.2(B)**。structural。\n");
        var document = GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var captures = document.Claims
            .Select(static atom => DigestionCasStore.Capture(atom.RawBytes.AsSpan()))
            .ToArray();
        var ledger = WithGenreCheck(
            Ledger(
                [],
                Entry("legacy-receipt", document.Claims[0]),
                Entry("structural-receipt", document.Claims[1])),
            GenreRegistryCheck.Collected([]));

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(bytes, captures),
            ledger,
            DigestionAlignmentMode.Admission);

        Assert.Empty(result.Findings);
        Assert.Empty(result.Residual);
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(AtomId(document.Claims[0])));
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(AtomId(document.Claims[1])));
    }

    [Fact]
    public void AdmissionAcceptsCasBackedHistoricalAndCurrentReceiptsWithoutReatomizing()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var newAtom = Assert.Single(GictAtomizer.Atomize(newBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var newCapture = DigestionCasStore.Capture(newAtom.RawBytes.AsSpan());
        var baseline = WithGenreCheck(
            Ledger([], Entry("old-receipt", oldAtom)),
            GenreRegistryCheck.Collected([]));
        var unacknowledged = WithGenreCheck(
            Ledger([], Entry("old-receipt", oldAtom)),
            GenreRegistryCheck.Collected([]));

        var rejected = DigestionLedgerAligner.Evaluate(
            unacknowledged,
            Snapshot(newBytes, [oldCapture]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Equal(DigestionReceiptAlignment.Seen, rejected.AlignmentFor(AtomId(oldAtom)));
        Assert.Empty(rejected.ActualStale);
        Assert.Empty(rejected.Residual);
        Assert.Empty(rejected.Findings);

        var closed = WithGenreCheck(
            Ledger(
                [AtomId(oldAtom)],
                Entry("old-receipt", oldAtom),
                Entry("new-receipt", newAtom)),
            GenreRegistryCheck.Collected([]));
        var admitted = DigestionLedgerAligner.Evaluate(
            closed,
            Snapshot(newBytes, [oldCapture, newCapture]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(admitted.Findings);
        Assert.Equal(DigestionReceiptAlignment.Seen, admitted.AlignmentFor(AtomId(oldAtom)));
        Assert.Equal(DigestionReceiptAlignment.Seen, admitted.AlignmentFor(AtomId(newAtom)));
        Assert.Empty(admitted.Residual);
    }

    [Fact]
    public void ChangedAstPathCannotInheritCasIdentity()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(
            oldBytes,
            DigestionTestSupport.Rules).Claims);
        var currentAtom = Assert.Single(GictAtomizer.Atomize(
            currentBytes,
            DigestionTestSupport.Rules).Claims);
        var oldId = Convert.ToHexStringLower(SHA256.HashData(oldAtom.RawBytes.AsSpan()));
        var currentId = Convert.ToHexStringLower(SHA256.HashData(currentAtom.RawBytes.AsSpan()));
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var baseline = Ledger([], Entry("old-receipt", oldAtom));

        var plan = DigestionIngestor.Plan(
            baseline,
            Snapshot(currentBytes, [oldCapture]),
            baseline);
        var entries = plan.Document.RequireDigestionEntries();

        Assert.NotEqual(oldId, currentId);
        Assert.Equal(
            new[] { oldId, currentId }.Order(StringComparer.Ordinal),
            entries.Select(static entry => entry.AtomId).Order(StringComparer.Ordinal).ToArray());
        Assert.All(entries, entry => Assert.Equal("sha256:" + entry.AtomId, entry.CasRef));
        Assert.Contains(
            plan.CasObjects,
            item => item.Reference == "sha256:" + currentId);
    }

    [Fact]
    public void ChangedStatusCannotInheritBaselineReceipt()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var entry = Entry("old-receipt", oldAtom);
        var baseline = Ledger([], entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        });
        var candidate = Ledger([], entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        });

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(newBytes, [oldCapture]),
            baseline,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(oldAtom)));
        Assert.Single(result.Residual);
    }

    [Fact]
    public void ChangedStatusWithCanonicalDirectoryMoveCannotInheritBaselineReceipt()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var entry = Entry("old-receipt", oldAtom);
        var baseline = Ledger([], entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        });
        var candidateEntry = entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };
        var candidate = Ledger([], candidateEntry);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(
                newBytes,
                [oldCapture],
                extraEntries:
                [
                    new RawRepositoryEntry(
                        $"Meta/Digestion/backfill/source/partial-open/{AtomId(oldAtom)}.yaml",
                        BackfillInventoryWriter.WriteAtom(candidateEntry)),
                ]),
            baseline,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(oldAtom)));
        Assert.Single(result.Residual);
    }

    [Fact]
    public void IngestStatusAuthorityRejectionSurvivesRawFingerprintMatch()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。unchanged。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules).Claims);
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var baselineEntry = Entry("baseline", atom) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };

        var result = DigestionLedgerAligner.Evaluate(
            Ledger([], candidateEntry),
            Snapshot(
                sourceBytes,
                [capture],
                extraEntries:
                [
                    new RawRepositoryEntry(
                        $"Meta/Digestion/backfill/source/partial-open/{AtomId(atom)}.yaml",
                        BackfillInventoryWriter.WriteAtom(candidateEntry)),
                ]),
            Ledger([], baselineEntry),
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(atom)));
        Assert.Null(result.AtomFor(AtomId(atom)));
    }

    [Fact]
    public void IngestStatusAuthorityRejectionSurvivesNormalizedFingerprintMatch()
    {
        var baselineBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。unchanged。\n");
        var candidateBytes = Encoding.UTF8.GetBytes("# GICT\r\n\r\n**定理 1.1(A)**。unchanged。\r\n");
        var baselineAtom = Assert.Single(GictAtomizer.Atomize(
            baselineBytes,
            DigestionTestSupport.Rules).Claims);
        var candidateAtom = Assert.Single(GictAtomizer.Atomize(
            candidateBytes,
            DigestionTestSupport.Rules).Claims);
        Assert.NotEqual(baselineAtom.Fingerprints.RawSha256, candidateAtom.Fingerprints.RawSha256);
        Assert.Equal(
            baselineAtom.Fingerprints.NormalizedSha256,
            candidateAtom.Fingerprints.NormalizedSha256);

        var capture = DigestionCasStore.Capture(baselineAtom.RawBytes.AsSpan());
        var baselineEntry = Entry("baseline", baselineAtom) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };

        var result = DigestionLedgerAligner.Evaluate(
            Ledger([], candidateEntry),
            Snapshot(
                candidateBytes,
                [capture],
                extraEntries:
                [
                    new RawRepositoryEntry(
                        $"Meta/Digestion/backfill/source/partial-open/{AtomId(baselineAtom)}.yaml",
                        BackfillInventoryWriter.WriteAtom(candidateEntry)),
                ]),
            Ledger([], baselineEntry),
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(AtomId(baselineAtom)));
        Assert.Null(result.AtomFor(AtomId(baselineAtom)));
    }

    [Fact]
    public void CanonicalStatusDirectoryMoveWithoutReceiptFailsClosedInAdmission()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("opaque status move source\n");
        var atomBytes = Encoding.UTF8.GetBytes("settled atom\n");
        var atom = new DigestionAtom(
            0,
            atomBytes.Length,
            ImmutableArray.CreateRange(atomBytes),
            DigestionFingerprint.Compute(atomBytes.AsSpan()),
            []);
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var atomId = AtomId(atom);
        var baselineEntry = Entry("baseline", atom) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };
        var baseline = WithAtomizer(
            Ledger([], baselineEntry),
            AtomizerRegistry.NoAtomizerId);
        var candidate = WithAtomizer(
            Ledger([], candidateEntry),
            AtomizerRegistry.NoAtomizerId);
        var baselinePath = $"Meta/Digestion/backfill/source/absorbed-open/{atomId}.yaml";
        var candidatePath = $"Meta/Digestion/backfill/source/partial-open/{atomId}.yaml";
        var changes = RawChangeSet.CreateWithKinds(
        [
            (baselinePath, RawChangeKind.Deleted),
            (candidatePath, RawChangeKind.Added),
        ]);

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            candidate,
            Snapshot(
                sourceBytes,
                [capture],
                extraEntries:
                [
                    new RawRepositoryEntry(
                        candidatePath,
                        BackfillInventoryWriter.WriteAtom(candidateEntry)),
                ]),
            DigestionTestSupport.AcceptedLean(Array.Empty<string>()),
            baselineDocument: baseline,
            changes: changes);
        var evaluated = Assert.Single(evaluation.Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, evaluated.Alignment);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            evaluated.DerivedStatus);
        Assert.Contains(
            $"entry {atomId} handwritten status partial-open differs from derived residual-open",
            evaluation.Findings);
    }

    [Fact]
    public void SettledReceiptSurvivesAcknowledgedStaleSourceViewSplit()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("opaque settled source\n");
        var atomBytes = Encoding.UTF8.GetBytes("settled atom\n");
        var atom = new DigestionAtom(
            0,
            atomBytes.Length,
            ImmutableArray.CreateRange(atomBytes),
            DigestionFingerprint.Compute(atomBytes.AsSpan()),
            []);
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var atomId = AtomId(atom);
        var baselineEntry = Entry("baseline", atom) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Closed),
        };
        var baseline = WithAtomizer(
            Ledger([atomId], baselineEntry),
            AtomizerRegistry.NoAtomizerId);
        var candidate = WithAtomizer(
            Ledger([], candidateEntry),
            AtomizerRegistry.NoAtomizerId);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, [capture]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(atomId));
    }

    [Fact]
    public void ProjectedStatusDirectoryMoveSurvivesBaselineIdentity()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("status directory move source\n");
        var atomBytes = Encoding.UTF8.GetBytes("settled atom\n");
        var atom = new DigestionAtom(
            0,
            atomBytes.Length,
            ImmutableArray.CreateRange(atomBytes),
            DigestionFingerprint.Compute(atomBytes.AsSpan()),
            []);
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var baselineEntry = Entry("baseline", atom) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Closed),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
        };
        var baseline = WithAtomizer(
            Ledger([], baselineEntry),
            AtomizerRegistry.NoAtomizerId);
        var candidate = WithAtomizer(
            Ledger([], candidateEntry),
            AtomizerRegistry.NoAtomizerId);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(
                sourceBytes,
                [capture],
                extraEntries:
                [
                    new RawRepositoryEntry(
                        $"Meta/Digestion/backfill/source/absorbed-closed/{AtomId(atom)}.yaml",
                        BackfillInventoryWriter.WriteAtom(candidateEntry)),
                ]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(AtomId(atom)));
    }

    [Fact]
    public void FingerprintTamperingCannotInheritBoundaryBaselineIdentity()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var currentAtom = Assert.Single(GictAtomizer.Atomize(currentBytes, DigestionTestSupport.Rules).Claims);
        var baseline = Ledger(
            [],
            Entry("old-receipt", oldAtom));
        var tampered = new DigestionFingerprints(
            "sha256:" + new string('0', 64),
            oldAtom.Fingerprints.NormalizedSha256);
        var oldAtomId = AtomId(oldAtom);
        var candidate = Ledger(
            [oldAtomId],
            EntryWithFingerprints(oldAtomId, tampered),
            Entry("current-receipt", currentAtom));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(oldAtomId));
        Assert.Contains(result.Findings, finding => finding.Contains(
            $"entry {oldAtomId} CAS blob is missing",
            StringComparison.Ordinal));
    }

    [Fact]
    public void NewlyAddedFakeFingerprintIsRejectedEvenWhenAcknowledged()
    {
        var bytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);
        var baseline = Ledger([], Entry("real-receipt", atom));
        var fakeId = new string('f', 64);
        var fake = EntryWithFingerprints(
            fakeId,
            new DigestionFingerprints(
                "sha256:" + new string('0', 64),
                "sha256:" + new string('1', 64)));
        var candidate = Ledger(
            [fakeId],
            Entry("real-receipt", atom),
            fake);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(bytes),
            baseline,
            DigestionAlignmentMode.Ingest);

        Assert.Contains(result.Findings, finding => finding.Contains(
            $"entry {fakeId} CAS blob is missing",
            StringComparison.Ordinal));
    }

    [Fact]
    public void DistinctContentAtomsNeedNoOccurrenceDisambiguation()
    {
        var firstBytes = ImmutableArray.Create((byte)'a');
        var secondBytes = ImmutableArray.Create((byte)'b');
        var first = new DigestionAtom(
            0,
            1,
            firstBytes,
            DigestionFingerprint.Compute(firstBytes.AsSpan()),
            []);
        var second = new DigestionAtom(
            1,
            2,
            secondBytes,
            DigestionFingerprint.Compute(secondBytes.AsSpan()),
            []);
        var duplicateDocument = new AtomizedTheoryDocument(
            [first, second],
            [new DigestionSlice(true, firstBytes), new DigestionSlice(true, secondBytes)],
            GenreRegistryCheck.NoGenreRegistry);
        var ledger = Ledger([]);
        var calls = 0;

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(Encoding.UTF8.GetBytes("ab")),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => (bytes, _) =>
            {
                calls++;
                return duplicateDocument;
            });

        Assert.Equal(1, calls);
        Assert.Empty(result.Findings);
        Assert.Equal(2, result.Residual.Length);
        Assert.Equal(
            [
                first.Fingerprints.RawSha256["sha256:".Length..],
                second.Fingerprints.RawSha256["sha256:".Length..],
            ],
            result.Residual.Select(static item => item.SuggestedAtomId));
    }

    [Fact]
    public void IngestPreservesHistoricalCasAndRegistersEveryNewContentAtom()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var baseline = Ledger([], Entry("old-receipt", oldAtom));
        var candidate = Ledger([], Entry("old-receipt", oldAtom));

        var plan = DigestionIngestor.Plan(candidate, Snapshot(currentBytes, [oldCapture]), baseline);
        var source = Assert.Single(plan.Document.RequireDigestionSources());
        var added = source.Entries.Where(entry => entry.AtomId != AtomId(oldAtom)).ToArray();

        Assert.Equal(0, plan.StaleAcknowledged);
        Assert.Equal(2, plan.ResidualOpenAdded);
        Assert.Empty(source.AcknowledgedStale);
        Assert.Equal(2, added.Length);
        Assert.All(added, entry =>
        {
            Assert.Empty(entry.CoverageGids);
            Assert.Empty(entry.Receipts.Coverage);
            Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
        });
        Assert.Equal(
            GictAtomizer.Atomize(currentBytes, DigestionTestSupport.Rules).Claims
                .Select(static atom => atom.Fingerprints.RawSha256)
                .Order(StringComparer.Ordinal),
            added.Select(static entry => entry.Fingerprints.RawSha256).Order(StringComparer.Ordinal));

        var admitted = DigestionLedgerAligner.Evaluate(
            plan.Document,
            Snapshot(currentBytes, plan.CasObjects.Prepend(oldCapture)),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(admitted.Findings);
        Assert.Empty(admitted.Residual);
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            admitted.AlignmentFor(AtomId(oldAtom)));
    }

    [Fact]
    public void IngestDropsObsoleteAcknowledgmentWithoutCreatingANewOne()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。unchanged。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var atomId = AtomId(atom);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var baseline = Ledger([], CasEntry("baseline", atom, captured.Reference));
        var candidate = Ledger([atomId], CasEntry("candidate", atom, captured.Reference));

        var plan = DigestionIngestor.Plan(
            candidate,
            Snapshot(sourceBytes, [captured]),
            baseline);
        var source = Assert.Single(plan.Document.RequireDigestionSources());

        Assert.Equal(DigestionReceiptAlignment.Seen, plan.Alignment.AlignmentFor(atomId));
        Assert.Empty(source.AcknowledgedStale);
        Assert.Equal(0, plan.StaleAcknowledged);
        Assert.Equal(0, plan.ResidualOpenAdded);
        Assert.Empty(plan.CasObjects);
    }

    [Fact]
    public void IngestMigratesCasBackedBoundariesAgainstNewVolumeAndIsByteIdempotent()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var baseline = Ledger(
            [],
            Entry("old-receipt", oldAtom));

        var first = DigestionIngestor.Plan(
            baseline,
            Snapshot(currentBytes, [oldCapture]),
            baseline);
        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        var migrated = first.Document;
        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(currentBytes, first.CasObjects.Prepend(oldCapture)),
            baseline);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Equal(0, first.StaleAcknowledged);
        Assert.Equal(2, first.ResidualOpenAdded);
        var source = Assert.Single(first.Document.RequireDigestionSources());
        Assert.Empty(source.AcknowledgedStale);
        Assert.Equal(0, second.StaleAcknowledged);
        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Equal(firstBytes, secondBytes);
    }

    private static (BackfillInventoryDocument Ledger, DigestionCasObject Capture) ExistingCasBackedLedger()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var ledger = Ledger(
            [],
            CasEntry("old-receipt", oldAtom, oldCapture.Reference));
        return (ledger, oldCapture);
    }

    internal static RepositorySnapshot Snapshot(
        byte[] sourceBytes,
        IEnumerable<DigestionCasObject>? casObjects = null,
        string sourcePath = "docs/source.md",
        IEnumerable<RawRepositoryEntry>? extraEntries = null)
    {
        var entries = new List<RawRepositoryEntry>
        {
            new(sourcePath, ImmutableArray.CreateRange(sourceBytes)),
            new(
                TheoryAtomizerDataLoader.DataPath,
                ImmutableArray.CreateRange(DigestionTestSupport.RulesBytes)),
        };
        entries.AddRange((casObjects ?? []).Select(static item =>
            new RawRepositoryEntry(item.RelativePath, item.Bytes)));
        entries.AddRange(extraEntries ?? []);
        var raw = RawRepositorySnapshot.Create(entries);
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

}
