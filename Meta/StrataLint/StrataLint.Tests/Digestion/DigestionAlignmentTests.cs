using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void IngestFallsBackToOneWholeSourceAtomWhenTheSourceFormatCannotBeAtomized()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("old-receipt", oldAtom, oldCapture.Reference)));
        var malformedBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**未知 1.2(B)**。free-form source。\n");

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(malformedBytes, [oldCapture]),
            ledger);

        var fallback = Assert.Single(plan.Fallbacks);
        Assert.Equal("source", fallback.SourceId);
        Assert.Contains("unknown GICT numbered claim kind", fallback.Reason, StringComparison.Ordinal);
        var coarse = Assert.Single(plan.Document.RequireDigestionEntries().Where(static entry =>
            entry.AtomId != "old-receipt"));
        var captured = Assert.Single(plan.CasObjects);
        Assert.Equal(captured.Reference, coarse.CasRef);
        Assert.Equal(captured.Reference, coarse.Fingerprints.RawSha256);
        Assert.Equal(malformedBytes, captured.Bytes.ToArray());

        var firstBytes = BackfillInventoryWriter.WriteForIngest(plan.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));
        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(malformedBytes, new[] { oldCapture }.Concat(plan.CasObjects)),
            ledger);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Single(second.Fallbacks);
        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    [Fact]
    public void IngestDoesNotFallbackForInternalAtomizerFormatFailures()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("old-receipt", oldAtom, oldCapture.Reference)));

        var exception = Assert.Throws<FormatException>(() => DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(Encoding.UTF8.GetBytes("source"), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => _ => throw new FormatException("invalid Markdown AST span")));

        Assert.Contains("invalid Markdown AST span", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestFallsBackToExactCoarseAtomForNonUtf8TheoryBytes()
    {
        const string theoryPath = "docs/develop/theory/non-utf8.bin";
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
                [],
                CasEntry("old-receipt", oldAtom, oldCapture.Reference))
            .Replace("path: docs/source.md", $"path: {theoryPath}", StringComparison.Ordinal));
        var opaqueBytes = new byte[] { 0xff, 0x00, 0xfe };

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(opaqueBytes, [oldCapture], theoryPath),
            ledger);

        var fallback = Assert.Single(plan.Fallbacks);
        Assert.Contains("Unicode", fallback.Reason, StringComparison.OrdinalIgnoreCase);
        var captured = Assert.Single(plan.CasObjects);
        Assert.Equal(opaqueBytes, captured.Bytes.ToArray());
        Assert.Equal(
            captured.Reference,
            plan.Document.RequireDigestionEntries().Single(static entry =>
                entry.AtomId != "old-receipt").CasRef);
    }

    [Fact]
    public void IngestCapturesSeenAndResidualAtomBytesAndRemainsByteIdempotent()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。seen。\n\n**定理 1.2(B)**。new。\n");
        var atoms = GictAtomizer.Atomize(sourceBytes).Claims;
        var ledger = BackfillInventoryLoader.Load(Ledger([], Entry("seen-receipt", atoms[0])));

        var first = DigestionIngestor.Plan(ledger, Snapshot(sourceBytes), ledger);
        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));

        Assert.Equal(1, first.ResidualOpenAdded);
        Assert.Equal(2, first.CasObjects.Length);
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
            Snapshot(sourceBytes, first.CasObjects),
            ledger);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    [Fact]
    public void IngestCapturesNoAtomizerBoundaryBytesAndRemainsByteIdempotent()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var atom = new DigestionAtom(
            "manual/receipt",
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            ImmutableArray<DigestionContext>.Empty);
        var ledgerText = Ledger([], LegacyEntry("spec-receipt", atom))
            .Replace(
                $"    atomizer: {AtomizerRegistry.GictId}\n    acknowledged_stale: []\n",
                $"    atomizer: {AtomizerRegistry.NoAtomizerId}\n",
                StringComparison.Ordinal);
        var ledger = BackfillInventoryLoader.Load(ledgerText);

        var first = DigestionIngestor.Plan(ledger, Snapshot(sourceBytes), ledger);
        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));

        var captured = Assert.Single(first.CasObjects);
        var migratedEntry = Assert.Single(migrated.RequireDigestionEntries());
        Assert.NotNull(migratedEntry.Boundary);
        Assert.Equal(atom.Fingerprints.RawSha256, migratedEntry.CasRef);
        Assert.Equal(sourceBytes, captured.Bytes.ToArray());

        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, first.CasObjects),
            ledger);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Empty(second.CasObjects);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    [Fact]
    public void IngestPreservesTheLegacyResidualIdForASingleOccurrence()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。seen。\n\n**定理 1.2(B)**。new。\n");
        var atoms = GictAtomizer.Atomize(sourceBytes).Claims;
        var ledger = BackfillInventoryLoader.Load(Ledger([], Entry("seen-receipt", atoms[0])));

        var plan = DigestionIngestor.Plan(ledger, Snapshot(sourceBytes), ledger);

        var residual = Assert.Single(plan.Document.RequireDigestionEntries().Where(static entry =>
            entry.AtomId != "seen-receipt"));
        Assert.Equal(
            AtomizerRegistry.Require(AtomizerRegistry.GictId).ResidualPrefix
            + "-residual-"
            + atoms[1].Fingerprints.RawSha256["sha256:".Length..],
            residual.AtomId);
    }

    [Fact]
    public void CasBackedReceiptDoesNotRequireSourceReconciliation()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(sourceBytes).Claims);
        var captured = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("cas-receipt", atom, captured.Reference)));
        var raw = RawRepositorySnapshot.Create(
        [
            new RawRepositoryEntry(captured.RelativePath, captured.Bytes),
        ]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Admission);

        Assert.Empty(result.Findings);
        Assert.Empty(result.Residual);
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor("cas-receipt"));
    }

    [Fact]
    public void IngestCreatesDistinctReceiptsForByteIdenticalOccurrences()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("old-receipt", oldAtom, oldCapture.Reference)));
        var duplicateBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\n| κ | 1 |\n");

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(duplicateBytes, [oldCapture]),
            ledger);

        var added = plan.Document.RequireDigestionEntries()
            .Where(static entry => entry.AtomId != "old-receipt")
            .ToArray();
        Assert.Equal(2, added.Length);
        Assert.Equal(2, added.Select(static entry => entry.AtomId).Distinct().Count());
        Assert.Equal(2, added.Select(static entry => entry.AstPath).Distinct().Count());
        Assert.Single(added.Select(static entry => entry.CasRef).Distinct());
        Assert.Single(plan.CasObjects);
    }

    [Fact]
    public void StructuredAlignmentAtomizesOncePerSourcePerEvaluationWithoutStaticCaching()
    {
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。raw。\n\n**定理 1.2(B)**。normalized。\n");
        var normalizedBytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n**定理 1.1(A)**。raw。\r\n\r\n**定理 1.2(B)**。normalized。\r\n");
        var current = GictAtomizer.Atomize(currentBytes);
        var normalized = GictAtomizer.Atomize(normalizedBytes);
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            Entry("raw-receipt", current.Claims[0]),
            Entry("normalized-receipt", normalized.Claims[1])));
        var snapshot = Snapshot(currentBytes);
        var calls = 0;
        TheoryAtomizer atomizer = bytes =>
        {
            calls++;
            return GictAtomizer.Atomize(bytes);
        };

        var first = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Admission,
            _ => atomizer);

        Assert.Empty(first.Findings);
        Assert.Empty(first.Residual);
        Assert.Equal(DigestionReceiptAlignment.Seen, first.AlignmentFor("raw-receipt"));
        Assert.Equal(
            DigestionReceiptAlignment.NormalizedSeen,
            first.AlignmentFor("normalized-receipt"));
        Assert.Equal(1, calls);

        var second = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Admission,
            _ => atomizer);

        Assert.Empty(second.Findings);
        Assert.Equal(2, calls);
    }

    [Fact]
    public void MixedDualReadDoesNotReadmitLegacyBoundaryReceiptAsResidual()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。legacy。\n\n**定理 1.2(B)**。structural。\n");
        var document = GictAtomizer.Atomize(bytes);
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            LegacyEntry("legacy-receipt", document.Claims[0]),
            Entry("structural-receipt", document.Claims[1])));

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(bytes),
            ledger,
            DigestionAlignmentMode.Admission);

        Assert.Empty(result.Findings);
        Assert.Empty(result.Residual);
        Assert.Equal(
            DigestionReceiptAlignment.LegacyBoundary,
            result.AlignmentFor("legacy-receipt"));
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor("structural-receipt"));
    }

    [Fact]
    public void AdmissionRequiresStaleAcknowledgmentAndResidualRegistration()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var newAtom = Assert.Single(GictAtomizer.Atomize(newBytes).Claims);
        var baseline = BackfillInventoryLoader.Load(Ledger([], Entry("old-receipt", oldAtom)));
        var unacknowledged = BackfillInventoryLoader.Load(Ledger([], Entry("old-receipt", oldAtom)));

        var rejected = DigestionLedgerAligner.Evaluate(
            unacknowledged,
            Snapshot(newBytes),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Equal(DigestionReceiptAlignment.Stale, rejected.AlignmentFor("old-receipt"));
        Assert.Equal(["old-receipt"], rejected.ActualStale.ToArray());
        Assert.Equal(newAtom.AstPath, Assert.Single(rejected.Residual).Atom.AstPath);
        Assert.Contains(rejected.Findings, finding => finding.Contains(
            "stale receipts are not acknowledged: old-receipt",
            StringComparison.Ordinal));
        Assert.Contains(rejected.Findings, finding => finding.Contains(
            "unregistered residual-open atom",
            StringComparison.Ordinal));

        var closed = BackfillInventoryLoader.Load(Ledger(
            ["old-receipt"],
            Entry("old-receipt", oldAtom),
            Entry("new-receipt", newAtom)));
        var admitted = DigestionLedgerAligner.Evaluate(
            closed,
            Snapshot(newBytes),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(admitted.Findings);
        Assert.Equal(DigestionReceiptAlignment.Stale, admitted.AlignmentFor("old-receipt"));
        Assert.Equal(DigestionReceiptAlignment.Seen, admitted.AlignmentFor("new-receipt"));
        Assert.Empty(admitted.Residual);
    }

    [Fact]
    public void BaselineIdentityAllowsLegacyBoundaryToStructuredStaleMigration()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var newAtom = Assert.Single(GictAtomizer.Atomize(newBytes).Claims);
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            LegacyEntry("old-receipt", oldAtom)));
        var candidate = BackfillInventoryLoader.Load(Ledger(
            ["old-receipt"],
            Entry("old-receipt", "promoted/theorem/1.1", oldAtom.Fingerprints),
            Entry("current-receipt", newAtom)));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(newBytes),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(result.Findings);
        Assert.Empty(result.Residual);
        Assert.Equal(DigestionReceiptAlignment.Stale, result.AlignmentFor("old-receipt"));
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor("current-receipt"));
        Assert.Equal(["old-receipt"], result.ActualStale.ToArray());
    }

    [Fact]
    public void MachineDerivedStatusIsExcludedFromBaselineReceiptPreimage()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var entry = Entry("old-receipt", oldAtom);
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            entry.Replace("migration: residual", "migration: absorbed", StringComparison.Ordinal)));
        var candidate = BackfillInventoryLoader.Load(Ledger(
            [],
            entry.Replace("migration: residual", "migration: partial", StringComparison.Ordinal)));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(newBytes),
            baseline,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Stale, result.AlignmentFor("old-receipt"));
    }

    [Fact]
    public void StatusFirstReceiptRetainsBaselineStaleIdentity()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            StatusFirstEntry("old-receipt", oldAtom)));

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(newBytes),
            ledger,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Stale, result.AlignmentFor("old-receipt"));
    }

    [Fact]
    public void SpacedMappingKeysRetainBaselineStaleIdentity()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var ledgerText = Ledger([], Entry("old-receipt", oldAtom))
            .Replace("entries:", "entries :", StringComparison.Ordinal)
            .Replace("status:", "status :", StringComparison.Ordinal);
        var ledger = BackfillInventoryLoader.Load(ledgerText);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(newBytes),
            ledger,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Stale, result.AlignmentFor("old-receipt"));
    }

    [Fact]
    public void SpacedStatusFirstKeyRetainsBaselineStaleIdentity()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var ledgerText = Ledger([], StatusFirstEntry("old-receipt", oldAtom))
            .Replace("entries:", "entries :", StringComparison.Ordinal)
            .Replace("- status:", "- status :", StringComparison.Ordinal);
        var ledger = BackfillInventoryLoader.Load(ledgerText);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(newBytes),
            ledger,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Stale, result.AlignmentFor("old-receipt"));
    }

    [Fact]
    public void NonIdentitySyntaxMutationRetainsBaselineStaleIdentity()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var entry = Entry("old-receipt", oldAtom);
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            entry.Replace(
                "truth: open",
                "truth: open\n                # receipt-note: baseline",
                StringComparison.Ordinal)));
        var candidate = BackfillInventoryLoader.Load(Ledger(
            [],
            entry.Replace(
                "truth: open",
                "truth: open\n                # receipt-note: candidate",
                StringComparison.Ordinal)));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(newBytes),
            baseline,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Stale, result.AlignmentFor("old-receipt"));
    }

    [Fact]
    public void FingerprintTamperingCannotInheritLegacyBaselineIdentity()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var currentAtom = Assert.Single(GictAtomizer.Atomize(currentBytes).Claims);
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            LegacyEntry("old-receipt", oldAtom)));
        var tampered = new DigestionFingerprints(
            "sha256:" + new string('0', 64),
            oldAtom.Fingerprints.NormalizedSha256);
        var candidate = BackfillInventoryLoader.Load(Ledger(
            ["old-receipt"],
            Entry("old-receipt", oldAtom.AstPath, tampered),
            Entry("current-receipt", currentAtom)));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor("old-receipt"));
        Assert.Contains(result.Findings, finding => finding.Contains(
            "entry old-receipt fingerprint does not match ast_path theorem/1.1 "
            + "and has no matching baseline receipt identity",
            StringComparison.Ordinal));
    }

    [Fact]
    public void NewlyAddedFakeFingerprintIsRejectedEvenWhenAcknowledged()
    {
        var bytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(bytes).Claims);
        var baseline = BackfillInventoryLoader.Load(Ledger([], Entry("real-receipt", atom)));
        var fake = Entry(
            "fake-receipt",
            atom.AstPath,
            new DigestionFingerprints(
                "sha256:" + new string('0', 64),
                "sha256:" + new string('1', 64)));
        var candidate = BackfillInventoryLoader.Load(Ledger(
            ["fake-receipt"],
            Entry("real-receipt", atom),
            fake));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(bytes),
            baseline,
            DigestionAlignmentMode.Ingest);

        Assert.Contains(result.Findings, finding => finding.Contains(
            "entry fake-receipt fingerprint does not match ast_path theorem/1.1 "
            + "and has no matching baseline receipt identity",
            StringComparison.Ordinal));
    }

    [Fact]
    public void DuplicateAtomizedAstPathFailsClosed()
    {
        var firstBytes = ImmutableArray.Create((byte)'a');
        var secondBytes = ImmutableArray.Create((byte)'b');
        var first = new DigestionAtom(
            "theorem/1.1",
            0,
            1,
            firstBytes,
            DigestionFingerprint.Compute(firstBytes.AsSpan()),
            []);
        var second = new DigestionAtom(
            "theorem/1.1",
            1,
            2,
            secondBytes,
            DigestionFingerprint.Compute(secondBytes.AsSpan()),
            []);
        var duplicateDocument = new AtomizedTheoryDocument(
            [first, second],
            [new DigestionSlice(true, firstBytes), new DigestionSlice(true, secondBytes)]);
        var ledger = BackfillInventoryLoader.Load(Ledger([], Entry("receipt", first)));
        var calls = 0;

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(Encoding.UTF8.GetBytes("ab")),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => bytes =>
            {
                calls++;
                return duplicateDocument;
            });

        Assert.Equal(1, calls);
        Assert.Contains(result.Findings, finding => finding.Contains(
            "duplicate atomized ast_path: theorem/1.1",
            StringComparison.Ordinal));
    }

    [Fact]
    public void IngestAcknowledgesActualStaleAndRegistersEveryResidualOpenClaim()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var baseline = BackfillInventoryLoader.Load(Ledger([], Entry("old-receipt", oldAtom)));
        var candidate = BackfillInventoryLoader.Load(Ledger([], Entry("old-receipt", oldAtom)));

        var plan = DigestionIngestor.Plan(candidate, Snapshot(currentBytes), baseline);
        var source = Assert.Single(plan.Document.RequireDigestionSources());
        var added = source.Entries.Where(static entry => entry.AtomId != "old-receipt").ToArray();

        Assert.Equal(1, plan.StaleAcknowledged);
        Assert.Equal(2, plan.ResidualOpenAdded);
        Assert.Equal(["old-receipt"], source.AcknowledgedStale.ToArray());
        Assert.Equal(2, added.Length);
        Assert.All(added, entry =>
        {
            Assert.Null(entry.Boundary);
            Assert.Empty(entry.CoverageGids);
            Assert.Empty(entry.Receipts.Coverage);
            Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
        });
        Assert.Equal(
            ["theorem/1.1", "theorem/1.2"],
            added.Select(static entry => entry.AstPath).Order(StringComparer.Ordinal).ToArray());

        var admitted = DigestionLedgerAligner.Evaluate(
            plan.Document,
            Snapshot(currentBytes, plan.CasObjects),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(admitted.Findings);
        Assert.Empty(admitted.Residual);
    }

    [Fact]
    public void IngestCountsOnlyNewStaleAcknowledgments()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var baseline = BackfillInventoryLoader.Load(Ledger([], Entry("old-receipt", oldAtom)));
        var acknowledged = BackfillInventoryLoader.Load(Ledger(
            ["old-receipt"],
            Entry("old-receipt", oldAtom)));

        var plan = DigestionIngestor.Plan(acknowledged, Snapshot(currentBytes), baseline);

        Assert.Equal(0, plan.StaleAcknowledged);
        Assert.Equal(
            ["old-receipt"],
            Assert.Single(plan.Document.RequireDigestionSources()).AcknowledgedStale.ToArray());
    }

    [Fact]
    public void IngestMigratesLegacyBoundariesAgainstNewVolumeAndIsByteIdempotent()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            LegacyEntry("old-receipt", oldAtom)));

        var first = DigestionIngestor.Plan(baseline, Snapshot(currentBytes), baseline);
        var firstBytes = BackfillInventoryWriter.WriteForIngest(first.Document);
        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(firstBytes.AsSpan()));
        var second = DigestionIngestor.Plan(
            migrated,
            Snapshot(currentBytes, first.CasObjects),
            baseline);
        var secondBytes = BackfillInventoryWriter.WriteForIngest(second.Document);

        Assert.Equal(1, first.StaleAcknowledged);
        Assert.Equal(2, first.ResidualOpenAdded);
        var source = Assert.Single(first.Document.RequireDigestionSources());
        Assert.Equal(["old-receipt"], source.AcknowledgedStale.ToArray());
        Assert.All(source.Entries, static entry => Assert.Null(entry.Boundary));
        Assert.DoesNotContain("boundary:", Encoding.UTF8.GetString(firstBytes.AsSpan()), StringComparison.Ordinal);
        Assert.Equal(0, second.StaleAcknowledged);
        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Equal(firstBytes.ToArray(), secondBytes.ToArray());
    }

    private static (BackfillInventoryDocument Ledger, DigestionCasObject Capture) ExistingCasBackedLedger()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("old-receipt", oldAtom, oldCapture.Reference)));
        return (ledger, oldCapture);
    }

    private static RepositorySnapshot Snapshot(
        byte[] sourceBytes,
        IEnumerable<DigestionCasObject>? casObjects = null,
        string sourcePath = "docs/source.md")
    {
        var entries = new List<RawRepositoryEntry>
        {
            new(sourcePath, ImmutableArray.CreateRange(sourceBytes)),
        };
        entries.AddRange((casObjects ?? []).Select(static item =>
            new RawRepositoryEntry(item.RelativePath, item.Bytes)));
        var raw = RawRepositorySnapshot.Create(entries);
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static string Ledger(IReadOnlyList<string> acknowledgedStale, params string[] entries)
    {
        var acknowledgments = acknowledgedStale.Count == 0
            ? "[]"
            : "\n" + string.Join("\n", acknowledgedStale.Select(static value => "      - " + value));
        return $$"""
            schema_version: 3
            ledger: theory-digestion-v1
            sources:
              - source_id: source
                path: docs/source.md
                atomizer: {{AtomizerRegistry.GictId}}
                acknowledged_stale: {{acknowledgments}}
                entries:
            {{string.Join("\n", entries)}}
            ticket_index: []
            """;
    }

    private static string Entry(string atomId, DigestionAtom atom) =>
        Entry(atomId, atom.AstPath, atom.Fingerprints);

    private static string CasEntry(string atomId, DigestionAtom atom, string casRef) => $$"""
              - atom_id: {{atomId}}
                ast_path: {{atom.AstPath}}
                fingerprints:
                  raw_sha256: {{atom.Fingerprints.RawSha256}}
                  normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                cas_ref: {{casRef}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                  chain_atoms: []
                  tail_authorization: null
                status:
                  migration: residual
                  truth: open
        """;

    private static string LegacyEntry(string atomId, DigestionAtom atom) => $$"""
                  - atom_id: {{atomId}}
                    boundary:
                      ast_path: {{atom.AstPath}}
                      start_byte: {{atom.StartByte}}
                      end_byte: {{atom.EndByte}}
                    fingerprints:
                      raw_sha256: {{atom.Fingerprints.RawSha256}}
                      normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
                    status:
                      migration: residual
                      truth: open
            """;

    private static string StatusFirstEntry(string atomId, DigestionAtom atom) => $$"""
                  - status:
                      migration: residual
                      truth: open
                    atom_id: {{atomId}}
                    ast_path: {{atom.AstPath}}
                    fingerprints:
                      raw_sha256: {{atom.Fingerprints.RawSha256}}
                      normalized_sha256: {{atom.Fingerprints.NormalizedSha256}}
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
            """;

    private static string Entry(
        string atomId,
        string astPath,
        DigestionFingerprints fingerprints) => $$"""
                  - atom_id: {{atomId}}
                    ast_path: {{astPath}}
                    fingerprints:
                      raw_sha256: {{fingerprints.RawSha256}}
                      normalized_sha256: {{fingerprints.NormalizedSha256}}
                    coverage_gids: []
                    receipts:
                      coverage: []
                      scribe: []
                      unresolved_subitems: []
                      chain_atoms: []
                      tail_authorization: null
                    status:
                      migration: residual
                      truth: open
            """;
}
