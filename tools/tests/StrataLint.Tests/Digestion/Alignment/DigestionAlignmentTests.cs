using System.Collections.Immutable;
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
            "coarse/source",
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
    public void IngestPreservesTheLegacyResidualIdForASingleOccurrence()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。seen。\n\n**定理 1.2(B)**。new。\n");
        var atoms = GictAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules).Claims;
        var seenCapture = DigestionCasStore.Capture(atoms[0].RawBytes.AsSpan());
        var ledger = Ledger([], Entry("seen-receipt", atoms[0]));

        var plan = DigestionIngestor.Plan(ledger, Snapshot(sourceBytes, [seenCapture]), ledger);

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
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor("cas-receipt"));
    }

    [Fact]
    public void IngestCreatesDistinctReceiptsForByteIdenticalOccurrences()
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
            .Where(static entry => entry.AtomId != "old-receipt")
            .ToArray();
        Assert.Equal(2, added.Length);
        Assert.Equal(2, added.Select(static entry => entry.AtomId).Distinct().Count());
        Assert.Equal(2, added.Select(static entry => entry.AstPath).Distinct().Count());
        Assert.Single(added.Select(static entry => entry.CasRef).Distinct());
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
        Assert.Equal(DigestionReceiptAlignment.Seen, first.AlignmentFor("raw-receipt"));
        Assert.Equal(DigestionReceiptAlignment.Seen, first.AlignmentFor("normalized-receipt"));
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
                BoundaryEntry("legacy-receipt", document.Claims[0]),
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
            result.AlignmentFor("legacy-receipt"));
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor("structural-receipt"));
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

        Assert.Equal(DigestionReceiptAlignment.Seen, rejected.AlignmentFor("old-receipt"));
        Assert.Empty(rejected.ActualStale);
        Assert.Empty(rejected.Residual);
        Assert.Empty(rejected.Findings);

        var closed = WithGenreCheck(
            Ledger(
                ["old-receipt"],
                Entry("old-receipt", oldAtom),
                Entry("new-receipt", newAtom)),
            GenreRegistryCheck.Collected([]));
        var admitted = DigestionLedgerAligner.Evaluate(
            closed,
            Snapshot(newBytes, [oldCapture, newCapture]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(admitted.Findings);
        Assert.Equal(DigestionReceiptAlignment.Stale, admitted.AlignmentFor("old-receipt"));
        Assert.Equal(DigestionReceiptAlignment.Seen, admitted.AlignmentFor("new-receipt"));
        Assert.Empty(admitted.Residual);
    }

    [Fact]
    public void ChangedAstPathCannotInheritCasIdentity()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var newAtom = Assert.Single(GictAtomizer.Atomize(newBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var newCapture = DigestionCasStore.Capture(newAtom.RawBytes.AsSpan());
        var baseline = WithGenreCheck(
            Ledger(
                [],
                BoundaryEntry("old-receipt", oldAtom)),
            GenreRegistryCheck.Collected([]));
        var candidate = WithGenreCheck(
            Ledger(
                ["old-receipt"],
                EntryForPath("old-receipt", "promoted/theorem/1.1", oldAtom.Fingerprints),
                Entry("current-receipt", newAtom)),
            GenreRegistryCheck.Collected([]));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(newBytes, [oldCapture, newCapture]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(result.Findings);
        Assert.Empty(result.Residual);
        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor("old-receipt"));
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor("current-receipt"));
        Assert.Empty(result.ActualStale);
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
        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor("old-receipt"));
        Assert.Single(result.Residual);
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
            BoundaryEntry("old-receipt", oldAtom));
        var tampered = new DigestionFingerprints(
            "sha256:" + new string('0', 64),
            oldAtom.Fingerprints.NormalizedSha256);
        var candidate = Ledger(
            ["old-receipt"],
            EntryForPath("old-receipt", oldAtom.AstPath, tampered),
            Entry("current-receipt", currentAtom));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor("old-receipt"));
        Assert.Contains(result.Findings, finding => finding.Contains(
            "entry old-receipt CAS blob is missing",
            StringComparison.Ordinal));
    }

    [Fact]
    public void NewlyAddedFakeFingerprintIsRejectedEvenWhenAcknowledged()
    {
        var bytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);
        var baseline = Ledger([], Entry("real-receipt", atom));
        var fake = EntryForPath(
            "fake-receipt",
            atom.AstPath,
            new DigestionFingerprints(
                "sha256:" + new string('0', 64),
                "sha256:" + new string('1', 64)));
        var candidate = Ledger(
            ["fake-receipt"],
            Entry("real-receipt", atom),
            fake);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(bytes),
            baseline,
            DigestionAlignmentMode.Ingest);

        Assert.Contains(result.Findings, finding => finding.Contains(
            "entry fake-receipt CAS blob is missing",
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
            [new DigestionSlice(true, firstBytes), new DigestionSlice(true, secondBytes)],
            GenreRegistryCheck.NoGenreRegistry);
        var ledger = Ledger([], Entry("receipt", first));
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
        Assert.Contains(result.Findings, finding => finding.Contains(
            "duplicate atomized ast_path: theorem/1.1",
            StringComparison.Ordinal));
    }

    [Fact]
    public void IngestRetiresReplacedHistoricalCasAndRegistersEveryResidualOpenClaim()
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
            Snapshot(currentBytes, plan.CasObjects.Prepend(oldCapture)),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(admitted.Findings);
        Assert.Empty(admitted.Residual);
        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            admitted.AlignmentFor("old-receipt"));
    }

    [Fact]
    public void IngestDropsObsoleteAcknowledgmentWithoutCreatingANewOne()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var baseline = Ledger([], Entry("old-receipt", oldAtom));
        var acknowledged = Ledger(
            ["old-receipt"],
            Entry("old-receipt", oldAtom));

        var plan = DigestionIngestor.Plan(
            acknowledged,
            Snapshot(currentBytes, [oldCapture]),
            baseline);

        Assert.Equal(0, plan.StaleAcknowledged);
        Assert.Equal(
            ["old-receipt"],
            Assert.Single(plan.Document.RequireDigestionSources()).AcknowledgedStale.ToArray());
    }

    [Fact]
    public void ProjectedStatusKeepsSettledStaleReceiptIdentityAndAlignmentByteIdempotent()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(A)**。rewritten。\n\n**定理 1.2(B)**。new。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(
            oldBytes,
            DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var original = Ledger([], Entry("old-receipt", oldAtom));
        var firstPlan = DigestionIngestor.Plan(
            original,
            Snapshot(currentBytes, [oldCapture]),
            original);
        var settled = firstPlan.Document;
        var snapshot = Snapshot(currentBytes, firstPlan.CasObjects.Prepend(oldCapture));
        var settledAlignment = DigestionLedgerAligner.Evaluate(
            settled,
            snapshot,
            settled,
            DigestionAlignmentMode.Admission);
        var source = Assert.Single(settled.RequireDigestionSources());
        var projected = settled.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries.Select(entry => entry.AtomId == "old-receipt"
                    ? entry with
                    {
                        ProjectedStatus = new DigestionStatus(
                            DigestionMigrationState.Partial,
                            DigestionTruthState.Closed),
                    }
                    : entry).ToImmutableArray(),
            },
        ]);

        var projectedAlignment = DigestionLedgerAligner.Evaluate(
            projected,
            snapshot,
            settled,
            DigestionAlignmentMode.Admission);
        var replay = DigestionIngestor.Plan(
            projected,
            snapshot,
            settled);
        var replayBytes = DirectoryLedgerTestSupport.Image(replay.Document);
        var secondReplay = DigestionIngestor.Plan(
            replay.Document,
            snapshot,
            settled);

        Assert.Empty(projectedAlignment.Findings);
        Assert.Empty(replay.Alignment.Findings);
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            settledAlignment.AlignmentFor("old-receipt"));
        Assert.Equal(
            settledAlignment.AlignmentFor("old-receipt"),
            projectedAlignment.AlignmentFor("old-receipt"));
        Assert.Equal(
            projectedAlignment.AlignmentFor("old-receipt"),
            replay.Alignment.AlignmentFor("old-receipt"));
        Assert.Empty(secondReplay.Alignment.Findings);
        Assert.Equal(replayBytes, DirectoryLedgerTestSupport.Image(secondReplay.Document));
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
            BoundaryEntry("old-receipt", oldAtom));

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
        Assert.All(source.Entries, static entry => Assert.Null(entry.Boundary));
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
