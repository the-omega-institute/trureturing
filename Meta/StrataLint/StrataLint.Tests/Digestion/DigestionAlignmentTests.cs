using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionAlignmentTests
{
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
    public void BaselineStaleRequiresExactReceiptRepresentation()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var baselineText = Ledger([], Entry("old-receipt", oldAtom));
        var candidateText = baselineText.Replace(
            "atom_id: old-receipt",
            "atom_id: 'old-receipt'",
            StringComparison.Ordinal);

        var result = DigestionLedgerAligner.Evaluate(
            BackfillInventoryLoader.Load(candidateText),
            Snapshot(newBytes),
            BackfillInventoryLoader.Load(baselineText),
            DigestionAlignmentMode.Ingest);

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor("old-receipt"));
        Assert.Contains(result.Findings, finding => finding.Contains(
            "is not byte-equal in the baseline ledger",
            StringComparison.Ordinal));
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
    public void PostStatusCommentMutationDoesNotInheritBaselineStaleIdentity()
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

        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor("old-receipt"));
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
            + "and is not byte-equal in the baseline ledger",
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
            Snapshot(currentBytes),
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

    private static RepositorySnapshot Snapshot(byte[] sourceBytes)
    {
        var raw = RawRepositorySnapshot.Create(
        [
            new RawRepositoryEntry("docs/source.md", ImmutableArray.CreateRange(sourceBytes)),
        ]);
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
