using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void IngestRejectsAtomizerHashFailureInsteadOfFallingBack()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var corrupt = new DigestionAtom(
            "theorem/1.2",
            0,
            1,
            sourceBytes,
            new DigestionFingerprints(
                "sha256:" + new string('0', 64),
                "sha256:" + new string('0', 64)),
            []);
        var corruptDocument = new AtomizedTheoryDocument(
            [corrupt],
            [new DigestionSlice(true, sourceBytes)]);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => _ => corruptDocument);

        Assert.Empty(result.Fallbacks);
        Assert.Contains(result.Findings, finding =>
            finding.Contains("fingerprint", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void IngestRejectsAtomPayloadThatDiffersFromItsSourceSpan()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var fabricatedBytes = ImmutableArray.Create((byte)'b');
        var fabricated = new DigestionAtom(
            "theorem/1.2",
            0,
            1,
            fabricatedBytes,
            DigestionFingerprint.Compute(fabricatedBytes.AsSpan()),
            []);
        var fabricatedDocument = new AtomizedTheoryDocument(
            [fabricated],
            [new DigestionSlice(true, sourceBytes)]);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => _ => fabricatedDocument);

        Assert.Empty(result.Fallbacks);
        Assert.Empty(result.Residual);
        Assert.Contains(result.Findings, finding =>
            finding.Contains("source span", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void IngestRejectsZeroClaimAtomizerOutputThatDoesNotReassembleTheSource()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var corrupt = new AtomizedTheoryDocument(
            [],
            [new DigestionSlice(false, ImmutableArray.Create((byte)'b'))]);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => _ => corrupt);

        Assert.Empty(result.Fallbacks);
        Assert.Empty(result.Residual);
        Assert.Contains(result.Findings, finding =>
            finding.Contains("reassemble", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void IngestFallsBackWhenZeroClaimAtomizerOutputExactlyReassemblesTheSource()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var unrecognized = new AtomizedTheoryDocument(
            [],
            [new DigestionSlice(false, sourceBytes)]);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => _ => unrecognized);

        Assert.Empty(result.Findings);
        Assert.Single(result.Fallbacks);
        Assert.Equal(sourceBytes.ToArray(), Assert.Single(result.Residual).Atom.RawBytes.ToArray());
    }

    [Fact]
    public void CoarseFallbackDoesNotCollapseASeparateOccurrenceWithIdenticalBytes()
    {
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var fingerprints = DigestionFingerprint.Compute(sourceBytes.AsSpan());
        var existing = new DigestionAtom(
            "theorem/1.1",
            0,
            sourceBytes.Length,
            sourceBytes,
            fingerprints,
            []);
        var captured = DigestionCasStore.Capture(sourceBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("existing-receipt", existing, captured.Reference)));
        var unrecognized = new AtomizedTheoryDocument(
            [],
            [new DigestionSlice(false, sourceBytes)]);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [captured]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => _ => unrecognized);

        Assert.Empty(result.Findings);
        Assert.Single(result.Fallbacks);
        Assert.Equal("coarse/source", Assert.Single(result.Residual).Atom.AstPath);
    }

    [Fact]
    public void CasReceiptSubtractsOnlyItsRecordedOccurrenceWhenRawBytesRepeat()
    {
        var atomBytes = ImmutableArray.Create((byte)'a');
        var fingerprints = DigestionFingerprint.Compute(atomBytes.AsSpan());
        var first = new DigestionAtom("theorem/1.1", 0, 1, atomBytes, fingerprints, []);
        var second = new DigestionAtom("theorem/1.2", 1, 2, atomBytes, fingerprints, []);
        var captured = DigestionCasStore.Capture(atomBytes.AsSpan());
        var ledger = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("first-receipt", first, captured.Reference)));
        var atomized = new AtomizedTheoryDocument(
            [first, second],
            [new DigestionSlice(true, atomBytes), new DigestionSlice(true, atomBytes)]);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot([(byte)'a', (byte)'a'], [captured]),
            ledger,
            DigestionAlignmentMode.Ingest,
            _ => _ => atomized);

        Assert.Empty(result.Findings);
        Assert.Equal("theorem/1.2", Assert.Single(result.Residual).Atom.AstPath);
    }

    [Fact]
    public void IngestRetiresCoarseCasReceiptWhenARegisteredAdapterReplacesTheFallback()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**定理(观察者代数的唯一形态)。** claim。\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            "coarse/source",
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var captured = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var priorAtomizer = AtomizerRegistry.RegisteredIds.First(id =>
            id != AtomizerRegistry.ObserverId);
        var baseline = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("coarse-receipt", coarse, captured.Reference)));
        var candidate = BackfillInventoryLoader.Load(
            Ledger([], CasEntry("coarse-receipt", coarse, captured.Reference))
                .Replace(
                    $"atomizer: {priorAtomizer}",
                    $"atomizer: {AtomizerRegistry.ObserverId}",
                    StringComparison.Ordinal));

        var plan = DigestionIngestor.Plan(
            candidate,
            Snapshot(sourceBytes, [captured]),
            baseline);
        var source = Assert.Single(plan.Document.RequireDigestionSources());

        Assert.Equal(1, plan.StaleAcknowledged);
        Assert.Equal(["coarse-receipt"], source.AcknowledgedStale.ToArray());
        Assert.Equal(
            captured.Reference,
            source.Entries.Single(static entry => entry.AtomId == "coarse-receipt").CasRef);
        Assert.Equal(
            "theorem/observer-algebra",
            source.Entries.Single(static entry => entry.AtomId != "coarse-receipt").AstPath);

        var admitted = DigestionLedgerAligner.Evaluate(
            plan.Document,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(admitted.Findings);
        Assert.Empty(admitted.Residual);
        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            admitted.AlignmentFor("coarse-receipt"));

        var migrated = BackfillInventoryLoader.Load(Encoding.UTF8.GetString(
            BackfillInventoryWriter.WriteForIngest(plan.Document).AsSpan()));
        var settled = DigestionIngestor.Plan(
            migrated,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            migrated);

        Assert.Equal(0, settled.StaleAcknowledged);
        Assert.Equal(0, settled.ResidualOpenAdded);
        Assert.Equal(
            ["coarse-receipt"],
            Assert.Single(settled.Document.RequireDigestionSources()).AcknowledgedStale.ToArray());
    }

    [Fact]
    public void AdmissionRejectsRemovingASettledCoarseReplacementAcknowledgment()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**定理(观察者代数的唯一形态)。** claim。\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            "coarse/source",
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var captured = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var priorAtomizer = AtomizerRegistry.RegisteredIds.First(id =>
            id != AtomizerRegistry.ObserverId);
        var original = BackfillInventoryLoader.Load(Ledger(
            [],
            CasEntry("coarse-receipt", coarse, captured.Reference)));
        var adapterCandidate = BackfillInventoryLoader.Load(
            Ledger([], CasEntry("coarse-receipt", coarse, captured.Reference))
                .Replace(
                    $"atomizer: {priorAtomizer}",
                    $"atomizer: {AtomizerRegistry.ObserverId}",
                    StringComparison.Ordinal));
        var plan = DigestionIngestor.Plan(
            adapterCandidate,
            Snapshot(sourceBytes, [captured]),
            original);
        var settledBytes = Encoding.UTF8.GetString(
            BackfillInventoryWriter.WriteForIngest(plan.Document).AsSpan());
        var settled = BackfillInventoryLoader.Load(settledBytes);
        var revived = BackfillInventoryLoader.Load(settledBytes.Replace(
            "    acknowledged_stale:\n      - coarse-receipt\n",
            "    acknowledged_stale: []\n",
            StringComparison.Ordinal));

        var result = DigestionLedgerAligner.Evaluate(
            revived,
            Snapshot(sourceBytes, new[] { captured }.Concat(plan.CasObjects)),
            settled,
            DigestionAlignmentMode.Admission);

        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            result.AlignmentFor("coarse-receipt"));
        Assert.Contains(result.Findings, finding => finding.Contains(
            "stale receipts are not acknowledged: coarse-receipt",
            StringComparison.Ordinal));
    }
}
