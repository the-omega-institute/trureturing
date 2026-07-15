using System.Collections.Immutable;
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
}
