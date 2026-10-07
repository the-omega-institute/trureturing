using static StrataLint.TestSupport.DigestionAlignmentFixture;
using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Digestion.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void IngestRejectsAtomizerHashFailureInsteadOfFallingBack()
    {
        var (ledger, oldCapture) = ExistingCasBackedLedger();
        var sourceBytes = ImmutableArray.Create((byte)'a');
        var corrupt = new DigestionAtom(
            0,
            1,
            sourceBytes,
            new DigestionFingerprints(
                "sha256:" + new string('0', 64),
                "sha256:" + new string('0', 64)),
            []);
        var corruptDocument = new AtomizedTheoryDocument(
            [corrupt],
            [new DigestionSlice(true, sourceBytes)],
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => corruptDocument);

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
            0,
            1,
            fabricatedBytes,
            DigestionFingerprint.Compute(fabricatedBytes.AsSpan()),
            []);
        var fabricatedDocument = new AtomizedTheoryDocument(
            [fabricated],
            [new DigestionSlice(true, sourceBytes)],
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => fabricatedDocument);

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
            [new DigestionSlice(false, ImmutableArray.Create((byte)'b'))],
            GenreRegistryCheck.NoGenreRegistry);

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            Snapshot(sourceBytes.ToArray(), [oldCapture]),
            DigestionAlignmentMode.Ingest,
            _ => (_, _) => corrupt);

        Assert.Empty(result.Fallbacks);
        Assert.Empty(result.Residual);
        Assert.Contains(result.Findings, finding =>
            finding.Contains("reassemble", StringComparison.OrdinalIgnoreCase));
    }

    [Fact]
    public void IngestDoesNotRetireCoarseReceiptForFineReceiptWithoutRegisteredAdapter()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# Legacy\n\nfine claim\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var fineBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("fine claim"));
        var fineStart = sourceBytes.AsSpan().IndexOf(fineBytes.AsSpan());
        var fine = new DigestionAtom(
            fineStart,
            fineStart + fineBytes.Length,
            fineBytes,
            DigestionFingerprint.Compute(fineBytes.AsSpan()),
            []);
        var coarseCapture = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var fineCapture = DigestionCasStore.Capture(fineBytes.AsSpan());
        var ledger = WithAtomizer(
            Ledger(
                [],
                CasEntry("coarse-receipt", coarse, coarseCapture.Reference),
                CasEntry("fine-receipt", fine, fineCapture.Reference)),
            AtomizerRegistry.NoAtomizerId);

        var plan = ReportFreeDigestionIngestor.Plan(
            ledger,
            Snapshot(sourceBytes, [coarseCapture, fineCapture]));

        var source = Assert.Single(plan.Document.RequireDigestionSources());
        Assert.Empty(source.AcknowledgedStale);
        Assert.Contains(source.Entries, entry => entry.AtomId == AtomId(coarse));
        Assert.Contains(source.Entries, entry => entry.AtomId == AtomId(fine));
    }

    [Fact]
    public void IngestPreservesFineGenerationRetirementAcknowledgment()
    {
        var (sourceBytes, coarseCapture, fineCapture, ledger) = MissedCoarseReplacement();
        var snapshot = Snapshot(sourceBytes, [coarseCapture, fineCapture]);
        var first = ReportFreeDigestionIngestor.Plan(ledger, snapshot);
        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        using var temporary = new TemporaryDirectory();
        var persisted = new Dictionary<string, string>(StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(persisted, first.Document);
        DirectoryLedgerTestSupport.Write(temporary.Path, persisted);
        var settled = BackfillInventoryLoader.LoadRoot(temporary.Path);

        var second = ReportFreeDigestionIngestor.Plan(settled, snapshot);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Equal(firstBytes, secondBytes);
    }
    private static (
        byte[] SourceBytes,
        DigestionCasObject CoarseCapture,
        DigestionCasObject FineCapture,
        BackfillInventoryDocument Ledger) MissedCoarseReplacement()
    {
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n**\u5b9a\u7406(\u89c2\u5bdf\u8005\u4ee3\u6570\u7684\u552f\u4e00\u5f62\u6001)\u3002** claim\u3002\n");
        var coarseBytes = ImmutableArray.CreateRange(sourceBytes);
        var coarse = new DigestionAtom(
            0,
            sourceBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var fine = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.ObserverId,
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var coarseCapture = DigestionCasStore.Capture(coarseBytes.AsSpan());
        var fineCapture = DigestionCasStore.Capture(fine.RawBytes.AsSpan());
        var ledger = WithAtomizer(
            Ledger(
                [],
                CasEntry("coarse-receipt", coarse, coarseCapture.Reference),
                CasEntry("fine-receipt", fine, fineCapture.Reference)),
            AtomizerRegistry.ObserverId);
        return (sourceBytes, coarseCapture, fineCapture, ledger);
    }
}
