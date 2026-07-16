using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void IngestRebindsACasBackedNoAtomizerBoundaryToOneByteExactMatch()
    {
        var receiptBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var (ledger, captured) = CasBackedNoAtomizerLedger(receiptBytes);
        var sourceBytes = Encoding.UTF8.GetBytes("preface\nmanual specification receipt\nsuffix\n");

        var plan = DigestionIngestor.Plan(
            ledger,
            Snapshot(
                ("docs/source.md", sourceBytes),
                (captured.RelativePath, captured.Bytes.ToArray())),
            ledger);

        var boundary = Assert.Single(plan.Document.RequireDigestionEntries()).Boundary;
        Assert.Equal(new DigestionBoundary("manual/receipt", 8, 37), boundary);
        Assert.Empty(plan.CasObjects);
    }

    [Fact]
    public void IngestRejectsACasBackedNoAtomizerBoundaryWithoutItsCasBlob()
    {
        var receiptBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var (ledger, _) = CasBackedNoAtomizerLedger(receiptBytes);

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            ledger,
            Snapshot(("docs/source.md", receiptBytes)),
            ledger));

        Assert.Contains("CAS blob is missing", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRejectsAChangedCasBackedNoAtomizerBoundary()
    {
        var receiptBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var (ledger, captured) = CasBackedNoAtomizerLedger(receiptBytes);
        var changed = Encoding.UTF8.GetBytes("preface\nmanual specification changed\nsuffix\n");

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            ledger,
            Snapshot(
                ("docs/source.md", changed),
                (captured.RelativePath, captured.Bytes.ToArray())),
            ledger));

        Assert.Contains("no byte-exact match", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestRejectsAnAmbiguousCasBackedNoAtomizerBoundary()
    {
        var receiptBytes = Encoding.UTF8.GetBytes("manual specification receipt\n");
        var (ledger, captured) = CasBackedNoAtomizerLedger(receiptBytes);
        var ambiguous = receiptBytes.Concat(receiptBytes).ToArray();

        var exception = Assert.Throws<FormatException>(() => DigestionIngestor.Plan(
            ledger,
            Snapshot(
                ("docs/source.md", ambiguous),
                (captured.RelativePath, captured.Bytes.ToArray())),
            ledger));

        Assert.Contains("multiple byte-exact matches", exception.Message, StringComparison.Ordinal);
    }
}
