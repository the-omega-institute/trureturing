using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Scribe;

internal sealed record ReceiptFreeDocumentCensus(
    ImmutableHashSet<string> ReceiptFreeDocumentGids,
    ImmutableHashSet<string> ReceiptBoundDocumentGids);

internal static class ReceiptFreeDocumentCatalog
{
    internal static ReceiptFreeDocumentCensus Load(
        string repositoryRoot,
        IEnumerable<ScribeDocument> documents,
        bool tolerateAbsentDocuments = false)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(documents);
        var documentGids = documents
            .Select(static document => document.Header.Gid.Value)
            .ToImmutableHashSet(StringComparer.Ordinal);
        if (documentGids.IsEmpty)
        {
            throw new InvalidOperationException("Scribe document corpus must not be empty.");
        }

        var inventory = BackfillInventoryLoader.LoadTrustedRoot(repositoryRoot);
        var receiptBound = inventory.RequireDigestionEntries()
            .SelectMany(static entry => entry.Receipts.Scribe)
            .Select(static receipt => ScribeEmissionAttestation.DocumentGid(receipt.Gid))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var unknown = receiptBound.Except(documentGids, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (!tolerateAbsentDocuments && unknown.Length > 0)
        {
            throw new InvalidOperationException(
                $"BACKFILL Scribe receipts target unknown documents: {string.Join(", ", unknown)}");
        }

        return new ReceiptFreeDocumentCensus(
            documentGids.Except(receiptBound, StringComparer.Ordinal)
                .ToImmutableHashSet(StringComparer.Ordinal),
            receiptBound.Intersect(documentGids, StringComparer.Ordinal)
                .ToImmutableHashSet(StringComparer.Ordinal));
    }
}
