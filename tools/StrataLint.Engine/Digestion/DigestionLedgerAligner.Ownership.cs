using System.Text.Json;

namespace StrataLint.Engine;

internal static partial class DigestionLedgerAligner
{
    private static HashSet<string> FindOwnedAtomIds(
        RepositorySnapshot snapshot,
        IEnumerable<string> ledgerAtomIds)
    {
        var ledgerIds = ledgerAtomIds.ToHashSet(StringComparer.Ordinal);
        var owned = new HashSet<string>(StringComparer.Ordinal);
        foreach (var (path, file) in snapshot.Files)
        {
            if (DigestionFormalizationReceipt.IsCanonicalPath(path.Value))
            {
                var atomId = path.Value[
                    DigestionFormalizationReceipt.RootPath.Length..
                    ^DigestionFormalizationReceipt.PathSuffix.Length];
                if (ledgerIds.Contains(atomId))
                {
                    owned.Add(atomId);
                }

                continue;
            }

            if (!FrozenLedgerChangeClassifier.IsAcceptedEventPath(path.Value))
            {
                continue;
            }

            try
            {
                using var document = JsonDocument.Parse(file.Text);
                FindExactAtomIdReferences(document.RootElement, ledgerIds, owned);
            }
            catch (JsonException exception)
            {
                throw new FormatException(
                    $"frozen ownership artifact is not valid JSON: {path.Value}",
                    exception);
            }
        }

        return owned;
    }

    private static void FindExactAtomIdReferences(
        JsonElement element,
        IReadOnlySet<string> ledgerAtomIds,
        ISet<string> owned)
    {
        switch (element.ValueKind)
        {
            case JsonValueKind.Object:
                foreach (var property in element.EnumerateObject())
                {
                    if (ledgerAtomIds.Contains(property.Name))
                    {
                        owned.Add(property.Name);
                    }

                    FindExactAtomIdReferences(property.Value, ledgerAtomIds, owned);
                }

                break;
            case JsonValueKind.Array:
                foreach (var item in element.EnumerateArray())
                {
                    FindExactAtomIdReferences(item, ledgerAtomIds, owned);
                }

                break;
            case JsonValueKind.String:
                var value = element.GetString();
                if (value is not null && ledgerAtomIds.Contains(value))
                {
                    owned.Add(value);
                }

                break;
        }
    }

    private static bool IsUnownedResidualOpen(
        DigestionLedgerEntry entry,
        IReadOnlySet<string> ownedAtomIds) =>
        entry.Boundary is null
        && entry.ProjectedStatus == new DigestionStatus(
            DigestionMigrationState.Residual,
            DigestionTruthState.Open)
        && entry.CoverageGids.IsEmpty
        && entry.Receipts.Coverage.IsEmpty
        && entry.Receipts.Scribe.IsEmpty
        && entry.Receipts.UnresolvedSubitems.IsEmpty
        && entry.Receipts.ChainAtoms.IsEmpty
        && entry.Receipts.TailAuthorization is null
        && entry.Receipts.Quarantine is null
        && !ownedAtomIds.Contains(entry.AtomId);

    private static bool CanAcknowledgeSupersededGeneration(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        IReadOnlySet<string> ownedAtomIds) =>
        entry.Boundary is null
        && (alignment == DigestionReceiptAlignment.Seen
                && IsUnownedResidualOpen(entry, ownedAtomIds)
            || entry.CoverageGids.Length > 0
            || entry.Receipts.Coverage.Length > 0
            || entry.Receipts.Scribe.Length > 0
            || entry.Receipts.UnresolvedSubitems.Length > 0
            || entry.Receipts.ChainAtoms.Length > 0
            || entry.Receipts.TailAuthorization is not null
            || entry.Receipts.Quarantine is not null
            || entry.Receipts.CoverDisposition is not null
            || ownedAtomIds.Contains(entry.AtomId));
}
