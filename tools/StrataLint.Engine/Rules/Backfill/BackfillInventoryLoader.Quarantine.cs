namespace StrataLint.Engine;

internal static partial class BackfillInventoryLoader
{
    private static IEnumerable<string> EnumerateFormalizationReceiptPaths(string root)
    {
        var directory = Path.Combine(
            root,
            DigestionFormalizationReceipt.RootPath.Replace('/', Path.DirectorySeparatorChar));
        return Directory.Exists(directory)
            ? Directory.EnumerateFiles(directory, "*.v1.json", SearchOption.TopDirectoryOnly)
            : [];
    }

    private static void ValidateQuarantineMachineFormMarkers(
        RepositorySnapshot snapshot,
        BackfillInventoryDocument document)
    {
        foreach (var entry in document.RequireDigestionEntries())
        {
            ValidateQuarantineMachineFormMarker(snapshot, entry);
        }
    }

    private static void ValidateQuarantineMachineFormMarker(
        RepositorySnapshot snapshot,
        DigestionLedgerEntry entry)
    {
        if (entry.Receipts.Quarantine is null)
        {
            return;
        }

        var markerPath = DigestionFormalizationReceipt.PathForRawSha256(
            entry.Fingerprints.RawSha256);
        if (!snapshot.TryGetFile(markerPath, out _))
        {
            return;
        }

        var marker = DigestionFormalizationReceipt.Load(snapshot, markerPath);
        if (!string.Equals(marker.AtomId, entry.AtomId, StringComparison.Ordinal)
            || !string.Equals(marker.CasRef, entry.CasRef, StringComparison.Ordinal)
            || !string.Equals(
                marker.RawSha256,
                entry.Fingerprints.RawSha256,
                StringComparison.Ordinal))
        {
            throw new FormatException(
                $"entry {entry.AtomId} machine-form marker does not bind the current atom");
        }

        throw new FormatException(
            $"entry {entry.AtomId} cannot be quarantined because {markerPath} provides a machine-form statement");
    }
}
