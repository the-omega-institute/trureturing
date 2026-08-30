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

        var markerPath = DigestionFormalizationReceipt.PathForAtom(entry.AtomId);
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

        throw new DigestionQuarantineConflictException(
            entry.AtomId,
            $"entry {entry.AtomId} cannot be quarantined because {markerPath} provides a machine-form statement");
    }
}

/// <summary>
/// 「已隔离的原子同时持有机器形式陈述(收据 / coverage_gids)」这一互斥由 loader 执法;它以**类型**而非散文暴露,
/// 使消费者(如 review-envelope)能把它映射为自己的典型结果,而不必解析消息文本(#4163 第 4/5 轮评审)。
/// 仍是 FormatException 的子类:所有既有 catch 过滤器行为不变。
/// </summary>
internal sealed class DigestionQuarantineConflictException(string atomId, string message) : FormatException(message)
{
    internal string AtomId { get; } = atomId;
}
