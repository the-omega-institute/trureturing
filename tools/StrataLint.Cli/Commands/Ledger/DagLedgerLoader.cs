using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

public static class DagLedgerLoader
{
    public static DagLedgerFilesLoadOutcome LoadFiles(IEnumerable<RepositoryFile> files) =>
        FrozenAcceptedEventLoader.LoadFiles(files);

    internal static DagLedgerFilesLoadOutcome LoadTrustedFiles(IEnumerable<RepositoryFile> files) =>
        FrozenAcceptedEventLoader.LoadTrustedFiles(files);

    public static bool TryOrderClosedDag(
        ImmutableArray<DagLedgerFileEvent> events,
        ImmutableArray<string> preferredIdentityPrefix,
        out ImmutableArray<DagLedgerFileEvent> ordered)
    {
        var byIdentity = events.ToDictionary(static item => item.Identity, StringComparer.Ordinal);
        var remaining = events.OrderBy(static item => item.Identity, StringComparer.Ordinal).ToList();
        var result = ImmutableArray.CreateBuilder<DagLedgerFileEvent>(events.Length);
        var placedIdentities = new HashSet<string>(StringComparer.Ordinal);
        var placedHashes = new HashSet<string>(StringComparer.Ordinal);
        if (preferredIdentityPrefix.IsEmpty)
        {
            var genesis = events.Where(static item => item.EventType == "Genesis").ToArray();
            if (genesis.Length != 1)
            {
                ordered = ImmutableArray<DagLedgerFileEvent>.Empty;
                return false;
            }

            Place(genesis[0], remaining, result, placedIdentities, placedHashes);
        }

        foreach (var identity in preferredIdentityPrefix)
        {
            if (!byIdentity.TryGetValue(identity, out var item)
                || !CanPlace(item, result.Count, placedIdentities, placedHashes))
            {
                ordered = ImmutableArray<DagLedgerFileEvent>.Empty;
                return false;
            }

            Place(item, remaining, result, placedIdentities, placedHashes);
        }

        while (remaining.Count > 0)
        {
            var index = remaining.FindIndex(item =>
                CanPlace(item, result.Count, placedIdentities, placedHashes));
            if (index < 0)
            {
                ordered = ImmutableArray<DagLedgerFileEvent>.Empty;
                return false;
            }

            Place(remaining[index], remaining, result, placedIdentities, placedHashes);
        }

        ordered = result.MoveToImmutable();
        return true;
    }

    internal static bool TryOrderIncrementalDag(
        ImmutableArray<DagLedgerFileEvent> events,
        IReadOnlySet<string> knownIdentities,
        IReadOnlySet<string> knownHashes,
        out ImmutableArray<DagLedgerFileEvent> ordered)
    {
        var remaining = events.OrderBy(static item => item.Identity, StringComparer.Ordinal).ToList();
        var result = ImmutableArray.CreateBuilder<DagLedgerFileEvent>(events.Length);
        var placedIdentities = knownIdentities.ToHashSet(StringComparer.Ordinal);
        var placedHashes = knownHashes.ToHashSet(StringComparer.Ordinal);
        while (remaining.Count > 0)
        {
            var index = remaining.FindIndex(item =>
                CanPlace(item, placedCount: 1, placedIdentities, placedHashes));
            if (index < 0)
            {
                ordered = ImmutableArray<DagLedgerFileEvent>.Empty;
                return false;
            }

            Place(remaining[index], remaining, result, placedIdentities, placedHashes);
        }

        ordered = result.MoveToImmutable();
        return true;
    }

    private static bool CanPlace(
        DagLedgerFileEvent item,
        int placedCount,
        HashSet<string> placedIdentities,
        HashSet<string> placedHashes) =>
        item.EventType == "Genesis"
            ? placedCount == 0
            : DependenciesPlaced(item, placedIdentities, placedHashes);

    private static void Place(
        DagLedgerFileEvent item,
        List<DagLedgerFileEvent> remaining,
        ImmutableArray<DagLedgerFileEvent>.Builder ordered,
        HashSet<string> placedIdentities,
        HashSet<string> placedHashes)
    {
        remaining.Remove(item);
        ordered.Add(item);
        placedIdentities.Add(item.Identity);
        if (item.Payload.TryGetProperty("frozen_node_id", out var frozenNodeId)
            && frozenNodeId.ValueKind == JsonValueKind.String)
        {
            placedIdentities.Add(frozenNodeId.GetString()!);
        }
        placedHashes.Add(item.EventHash);
    }

    private static bool DependenciesPlaced(
        DagLedgerFileEvent item,
        HashSet<string> placedIdentities,
        HashSet<string> placedHashes)
    {
        if (item.EventType == "Freeze")
        {
            if (!item.Payload.TryGetProperty("prerequisite_frozen_node_ids", out var prerequisites)
                || prerequisites.ValueKind != JsonValueKind.Array)
            {
                return false;
            }

            return prerequisites.EnumerateArray().All(prerequisite =>
                prerequisite.ValueKind == JsonValueKind.String
                && placedIdentities.Contains(prerequisite.GetString()!));
        }

        if (item.EventType == "Revoke")
        {
            return item.Payload.TryGetProperty("evidence", out var evidence)
                && evidence.ValueKind == JsonValueKind.Array
                && evidence.EnumerateArray().All(entry =>
                    entry.ValueKind == JsonValueKind.Object
                    && entry.TryGetProperty("root_frozen_node_id", out var root)
                    && root.ValueKind == JsonValueKind.String
                    && placedIdentities.Contains(root.GetString()!));
        }

        return true;
    }

}
