using System.Collections.Immutable;
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
        foreach (var identity in preferredIdentityPrefix)
        {
            if (!byIdentity.TryGetValue(identity, out var item)
                || !CanPlace(item, placedIdentities))
            {
                ordered = ImmutableArray<DagLedgerFileEvent>.Empty;
                return false;
            }

            Place(item, remaining, result, placedIdentities, placedHashes);
        }

        while (remaining.Count > 0)
        {
            var index = remaining.FindIndex(item =>
                CanPlace(item, placedIdentities));
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
                CanPlace(item, placedIdentities));
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
        HashSet<string> placedIdentities) =>
        item.EventType == "Freeze"
            && DependenciesPlaced(item, placedIdentities);

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
        placedIdentities.Add(item.FrozenNodeId.Value);
        placedHashes.Add(item.EventHash);
    }

    private static bool DependenciesPlaced(
        DagLedgerFileEvent item,
        HashSet<string> placedIdentities)
    {
        var prerequisites = FrozenLedgerAttestationChain.RequiredStringArray(
            item.Payload,
            "prerequisite_frozen_node_ids");
        return prerequisites.All(placedIdentities.Contains);
    }

}
