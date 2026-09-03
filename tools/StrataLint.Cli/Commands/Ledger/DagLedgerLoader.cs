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
        out ImmutableArray<DagLedgerFileEvent> ordered) =>
        TryOrderClosedDag(events, preferredIdentityPrefix, out ordered, out _);

    internal static bool TryOrderClosedDag(
        ImmutableArray<DagLedgerFileEvent> events,
        ImmutableArray<string> preferredIdentityPrefix,
        out ImmutableArray<DagLedgerFileEvent> ordered,
        out DagLedgerOrderingFailure? failure)
    {
        var byIdentity = events.ToDictionary(static item => item.Identity, StringComparer.Ordinal);
        var remaining = events.OrderBy(static item => item.Identity, StringComparer.Ordinal).ToList();
        var result = ImmutableArray.CreateBuilder<DagLedgerFileEvent>(events.Length);
        var placedIdentities = new HashSet<string>(StringComparer.Ordinal);
        var placedHashes = new HashSet<string>(StringComparer.Ordinal);
        foreach (var identity in preferredIdentityPrefix)
        {
            if (!byIdentity.TryGetValue(identity, out var item))
            {
                ordered = ImmutableArray<DagLedgerFileEvent>.Empty;
                failure = new DagLedgerOrderingFailure(identity, null, null, null);
                return false;
            }

            if (!CanPlace(item, placedIdentities))
            {
                ordered = ImmutableArray<DagLedgerFileEvent>.Empty;
                failure = FailureFor(item, placedIdentities);
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
                failure = FailureFor(remaining[0], placedIdentities);
                return false;
            }

            Place(remaining[index], remaining, result, placedIdentities, placedHashes);
        }

        ordered = result.MoveToImmutable();
        failure = null;
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

    private static DagLedgerOrderingFailure FailureFor(
        DagLedgerFileEvent item,
        HashSet<string> placedIdentities)
    {
        var unresolved = FrozenLedgerAttestationChain.RequiredStringArray(
                item.Payload,
                "prerequisite_frozen_node_ids")
            .Where(prerequisite => !placedIdentities.Contains(prerequisite))
            .Order(StringComparer.Ordinal)
            .FirstOrDefault() ?? item.Identity;
        return new DagLedgerOrderingFailure(
            unresolved,
            item.EventHash,
            item.DescriptorPath,
            item.SourcePath);
    }

}

internal sealed record DagLedgerOrderingFailure(
    string UnresolvedPrerequisiteIdentity,
    string? ReferencingEventHash,
    RepoPath? DescriptorPath,
    RepoPath? SourcePath)
{
    internal string Render() =>
        $"unresolved prerequisite identity {UnresolvedPrerequisiteIdentity}; "
        + $"referencing_event_hash={ReferencingEventHash ?? "<unavailable>"}; "
        + $"descriptor_selector={DescriptorPath?.Value ?? "<unavailable>"}; "
        + $"source_path={SourcePath?.Value ?? "<unavailable>"}";
}
