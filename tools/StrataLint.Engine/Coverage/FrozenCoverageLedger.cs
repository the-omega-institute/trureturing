using System.Collections.Immutable;
using System.Text.Json;
using Dunet;

namespace StrataLint.Engine;

[Union(EnableImplicitConversions = false)]
public partial record FrozenCoverageLoadOutcome
{
    public partial record Loaded(ImmutableArray<RepoPath> ActiveFrozenPaths);

    public partial record Invalid(string Message);
}

public static class FrozenCoverageLedger
{
    public static FrozenCoverageLoadOutcome Load(ImmutableArray<DagLedgerFileEvent> events)
    {
        if (events.IsDefault)
        {
            throw new ArgumentException("Frozen event set is uninitialized.", nameof(events));
        }
        try
        {
            var active = new Dictionary<string, RepoPath>(StringComparer.Ordinal);
            var activePaths = new HashSet<RepoPath>();
            var sawGenesis = false;
            foreach (var item in events)
            {
                var eventType = item.EventType;
                var payload = item.Payload;
                if (!sawGenesis && eventType != "Genesis")
                {
                    throw new FormatException($"{eventType} event occurs before Genesis");
                }
                switch (eventType)
                {
                    case "Genesis":
                        if (sawGenesis || active.Count > 0)
                        {
                            throw new FormatException("duplicate or noninitial Genesis event");
                        }
                        sawGenesis = true;
                        break;
                    case "Freeze":
                        var nodeId = RequiredString(payload, "frozen_node_id");
                        var pathText = RequiredString(
                            payload.GetProperty("input"),
                            "descriptor_selector");
                        if (!FrozenHashSyntax.IsSha256(nodeId)
                            || !RepoPath.TryCreate(pathText, out var path)
                            || !active.TryAdd(nodeId, path))
                        {
                            throw new FormatException("Freeze has an invalid path or duplicate node id");
                        }
                        if (!activePaths.Add(path))
                        {
                            throw new FormatException($"Freeze has a duplicate path {path.Value}");
                        }
                        break;
                    case "Revoke":
                        foreach (var node in RequiredStrings(payload, "affected_frozen_node_ids"))
                        {
                            if (!active.Remove(node, out var revokedPath))
                            {
                                throw new FormatException($"Revoke targets inactive frozen node {node}");
                            }
                            activePaths.Remove(revokedPath);
                        }
                        break;
                    case "Reattest":
                        break;
                    default:
                        throw new FormatException($"unknown event type {eventType}");
                }
            }

            if (!sawGenesis)
            {
                throw new FormatException("frozen ledger has no Genesis event");
            }

            return new FrozenCoverageLoadOutcome.Loaded(
                activePaths.OrderBy(static path => path.Value, StringComparer.Ordinal).ToImmutableArray());
        }
        catch (Exception exception) when (exception is FormatException or InvalidOperationException)
        {
            return new FrozenCoverageLoadOutcome.Invalid(exception.Message);
        }
    }

    private static string RequiredString(JsonElement value, string property)
    {
        if (!value.TryGetProperty(property, out var result)
            || result.ValueKind != JsonValueKind.String
            || string.IsNullOrEmpty(result.GetString()))
        {
            throw new FormatException($"ledger event {property} must be a string");
        }

        return result.GetString()!;
    }

    private static IEnumerable<string> RequiredStrings(JsonElement value, string property)
    {
        if (!value.TryGetProperty(property, out var result) || result.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException($"ledger event {property} must be an array");
        }

        foreach (var item in result.EnumerateArray())
        {
            if (item.ValueKind != JsonValueKind.String || string.IsNullOrEmpty(item.GetString()))
            {
                throw new FormatException($"ledger event {property} entries must be strings");
            }

            yield return item.GetString()!;
        }
    }
}
