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
    public static FrozenCoverageLoadOutcome Load(FrozenLedgerSyntax syntax)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        try
        {
            var active = new Dictionary<string, RepoPath>(StringComparer.Ordinal);
            var activePaths = new HashSet<RepoPath>();
            var sawGenesis = false;
            foreach (var line in syntax.Lines)
            {
                var root = line.Value;
                var eventType = RequiredString(root, "event_type");
                var payload = RequiredObject(root, "payload");
                if (!sawGenesis && eventType is "Freeze" or "Reattest" or "Supersede" or "Revoke")
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
                        // schema v4 retired the node_path alias; the authoritative path has
                        // always been input.descriptor_selector. Committed v2/v3 events keep
                        // the alias, so read the authority first and fall back for history.
                        var pathText = payload.TryGetProperty("input", out var freezeInput)
                            && freezeInput.TryGetProperty("descriptor_selector", out var selector)
                            && selector.ValueKind == JsonValueKind.String
                                ? selector.GetString()!
                                : RequiredString(payload, "node_path");
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
                    case "Reattest":
                        // Reattest 换 frozen_node_id(witness 含 source blob),路径不变。
                        // 不跟着换,后续 Revoke 指向新 id 时 active 表里没有它 ⟹ 整册被拒。
                        // v4 用正名 frozen_node_id;v2/v3 的 legacy 形只有别名 semantic_receipt。
                        var reattested = payload.TryGetProperty("frozen_node_id", out var freshNode)
                            && freshNode.ValueKind == JsonValueKind.String
                                ? freshNode.GetString()!
                                : RequiredString(payload, "semantic_receipt");
                        var reattestPath = RequiredString(
                            payload.GetProperty("input"), "descriptor_selector");
                        var priorNode = active.SingleOrDefault(item => item.Value.Value == reattestPath);
                        if (!FrozenHashSyntax.IsSha256(reattested)
                            || priorNode.Equals(default(KeyValuePair<string, RepoPath>))
                            || !active.Remove(priorNode.Key, out var reattestedPath)
                            || !active.TryAdd(reattested, reattestedPath))
                        {
                            throw new FormatException(
                                "Reattest has an invalid or inactive node identity");
                        }
                        break;
                    case "Supersede":
                        var caseId = RequiredString(payload, "case_id");
                        var newNodeId = RequiredString(payload, "frozen_node_id");
                        var oldNode = active.SingleOrDefault(item =>
                            item.Value.Value == RequiredString(payload.GetProperty("input"), "descriptor_selector"));
                        if (!FrozenHashSyntax.IsSha256(newNodeId)
                            || string.IsNullOrEmpty(caseId)
                            || oldNode.Equals(default(KeyValuePair<string, RepoPath>))
                            || !active.Remove(oldNode.Key, out var supersededPath)
                            || !active.TryAdd(newNodeId, supersededPath))
                        {
                            throw new FormatException(
                                "Supersede has an invalid or inactive node identity");
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

    private static JsonElement RequiredObject(JsonElement value, string property)
    {
        if (!value.TryGetProperty(property, out var result) || result.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException($"ledger event {property} must be an object");
        }

        return result;
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
