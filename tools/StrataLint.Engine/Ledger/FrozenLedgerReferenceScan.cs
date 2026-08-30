using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    private static readonly string[] FreezePayloadFields =
    [
        "declaration_statement_ids",
        "descriptor_selector",
        "prerequisite_frozen_node_ids",
        "statement_id",
    ];

    private static readonly string[] ReanchorPayloadFields =
    [
        "declaration_statement_ids",
        "descriptor_selector",
        "prerequisite_frozen_node_ids",
        "previous_event_hash",
        "statement_id",
    ];

    internal static RepoPath ParseAcceptedEventDescriptorPath(
        string eventType,
        JsonElement payload)
    {
        RequireEventPayloadFields(payload, eventType);
        var selector = RequiredString(payload, "descriptor_selector");
        return RepoPath.TryCreate(selector, out var path)
            ? path
            : throw new FormatException("Freeze descriptor_selector is not a canonical repository path.");
    }

    private static void RequireEventPayloadFields(JsonElement payload, string eventType)
    {
        var fields = eventType switch
        {
            "Freeze" => FreezePayloadFields,
            "Reanchor" => ReanchorPayloadFields,
            _ => throw new FormatException($"Unknown frozen event type {eventType}."),
        };

        RequireObjectFields(payload, $"{eventType} payload", fields);
    }
}
