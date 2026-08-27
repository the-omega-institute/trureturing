using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class FrozenLedgerAttestationChain
{
    internal static ImmutableArray<TrustedFrozenLedgerEvent> ActiveAttestations(
        ImmutableArray<TrustedFrozenLedgerEvent> events)
    {
        var predecessors = events
            .Where(static item => item.EventType == "Reattest")
            .Select(static item => RequiredString(
                item.Payload,
                "previous_attestation_event_hash"))
            .ToImmutableHashSet(StringComparer.Ordinal);
        return events
            .Where(static item => item.EventType is "Freeze" or "Reattest")
            .Where(item => !predecessors.Contains(item.EventHash))
            .ToImmutableArray();
    }

    internal static string RequiredString(JsonElement value, string property) =>
        value.TryGetProperty(property, out var child) && child.ValueKind == JsonValueKind.String
            ? child.GetString()
                ?? throw new FormatException($"trusted frozen ledger field {property} is null")
            : throw new FormatException($"trusted frozen ledger field {property} is not a string");

    internal static int RequiredInteger(JsonElement value, string property) =>
        value.TryGetProperty(property, out var child) && child.TryGetInt32(out var result)
            ? result
            : throw new FormatException($"trusted frozen ledger field {property} is not an integer");

    internal static ImmutableArray<string> RequiredStringArray(JsonElement value, string property)
    {
        if (!value.TryGetProperty(property, out var child) || child.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException($"trusted frozen ledger field {property} is not an array");
        }

        return child.EnumerateArray().Select(item => item.ValueKind == JsonValueKind.String
            ? item.GetString()
                ?? throw new FormatException($"trusted frozen ledger field {property} contains null")
            : throw new FormatException($"trusted frozen ledger field {property} contains a non-string"))
            .ToImmutableArray();
    }

    internal static ImmutableArray<string> OptionalStringArray(JsonElement value, string property) =>
        value.TryGetProperty(property, out _)
            ? RequiredStringArray(value, property)
            : ImmutableArray<string>.Empty;
}
