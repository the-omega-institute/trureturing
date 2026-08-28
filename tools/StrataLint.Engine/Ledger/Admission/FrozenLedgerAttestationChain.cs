using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class FrozenLedgerAttestationChain
{
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
}
