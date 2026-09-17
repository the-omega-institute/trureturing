using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

// Routing reads only owner addresses. Payload validation belongs to Read, after
// this projection; unrelated registrations never acquire an evidence obligation.
internal sealed class InformationTemplateSelection(ImmutableHashSet<string> sources)
{
    private readonly ImmutableHashSet<string> modules = sources
        .Select(InformationTemplateEvidence.ModuleForSource).ToImmutableHashSet(StringComparer.Ordinal);

    internal bool HasRecords(JsonElement value) =>
        value.ValueKind == JsonValueKind.Object
        && value.TryGetProperty("records", out var records) && records.ValueKind == JsonValueKind.Array
        && records.EnumerateArray().Any(record => IncludesRecord(record, ownerSelected: false));

    internal JsonElement Project(JsonElement value, string producer)
    {
        if (value.ValueKind != JsonValueKind.Object) return value;
        var ownerSelected = sources.Contains(producer);
        using var stream = new MemoryStream();
        using (var writer = new Utf8JsonWriter(stream))
        {
            writer.WriteStartObject();
            foreach (var property in value.EnumerateObject())
            {
                writer.WritePropertyName(property.Name);
                if (property.Name is "inventory" or "registered" && !ownerSelected)
                {
                    // These are the sidecar producer's own registrations.
                    writer.WriteStartArray();
                    writer.WriteEndArray();
                }
                else if (property.Name is "records" or "inventory" or "registered"
                    && property.Value.ValueKind == JsonValueKind.Array)
                {
                    writer.WriteStartArray();
                    foreach (var item in property.Value.EnumerateArray())
                    {
                        var included = property.Name == "records"
                            ? IncludesRecord(item, ownerSelected)
                            : String(item, "registration_module") is not { } module || modules.Contains(module);
                        if (included) item.WriteTo(writer);
                    }
                    writer.WriteEndArray();
                }
                else property.Value.WriteTo(writer);
            }
            writer.WriteEndObject();
        }
        using var document = JsonDocument.Parse(stream.ToArray());
        return document.RootElement.Clone();
    }

    private bool IncludesRecord(JsonElement record, bool ownerSelected)
    {
        var source = String(record, "registration_source_path");
        var module = record.ValueKind == JsonValueKind.Object && record.TryGetProperty("key", out var key)
            ? String(key, "registration_module") : null;
        // Either selected address keeps the record: inconsistent addresses must
        // reach the strict reader, not hide a selected record in a foreign owner.
        return source is not null && sources.Contains(source) || module is not null && modules.Contains(module)
            || ownerSelected && source is null && module is null;
    }

    private static string? String(JsonElement value, string field) =>
        value.ValueKind == JsonValueKind.Object && value.TryGetProperty(field, out var item)
            && item.ValueKind == JsonValueKind.String && item.GetString() is { Length: > 0 } text ? text : null;
}
