using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

// Owner projection reads addresses; Read validates selected evidence. Changed
// producers are validated before routing their claims to the exact owner join.
internal sealed class InformationTemplateSelection(ImmutableHashSet<string> sources,
    ImmutableHashSet<string>? theorems = null, ImmutableHashSet<InformationOccurrenceKey>? occurrences = null)
{
    internal static InformationTemplateUniverse CollectProducer(RepositorySnapshot snapshot, LeanAxiomReport report,
        RepoPath producer)
    {
        if (!report.Files.TryGetValue(producer, out var module) || module.Error is not null
            || module.InformationTemplates is not { } payload)
            throw new FormatException("DTR-Evidence: missing current producer for " + producer.Value);
        // Validate the selected producer before owner projection. In particular,
        // Read binds every overlay's binding_source_path to this actual producer.
        var evidence = InformationTemplateEvidence.Read(payload, producer.Value, snapshot);
        var own = InformationTemplateEvidence.Collect(snapshot, report, [producer]);
        var joined = own.Occurrences.ToBuilder();
        var inventory = own.Inventory.ToBuilder();
        foreach (var owner in evidence.Records.Where(record => record.RegistrationSourcePath != producer.Value)
            .GroupBy(record => record.RegistrationSourcePath, StringComparer.Ordinal))
        {
            var keys = owner.Select(record => record.Key).ToImmutableHashSet();
            // S imports M, so S need not be in M's import closure. The ordinary
            // strict join includes all claims for these exact occurrences, also
            // retaining competing claims rather than hiding duplicate evidence.
            var routed = InformationTemplateEvidence.Collect(snapshot, report,
                [RepoPath.CreateKnown(owner.Key)], occurrences: keys);
            joined.AddRange(routed.Occurrences);
            inventory.UnionWith(routed.Inventory);
        }
        return new(joined.ToImmutable(), inventory.ToImmutable());
    }

    internal static IEnumerable<RepoPath> ChangedProducers(DeltaRuleContext context) =>
        RepositoryRules.ChangedOrFirstPinD5Modules(context).Concat(context.Changes.Paths.Where(path =>
            IsRegSource(path) && context.Current.Files.TryGetValue(path, out var current)
            && (!context.Baseline.Files.TryGetValue(path, out var baseline)
                || !current.RawBytes.AsSpan().SequenceEqual(baseline.RawBytes.AsSpan()))))
        .Distinct().OrderBy(path => path.Value, StringComparer.Ordinal);

    internal static bool IsRegSource(RepoPath path) =>
        path.Value.StartsWith("Reg/", StringComparison.Ordinal) && path.Value.EndsWith(".lean", StringComparison.Ordinal);

    internal static bool HasTheorems(JsonElement value, ImmutableHashSet<string> names) =>
        value.ValueKind == JsonValueKind.Object && value.EnumerateObject().Any(property =>
            property.Value.ValueKind == JsonValueKind.Array && (property.Name switch
            {
                "inventory" or "registered" => property.Value.EnumerateArray().Any(key => IncludesTheorem(key, names)),
                "records" => property.Value.EnumerateArray().Any(record => HasTheorem(record, names)),
                _ => false,
            }));

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
                else if (property.Name is "inventory" or "registered" && (theorems is not null || occurrences is not null)
                    && property.Value.ValueKind == JsonValueKind.Array)
                {
                    writer.WriteStartArray();
                    foreach (var key in property.Value.EnumerateArray())
                        if (IncludesKey(key)) key.WriteTo(writer);
                    writer.WriteEndArray();
                }
                else if (property.Name == "records"
                    && property.Value.ValueKind == JsonValueKind.Array)
                {
                    writer.WriteStartArray();
                    foreach (var item in property.Value.EnumerateArray())
                    {
                        if (IncludesRecord(item, ownerSelected)) item.WriteTo(writer);
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
        if (theorems is not null && !HasTheorem(record, theorems)) return false;
        if (occurrences is not null && (record.ValueKind != JsonValueKind.Object
            || !record.TryGetProperty("key", out var occurrence) || !IncludesKey(occurrence))) return false;
        var source = String(record, "registration_source_path");
        var module = record.ValueKind == JsonValueKind.Object && record.TryGetProperty("key", out var key)
            ? String(key, "registration_module") : null;
        // Either selected address keeps the record: inconsistent addresses must
        // reach the strict reader, not hide a selected record in a foreign owner.
        return source is not null && sources.Contains(source) || module is not null && modules.Contains(module)
            || ownerSelected && source is null && module is null;
    }

    private bool IncludesKey(JsonElement key) =>
        (theorems is null || IncludesTheorem(key, theorems))
        && (occurrences is null || occurrences.Any(selected =>
            String(key, "root") == selected.Root && String(key, "registration_module") == selected.RegistrationModule
            && String(key, "theorem") == selected.Theorem && String(key, "object_arena") == selected.ObjectArena
            && String(key, "catalog") == selected.Catalog));

    internal static bool HasTheorem(JsonElement record, ImmutableHashSet<string> names) =>
        record.ValueKind == JsonValueKind.Object && record.TryGetProperty("key", out var key)
        && IncludesTheorem(key, names);

    internal static bool IncludesTheorem(JsonElement key, ImmutableHashSet<string> names) =>
        String(key, "theorem") is { } name && names.Contains(name);

    private static string? String(JsonElement value, string field) =>
        value.ValueKind == JsonValueKind.Object && value.TryGetProperty(field, out var item)
            && item.ValueKind == JsonValueKind.String && item.GetString() is { Length: > 0 } text ? text : null;
}
