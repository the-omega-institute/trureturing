using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static class InformationTemplateTheoremSelection
{
    // Only routing keys are inspected here. The existing strict collector checks
    // the selected occurrences, including foreign registrations and sidecars.
    internal static InformationTemplateUniverse Collect(RepositorySnapshot snapshot, LeanAxiomReport report,
        ImmutableHashSet<string> theorems)
    {
        var owners = ImmutableHashSet.CreateBuilder<RepoPath>();
        foreach (var (path, module) in report.Files)
        {
            if (module.InformationTemplates is not { ValueKind: JsonValueKind.Object } payload) continue;
            if (payload.TryGetProperty("inventory", out var inventory) && inventory.ValueKind == JsonValueKind.Array
                && inventory.EnumerateArray().Any(key => InformationTemplateSelection.IncludesTheorem(key, theorems)))
                owners.Add(path);
            if (!payload.TryGetProperty("records", out var records) || records.ValueKind != JsonValueKind.Array) continue;
            foreach (var record in records.EnumerateArray().Where(record => InformationTemplateSelection.HasTheorem(record, theorems)))
            {
                if (record.TryGetProperty("registration_source_path", out var owner) && owner.ValueKind == JsonValueKind.String
                    && RepoPath.TryCreate(owner.GetString()!, out var source)) owners.Add(source);
                else throw new FormatException("DTR-Evidence: selected theorem binding lacks its registration owner");
            }
        }
        return InformationTemplateEvidence.Collect(snapshot, report, owners, theorems);
    }
}
