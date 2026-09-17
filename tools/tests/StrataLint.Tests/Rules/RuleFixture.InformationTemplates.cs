using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed partial class RuleFixture
{
    // General rule fixtures have no information registrations. Supply the same
    // empty wire inventory as the current producer; explicit evidence is retained.
    private Dictionary<string, LeanFileReport> ReportsWithEmptyTemplateEvidence(RepositorySnapshot snapshot)
    {
        var inputs = snapshot.Files.Values.Where(file => file.Path.Value.StartsWith("D5/", StringComparison.Ordinal)
                && file.Path.Value.EndsWith(".lean", StringComparison.Ordinal)
                || file.Path.Value is "Trureturing.lean" or "lean-toolchain" or "lake-manifest.json" or "lean-report-inputs.json")
            .OrderBy(file => file.Path.Value, StringComparer.Ordinal)
            .Select(file => new InformationTemplateContentInput(file.Path.Value,
                InformationTemplateJson.Sha256(file.RawBytes.AsSpan()))).ToImmutableArray();
        using var manifest = JsonDocument.Parse(snapshot.Files[RepoPath.CreateKnown("lean-report-inputs.json")].Text);
        var wire = JsonSerializer.SerializeToElement(new
        {
            schema_version = 1,
            compatibility_version = manifest.RootElement.GetProperty("report_semantic_version").GetInt32(),
            inputs = inputs.Select(input => new { path = input.Path, sha256 = input.Sha256 }),
            inventory = Array.Empty<object>(), registered = Array.Empty<object>(), records = Array.Empty<object>(),
        });
        return Reports.ToDictionary(pair => pair.Key, pair => pair.Value.InformationTemplates is not null ? pair.Value
            : pair.Value with { InformationTemplates = new(wire, [], [], [], inputs) }, StringComparer.Ordinal);
    }
}
