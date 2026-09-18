using System.Text.Json.Nodes;
using StrataLint.TestSupport;

namespace StrataLint.Tests;

internal sealed partial class RuleFixture
{
    internal void RegisterLeanProducerInputs()
    {
        // Sparse fixtures use the authored producer patterns, with presence optional.
        // They do not introduce a second producer-selection heuristic.
        var declaration = JsonNode.Parse(TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("lean-report-inputs.json")))!;
        var manifest = JsonNode.Parse(Files["lean-report-inputs.json"])!;
        foreach (var name in new[] { "config_inputs", "inspector_sources" })
            manifest[name] = Optional(declaration[name]!);
        manifest["producer_scopes"]!["lean-report"] = Optional(declaration["producer_scopes"]!["lean-report"]!);
        Files["lean-report-inputs.json"] = manifest.ToJsonString();
        Files["Meta/ReportProducers/lean-report.json"] = """
            {"schema":"report-producer-scope-v2","registration":"lean-report-inputs.json","scope":"lean-report","projects":[]}
            """;

        static JsonNode Optional(JsonNode selection)
        {
            var copy = selection.DeepClone();
            foreach (var include in copy["include"]!.AsArray()) include!["optional"] = true;
            return copy;
        }
    }
}
