using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CurrentDeltaCliContractTests
{
    private static readonly InformationOccurrenceKey TemplateOccurrence = new(
        "D5.S0.Carrier.Ring", "D5.S0.Carrier.Ring", "goldenRing",
        "D5.S0.Carrier.Ring.arena", "D5.S0.Carrier.Ring.catalog");

    private static InformationTemplateContentInput TemplateInput(RepositorySnapshot snapshot, string path) => new(
        path, InformationTemplateJson.Sha256(snapshot.Files[RepoPath.CreateKnown(path)].RawBytes.AsSpan()));

    // Source-bound wire evidence for the existing fixture's goldenRing definition.
    // The integration fixture tests CLI handoff; no kernel-proof claim is made.
    private static LeanAxiomReport TemplateReport(RepositorySnapshot snapshot,
        IReadOnlyDictionary<string, LeanFileReport> reports, bool missingEvidence)
    {
        var inputs = snapshot.Files.Keys.Select(path => path.Value)
            .Where(path => path.StartsWith("D5/", StringComparison.Ordinal) && path.EndsWith(".lean", StringComparison.Ordinal)
                || path is "lean-report-inputs.json" or "lean-toolchain" or "lake-manifest.json")
            .Order(StringComparer.Ordinal).Select(path => TemplateInput(snapshot, path)).ToArray();
        return LeanAxiomReport.Create(reports.ToDictionary(pair => pair.Key, pair =>
        {
            if (!pair.Key.StartsWith("D5/", StringComparison.Ordinal)) return pair.Value;
            var own = pair.Key == RuleFixture.RingPath ? new[] { TemplateOccurrence } : [];
            var wire = JsonSerializer.SerializeToElement(new
            {
                schema_version = 1, compatibility_version = 6,
                inputs = inputs.Select(input => new { path = input.Path, sha256 = input.Sha256 }),
                inventory = own.Select(InformationTemplateJson.KeyJson),
                registered = own.Select(InformationTemplateJson.KeyJson),
                records = own.Select(key => new
                {
                    key = InformationTemplateJson.KeyJson(key), registration_source_path = RuleFixture.RingPath,
                    statement_identity = InformationTemplateJson.Sha256(System.Text.Encoding.UTF8.GetBytes(key.Theorem)),
                    content_inputs = new[] { TemplateInput(snapshot, RuleFixture.RingPath) }
                        .Select(input => new { path = input.Path, sha256 = input.Sha256 }),
                    binding_source_path = (string?)null, state = "undeclared",
                    diagnostic = $"IE-C050 ClosedTruthReadout key={key.Root}/{key.Catalog}/{key.Theorem} "
                        + "reason=unclassified_form rule=dtr.missing_declaration site=\"\" readout=\"\" "
                        + "provenance={\"argument_inputs\":[],\"extraction_inputs\":[],\"plan_identity\":null,"
                        + "\"rule\":\"dtr.missing_declaration\",\"site\":\"\",\"template_key\":null}",
                    escape_from = DeclaredTemplateEscapeRecordTests.FromSlot,
                    escape_continues = DeclaredTemplateEscapeRecordTests.OpenSlot, bridge_kind = "legacy",
                    unit_name = "goldenRing", realization_name = "goldenRing", certificate = (object?)null,
                }),
            });
            return pair.Value with
            {
                InformationTemplates = missingEvidence && pair.Key == RuleFixture.RingPath ? null : wire,
                InformationRegistrationErrors = ImmutableArray<string>.Empty,
            };
        }));
    }
}
