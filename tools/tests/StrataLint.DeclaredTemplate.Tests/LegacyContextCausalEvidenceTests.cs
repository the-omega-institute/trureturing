using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class LegacyContextCausalEvidenceTests
{
    private static readonly string[] Registrations = [
        "Reg/D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint/InformationRoot.lean",
        "Reg/D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint/TemplateShadow.lean",
        "Reg/D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation/InformationRoot.lean",
        "Reg/D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation/TemplateShadow.lean",
        "Reg/D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation/UnifiedCausalRegistration.lean",
        "Reg/D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation/UnifiedCausalRegistration.lean",
    ];

    // The opt-in data are current native :report zips, including actual type material.
    // The runner must report a skip as unverified, never as acceptance.
    [SkippableFact]
    public void historical_contexts_pass_native_materials_and_import_join_with_causal_gaps()
    {
        var directory = Environment.GetEnvironmentVariable("LEGACY_CONTEXT_CAUSAL_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused native artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        using var scratch = new TemporaryDirectory();
        foreach (var artifact in Directory.GetFiles(directory!, "*.zip").Order(StringComparer.Ordinal))
        {
            var extracted = Path.Combine(scratch.Path, Path.GetFileNameWithoutExtension(artifact));
            ZipFile.ExtractToDirectory(artifact, extracted);
            var reportPath = Path.Combine(extracted, "raw-lean-report.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath));
            var row = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            var source = row.GetProperty("source_path").GetString()!;
            sources.Add(source, Source(source));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                RawRepositorySnapshot.Create([sources[source], Source("lean-report-inputs.json")]))).Snapshot;
            var file = RawLeanReportArtifact.ReadFile(reportPath, snapshot, validateMaterials: true)
                .Files[RepoPath.CreateKnown(source)];
            var missingSource = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                RawRepositorySnapshot.Create([Source("lean-report-inputs.json")]))).Snapshot;
            Assert.Throws<FormatException>(() =>
                RawLeanReportArtifact.ReadFile(reportPath, missingSource, validateMaterials: true));
            if (source == "Reg/Support/LegacyContextReplacement.lean"
                || source == "Reg/Support/LegacyCausalCoordinates.lean"
                || source == "Reg/Support/LegacyCausalSlots.lean")
            {
                var text = File.ReadAllText(Path.Combine(root, source));
                var start = text.IndexOf("  Law r :=", StringComparison.Ordinal);
                var end = text.IndexOf("\ndef ", start, StringComparison.Ordinal);
                Assert.True(start >= 0 && end > start);
                var changedLaw = text[..start] + "  Law _ := True\n" + text[end..];
                var stale = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                    RawRepositorySnapshot.Create([
                        new(source, ImmutableArray.CreateRange(System.Text.Encoding.UTF8.GetBytes(changedLaw))),
                        Source("lean-report-inputs.json")]))).Snapshot;
                Assert.Throws<FormatException>(() =>
                    RawLeanReportArtifact.ReadFile(reportPath, stale, validateMaterials: true));
            }
            Assert.All(file.Declarations, declaration =>
            {
                Assert.NotEmpty(declaration.LoadTypeRepresentation());
                Assert.All(declaration.Axioms, axiom =>
                    Assert.Contains(axiom, new[] { "propext", "Classical.choice", "Quot.sound" }));
            });
            files.Add(source, file);
        }
        foreach (var required in new[] {
            "Reg/Support/LegacyContextReplacement.lean",
            "Reg/Support/LegacyCausalCoordinates.lean",
            "Reg/Support/LegacyCausalSlots.lean",
            "D5/S3/ConceptDynamics/Interpretation/InterpretationFixedPoint.lean",
            "D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation.lean",
            "D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation.lean",
        }) Assert.Contains(required, files.Keys);
        sources.Add("lean-report-inputs.json", Source("lean-report-inputs.json"));
        var joined = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(sources.Values))).Snapshot;
        var selected = Registrations.Select(RepoPath.CreateKnown).ToArray();
        var evidence = InformationTemplateEvidence.Collect(joined, LeanAxiomReport.Create(files), selected);
        Assert.Equal(6, evidence.Inventory.Count);
        Assert.Equal(2, evidence.Occurrences.Values.Count(occurrence => occurrence.HasFourSlots));
        foreach (var path in Registrations)
        {
            var wire = JsonNode.Parse(files[path].InformationTemplates!.Value.GetRawText())!;
            var record = Assert.Single(wire["records"]!.AsArray(),
                row => row!["registration_source_path"]!.GetValue<string>() == path)!;
            if (!path.Contains("InterpretationFixedPoint", StringComparison.Ordinal))
            {
                Assert.Equal("undeclared", record["state"]!.GetValue<string>());
                Assert.Null(record["certificate"]);
                continue;
            }
            Assert.Equal("declared_validated", record["state"]!.GetValue<string>());
            foreach (var mutation in new[] { "missing-certificate", "retargeted-certificate", "missing-unit" })
            {
                var changed = wire.DeepClone();
                var changedRecord = changed["records"]!.AsArray().Single(row =>
                    row!["registration_source_path"]!.GetValue<string>() == path)!;
                switch (mutation)
                {
                    case "missing-certificate": changedRecord["certificate"] = null; break;
                    case "retargeted-certificate":
                        changedRecord["certificate"]!["key"]!["object_arena"] = "Reg.Invalid.changedLaw";
                        break;
                    case "missing-unit": changedRecord["unit_name"] = "Reg.Invalid.missingUnit"; break;
                }
                var corrupted = new Dictionary<string, LeanFileReport>(files) {
                    [path] = files[path] with { InformationTemplates = JsonSerializer.SerializeToElement(changed) }
                };
                Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joined,
                    LeanAxiomReport.Create(corrupted), selected));
            }
            var missing = files.Where(pair => pair.Key != path)
                .ToDictionary(pair => pair.Key, pair => pair.Value);
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joined,
                LeanAxiomReport.Create(missing), selected));
        }
    }
}
