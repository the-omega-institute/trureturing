using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class LegacyRelationsNativeTests
{
    // Consume focused current native reports, including the actual retained units,
    // source declarations, finite bridges and family registration owners.
    [SkippableFact]
    public void five_original_occurrences_have_four_slots_and_reject_missing_or_retargeted_evidence()
    {
        var directory = Environment.GetEnvironmentVariable("LEGACY_RELATIONS_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused native artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        sources.Add("lean-report-inputs.json", Source("lean-report-inputs.json"));
        using var scratch = new TemporaryDirectory();
        var artifacts = Directory.GetFiles(directory!, "*.zip").Order(StringComparer.Ordinal).ToArray();
        Assert.NotEmpty(artifacts);
        foreach (var artifact in artifacts)
        {
            var extracted = Path.Combine(scratch.Path, Path.GetFileNameWithoutExtension(artifact));
            ZipFile.ExtractToDirectory(artifact, extracted);
            var reportPath = Path.Combine(extracted, "raw-lean-report.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath));
            var row = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            var source = row.GetProperty("source_path").GetString()!;
            sources.Add(source, Source(source));
            var snapshot = Decode([sources[source], sources["lean-report-inputs.json"]]);
            var report = RawLeanReportArtifact.ReadFile(reportPath, snapshot, validateMaterials: true);
            Assert.Throws<FormatException>(() => RawLeanReportArtifact.ReadFile(reportPath,
                Decode([sources["lean-report-inputs.json"]]), validateMaterials: true));
            var file = report.Files[RepoPath.CreateKnown(source)];
            Assert.All(file.Declarations, declaration =>
            {
                Assert.NotEmpty(declaration.LoadTypeRepresentation());
                Assert.All(declaration.Axioms, axiom =>
                    Assert.Contains(axiom, new[] { "propext", "Classical.choice", "Quot.sound" }));
            });
            files.Add(source, file);
        }
        string[] assigned = [
            "Reg/D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause/InformationRoot.lean",
            "Reg/D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause/TemplateShadow.lean",
            "Reg/D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange/InformationRoot.lean",
            "Reg/D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange/TemplateShadow.lean",
            "Reg/D5/S3/ConceptDynamics/InformationEscape/SystemUnit.lean"
        ];
        var joined = Decode(sources.Values);
        var selected = assigned.Select(RepoPath.CreateKnown).ToArray();
        var evidence = InformationTemplateEvidence.Collect(joined, LeanAxiomReport.Create(files), selected);
        Assert.Equal(5, evidence.Inventory.Count);
        Assert.Equal(5, evidence.Occurrences.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        AssertFiniteNamedReference(joined, files, selected);
        foreach (var path in assigned)
        {
            var wire = files[path].InformationTemplates!.Value;
            var row = Assert.Single(wire.GetProperty("records").EnumerateArray());
            Assert.Equal("declared_validated", row.GetProperty("state").GetString());
            Assert.Equal("source-equivalence", row.GetProperty("bridge_kind").GetString());
            var certificate = row.GetProperty("certificate");
            Assert.Equal(15, wire.GetProperty("compatibility_version").GetInt32());
            Assert.True(certificate.GetProperty("source_binding").TryGetProperty("finite_projection", out _));
            foreach (var mutation in new[] { "certificate", "source-owner", "source-name", "projection",
                "bridge", "arena-dependency", "path", "occurrence", "law-identity", "realization" })
            {
                var changed = JsonNode.Parse(wire.GetRawText())!;
                var record = changed["records"]![0]!;
                var binding = record["certificate"]!["source_binding"]!;
                switch (mutation)
                {
                    case "certificate": record["certificate"] = null; break;
                    case "source-owner": binding["source_owner"] = "D5.Wrong"; break;
                    case "source-name": binding["source_name"] = "D5.Wrong.result"; break;
                    case "projection": binding.AsObject().Remove("finite_projection"); break;
                    case "bridge": binding["finite_projection"]!["bridge"] = "D5.Wrong.bridge"; break;
                    case "arena-dependency":
                        var dependencies = record["certificate"]!["extraction_inputs"]!.AsArray();
                        dependencies.Remove(dependencies.Single(input => input!["name"]!.GetValue<string>()
                            == record["key"]!["object_arena"]!.GetValue<string>()));
                        break;
                    case "path": binding["readouts"]![0]!["path"] = new JsonArray("absent"); break;
                    case "occurrence": record["key"]!["catalog"] = "D5.Wrong.catalog"; break;
                    case "law-identity": record["statement_identity"] = new string('0', 64); break;
                    case "realization": record["realization_name"] = "D5.Wrong.actual"; break;
                }
                var mutated = new Dictionary<string, LeanFileReport>(files)
                {
                    [path] = files[path] with { InformationTemplates = JsonSerializer.SerializeToElement(changed) }
                };
                Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(
                    joined, LeanAxiomReport.Create(mutated), selected));
            }
            var source = certificate.GetProperty("source_binding").GetProperty("source_owner").GetString()!
                .Replace('.', '/') + ".lean";
            var support = path.Contains("EndStateOmitsPreemptingCause", StringComparison.Ordinal) ? "Preemption"
                : path.Contains("CommutingCompletionExchange", StringComparison.Ordinal) ? "Completion" : "System";
            var bridgeName = certificate.GetProperty("source_binding").GetProperty("finite_projection")
                .GetProperty("bridge").GetString();
            var bridgeOwner = certificate.GetProperty("extraction_inputs").EnumerateArray()
                .Single(input => input.GetProperty("name").GetString() == bridgeName)
                .GetProperty("owner").GetString()!.Replace('.', '/') + ".lean";
            foreach (var missingPath in new[] { source, $"Reg/Support/LegacyRelations/{support}.lean", bridgeOwner }.Distinct())
            {
                var missing = files.Where(pair => pair.Key != missingPath)
                    .ToDictionary(pair => pair.Key, pair => pair.Value);
                Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(
                    joined, LeanAxiomReport.Create(missing), selected));
            }
        }
        string[] predecessors = [
            "Reg/D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentScope/InformationRoot.lean",
            "Reg/D5/S3/ConceptDynamics/EscapeSpectrum/SpectrumCommitmentScope/TemplateShadow.lean",
            "Reg/D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation/InformationRoot.lean",
            "Reg/D5/S3/ConceptDynamics/Interventions/ObservationInterventionSeparation/TemplateShadow.lean"
        ];
        var preserved = InformationTemplateEvidence.Collect(joined, LeanAxiomReport.Create(files),
            predecessors.Select(RepoPath.CreateKnown));
        Assert.Equal(4, preserved.Occurrences.Count);
        Assert.All(preserved.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        Assert.All(new[] { "Reg/Catalogs/InformationRoot.lean", "Reg/Catalogs/TemplateShadow.lean" },
            catalog => Assert.True(files.ContainsKey(catalog)));
        foreach (var support in new[] { "Preemption", "Completion", "System" })
        {
            var path = $"Reg/Support/LegacyRelations/{support}.lean";
            Assert.Contains(files[path].Declarations, declaration =>
                declaration.Name == $"Reg.Support.LegacyRelations.{support}.registration");
        }
    }

    // Exercise the fusion against System's actual finite catalog projection.
    // These mutations retain internally consistent wire identities, so the
    // current raw declaration material must remain an independent check.
    private static void AssertFiniteNamedReference(RepositorySnapshot snapshot,
        Dictionary<string, LeanFileReport> files, RepoPath[] selected)
    {
        const string registration = "Reg/D5/S3/ConceptDynamics/InformationEscape/SystemUnit.lean";
        const string source = "D5/S3/ConceptDynamics/InformationEscape/SystemUnit.lean";
        var wire = files[registration].InformationTemplates!.Value;
        var original = Assert.Single(wire.GetProperty("records").EnumerateArray());
        var theoremName = original.GetProperty("key").GetProperty("theorem").GetString()!;
        var definitionName = original.GetProperty("certificate").GetProperty("source_binding")
            .GetProperty("definition_entry").GetProperty("name").GetString()!;
        var theorem = files[source].Declarations.Single(d => d.Name == theoremName);
        var definition = files[source].Declarations.Single(d => d.Name == definitionName);
        var material = theorem.LoadTypeRepresentation();
        Assert.StartsWith("statement-v1(uparams=[],type=ec(", material, StringComparison.Ordinal);
        foreach (var mutation in new[] { "reference", "universe", "retarget", "polarity",
            "material", "missing-material", "missing-definition", "definition-kind",
            "definition-material", "projection-owner", "projection-owner-duplicate" })
        {
            var changed = JsonNode.Parse(wire.GetRawText())!;
            var row = changed["records"]![0]!;
            var binding = row["certificate"]!["source_binding"]!;
            var entry = binding["definition_entry"]!;
            Assert.NotNull(binding["finite_projection"]);
            var candidates = new Dictionary<string, LeanFileReport>(files);
            var replacement = theorem;
            switch (mutation)
            {
                case "reference":
                    var wrong = new string('0', 64);
                    entry["reference_identity"] = wrong;
                    row["statement_identity"] = wrong;
                    binding["source_type_identity"] = wrong;
                    row["escape_from"]!["type_identity"] = wrong;
                    row["certificate"]!["extraction_inputs"]!.AsArray().Single(input =>
                        input!["name"]!.GetValue<string>() == theoremName)!["type_identity"] = wrong;
                    break;
                case "universe": binding["level_count"] = 1; break;
                case "retarget":
                    replacement = theorem with { TypeRepresentation = material.Replace(
                        definition.NameKey, "ns(n0,5:Other)", StringComparison.Ordinal) };
                    break;
                case "polarity":
                    const string prefix = "statement-v1(uparams=[],type=";
                    replacement = theorem with { TypeRepresentation = prefix
                        + "ea(ec(ns(n0,3:Not),[])," + material[prefix.Length..^1] + "))" };
                    break;
                case "material": replacement = theorem with { TypeRepresentation = "wrong-material" }; break;
                case "missing-material":
                    replacement = new(theorem.Name, theorem.Kind, "", theorem.Axioms) { NameKey = theorem.NameKey };
                    break;
                case "missing-definition":
                    candidates[source] = files[source] with { Declarations = files[source].Declarations
                        .Where(d => d.Name != definitionName).ToImmutableArray() };
                    break;
                case "definition-kind":
                case "definition-material":
                    var badDefinition = mutation == "definition-kind" ? definition with { Kind = "theorem" }
                        : definition with { TypeRepresentation = "statement-v1(uparams=[],type=es(ls(l0)),value=fixture)" };
                    candidates[source] = files[source] with { Declarations = files[source].Declarations
                        .Select(d => d.Name == definitionName ? badDefinition : d).ToImmutableArray() };
                    break;
                case "projection-owner":
                    var bridge = binding["finite_projection"]!["bridge"]!.GetValue<string>();
                    row["certificate"]!["extraction_inputs"]!.AsArray().Single(input =>
                        input!["name"]!.GetValue<string>() == bridge)!["owner"] = "D5.Wrong";
                    break;
                case "projection-owner-duplicate":
                    var bridgeName = binding["finite_projection"]!["bridge"]!.GetValue<string>();
                    candidates[source] = files[source] with { Declarations = files[source].Declarations.Add(
                        new(bridgeName, "def", "duplicate import owner", [])) };
                    break;
            }
            if (replacement != theorem)
                candidates[source] = files[source] with { Declarations = files[source].Declarations
                    .Select(d => d.Name == theoremName ? replacement : d).ToImmutableArray() };
            // Each mutation passes the closed wire shape before the actual
            // source/material/projection join rejects it.
            InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(changed), registration, snapshot);
            candidates[registration] = files[registration] with {
                InformationTemplates = JsonSerializer.SerializeToElement(changed) };
            var error = Record.Exception(() => InformationTemplateEvidence.Collect(snapshot,
                LeanAxiomReport.Create(candidates), selected));
            Assert.True(error is FormatException or InvalidDataException,
                $"finite named source accepted {mutation}: {error}");
        }
    }

    private static RepositorySnapshot Decode(IEnumerable<RawRepositoryEntry> entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;
}
