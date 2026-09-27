using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class LegacyAssignedTransportTests
{
    // The acceptance cases load native materials, declarations, imports and axiom closures.
    [SkippableFact]
    public void eight_original_occurrences_pass_native_join_and_reject_missing_or_retargeted_evidence()
    {
        var directory = Environment.GetEnvironmentVariable("LEGACY_ASSIGNED_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused native legacy artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        using var scratch = new TemporaryDirectory();
        var artifacts = Directory.GetFiles(directory!, "*.zip").Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(23, artifacts.Length);
        foreach (var artifact in artifacts)
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
            var report = RawLeanReportArtifact.ReadFile(reportPath, snapshot, validateMaterials: true);
            var file = report.Files[RepoPath.CreateKnown(source)];
            Assert.All(file.Declarations, declaration =>
            {
                Assert.NotEmpty(declaration.LoadTypeRepresentation());
                Assert.All(declaration.Axioms, axiom =>
                    Assert.Contains(axiom, new[] { "propext", "Classical.choice", "Quot.sound" }));
            });
            files.Add(source, file);
        }
        sources.Add("lean-report-inputs.json", Source("lean-report-inputs.json"));
        var joined = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(sources.Values))).Snapshot;
        var cases = new[] {
            (Path: "Aggregation/AgendaPower", Name: "agenda_power", Support: "LegacyAgenda"),
            (Path: "Coding/AdaptiveResidueIdentification", Name: "two_step_adaptive_residue_identification",
                Support: "LegacyResidue"),
            (Path: "ExperimentDesign/StaticExactExperimentDesign", Name: "static_exact_design",
                Support: "LegacyStaticDesign"),
            (Path: "Gluing/LocalLawGluingObstruction", Name: "compatible_local_laws_can_lack_global_state",
                Support: "LegacyGluing"),
        };
        var selected = cases.SelectMany(c => new[] { "InformationRoot", "TemplateShadow" }
            .Select(leaf => RepoPath.CreateKnown("Reg/D5/S3/ConceptDynamics/" + c.Path + "/" + leaf + ".lean")))
            .ToArray();
        var evidence = InformationTemplateEvidence.Collect(joined, LeanAxiomReport.Create(files), selected);
        Assert.Equal(8, evidence.Inventory.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        foreach (var item in cases)
        {
            var source = RepoPath.CreateKnown("D5/S3/ConceptDynamics/" + item.Path + ".lean");
            var name = "D5.S3.ConceptDynamics." + item.Path.Replace('/', '.') + "." + item.Name;
            var theorem = Assert.Single(files[source.Value].Declarations.Where(d => d.Name == name));
            Assert.Equal("theorem", theorem.Kind);
            foreach (var leaf in new[] { "InformationRoot", "TemplateShadow" })
            {
                var path = "Reg/" + source.Value[..^5] + "/" + leaf + ".lean";
                var owner = RepoPath.CreateKnown(path);
                var names = ImmutableHashSet.Create(name);
                var one = InformationTemplateTheoremSelection.Collect(joined,
                    LeanAxiomReport.Create(files), source, owner, names);
                Assert.Single(one.Occurrences);
                var wire = JsonNode.Parse(files[path].InformationTemplates!.Value.GetRawText())!;
                var record = Assert.Single(wire["records"]!.AsArray())!;
                Assert.Equal(name, record["key"]!["theorem"]!.GetValue<string>());
                Assert.Equal("Reg.Support." + item.Support + ".arena",
                    record["key"]!["object_arena"]!.GetValue<string>());
                Assert.Equal("declared_validated", record["state"]!.GetValue<string>());
                Assert.Equal("open", record["escape_continues"]!["kind"]!.GetValue<string>());
                foreach (var mutation in new[] { "certificate", "source", "arena" })
                {
                    var changed = wire.DeepClone();
                    var changedRecord = changed["records"]![0]!;
                    switch (mutation)
                    {
                        case "certificate": changedRecord["certificate"] = null; break;
                        case "source": changedRecord["key"]!["theorem"] = "D5.Other.result"; break;
                        case "arena": changedRecord["key"]!["object_arena"] = "Reg.Other.changedLaw"; break;
                    }
                    var changedFiles = new Dictionary<string, LeanFileReport>(files) {
                        [path] = files[path] with { InformationTemplates = JsonSerializer.SerializeToElement(changed) }
                    };
                    Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joined,
                        LeanAxiomReport.Create(changedFiles), selected));
                }
                foreach (var missingPath in new[] { source.Value, "Reg/Support/" + item.Support + ".lean" })
                {
                    var missing = files.Where(p => p.Key != missingPath).ToDictionary(p => p.Key, p => p.Value);
                    Assert.Throws<FormatException>(() => InformationTemplateTheoremSelection.Collect(joined,
                        LeanAxiomReport.Create(missing), source, owner, names));
                }
            }
        }
    }
}
