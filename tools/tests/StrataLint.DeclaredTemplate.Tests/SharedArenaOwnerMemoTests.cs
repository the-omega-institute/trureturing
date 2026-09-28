using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class SharedArenaOwnerMemoTests
{
    [SkippableFact]
    public void original_finite_registration_and_real_catalog_pass_strict_native_consumers()
    {
        var directory = Environment.GetEnvironmentVariable("SHARED_ARENA_NATIVE");
        Skip.If(string.IsNullOrEmpty(directory), "Supply current scoped SharedArena native reports.");
        const string source = "D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation.lean";
        const string registration = "Reg/D5/S3/ConceptDynamics/Interventions/InterventionCounterfactualSeparation/SharedArenaPeers.lean";
        const string catalog = "Reg/Catalogs/SharedArenaPeers.lean";
        const string theorem = "D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual";
        const string unit = theorem + ".«Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit";
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry ReadSource(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        sources.Add("lean-report-inputs.json", ReadSource("lean-report-inputs.json"));
        using var scratch = new TemporaryDirectory();
        foreach (var artifact in Directory.GetFiles(directory!, "*.zip").Order(StringComparer.Ordinal))
        {
            var extracted = Path.Combine(scratch.Path, Path.GetFileNameWithoutExtension(artifact));
            ZipFile.ExtractToDirectory(artifact, extracted);
            var path = Path.Combine(extracted, "raw-lean-report.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(path));
            var row = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            var owner = row.GetProperty("source_path").GetString()!;
            sources.Add(owner, ReadSource(owner));
            var file = RawLeanReportArtifact.ReadFile(path,
                Decode([sources[owner], sources["lean-report-inputs.json"]]), validateMaterials: true)
                .Files[RepoPath.CreateKnown(owner)];
            Assert.All(file.Declarations, declaration =>
            {
                Assert.NotEmpty(declaration.LoadTypeRepresentation());
                Assert.All(declaration.Axioms, axiom =>
                    Assert.Contains(axiom, new[] { "propext", "Classical.choice", "Quot.sound" }));
            });
            files.Add(owner, file);
        }
        var snapshot = Decode(sources.Values);
        var report = LeanAxiomReport.Create(files);
        var complete = Path.Combine(scratch.Path, "complete.json");
        RawLeanReportArtifact.WriteFile(complete, snapshot, report);
        report = RawLeanReportArtifact.ReadFile(complete, snapshot, validateMaterials: true);
        // The selected production owner determines its required import closure.
        // The real catalog is additionally consumed as a native material artifact.
        Assert.NotEmpty(LeanImportClosure.RepositoryPaths(report, RepoPath.CreateKnown(registration)));
        var selected = new[] { RepoPath.CreateKnown(registration) };
        var evidence = InformationTemplateEvidence.Collect(snapshot, report, selected);
        Assert.True(Assert.Single(evidence.Occurrences.Values).HasFourSlots);
        var binding = Assert.Single(files[registration].InformationTemplates!.Value
            .GetProperty("records").EnumerateArray());
        Assert.Equal("declared_validated", binding.GetProperty("state").GetString());
        Assert.Equal(theorem, binding.GetProperty("key").GetProperty("theorem").GetString());
        Assert.Equal("finiteProbe", binding.GetProperty("key").GetProperty("catalog").GetString());
        Assert.Equal("f71d521d981aac97aee79978fb26007cfea2622d673c463ebc8203611dca5be4",
            binding.GetProperty("statement_identity").GetString());
        Assert.Equal(unit, binding.GetProperty("unit_name").GetString());
        Assert.Contains(files[registration].Declarations, declaration => declaration.Name == unit);
        Assert.Contains(files[source].Declarations, declaration => declaration.Name == theorem);
        Assert.Contains(files[catalog].Declarations, declaration => declaration.Name.EndsWith(
            ".interventionCatalog", StringComparison.Ordinal));
        Assert.Contains(unit, File.ReadAllText(Path.Combine(root, catalog)), StringComparison.Ordinal);
        foreach (var missing in new[] { source, registration, "Reg/Support/SharedArenaPeers.lean" })
        {
            // Corrupt the valid wire, retaining the complete expected snapshot and
            // material archive so this reaches the strict reader's completeness check.
            var incomplete = JsonNode.Parse(File.ReadAllBytes(complete))!;
            var modules = incomplete["modules"]!.AsArray();
            modules.Remove(Assert.Single(modules, module =>
                module!["source_path"]!.GetValue<string>() == missing));
            var incompletePath = Path.Combine(scratch.Path, "missing.json");
            File.WriteAllBytes(incompletePath,
                StructuredCanonicalWriter.WriteJson(incomplete.ToJsonString()).ToArray());
            File.Copy(RawLeanReportArtifact.MaterialsPath(complete),
                RawLeanReportArtifact.MaterialsPath(incompletePath), overwrite: true);
            var error = Assert.Throws<FormatException>(() => RawLeanReportArtifact.ReadFile(
                incompletePath, snapshot, validateMaterials: true));
            Assert.Equal("Raw Lean report is missing modules: " + missing, error.Message);
        }
        // Independently exercise the collector's required registration-owner check.
        var missingRegistration = files.Where(pair => pair.Key != registration)
            .ToDictionary(pair => pair.Key, pair => pair.Value);
        var producerError = Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(
            snapshot, LeanAxiomReport.Create(missingRegistration), selected));
        Assert.Equal("DTR-Evidence: missing current producer for " + registration, producerError.Message);
    }

    private static RepositorySnapshot Decode(IEnumerable<RawRepositoryEntry> entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;
}
