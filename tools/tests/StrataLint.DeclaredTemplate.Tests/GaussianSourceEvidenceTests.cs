using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class GaussianSourceEvidenceTests
{
    [Fact]
    public void generated_gaussian_artifacts_pass_production_material_axiom_and_import_join()
    {
        var directory = Environment.GetEnvironmentVariable("GAUSSIAN_SOURCE_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused Gaussian native module artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        const string sourcePath = "D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticLimit.lean";
        var registration = RepoPath.CreateKnown("Reg/" + sourcePath);
        Assert.Equal("82443192d04cd30c222f5f914436c735e92f59c190461f508ceeec999d545e70",
            Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(Path.Combine(root, sourcePath)))));
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        using var scratch = new TemporaryDirectory();
        var artifacts = Directory.GetFiles(directory!, "*.zip");
        Assert.Equal(2, artifacts.Length);
        foreach (var artifact in artifacts)
        {
            var extracted = Path.Combine(scratch.Path, Path.GetFileNameWithoutExtension(artifact));
            ZipFile.ExtractToDirectory(artifact, extracted);
            var reportPath = Path.Combine(extracted, "raw-lean-report.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath));
            var row = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            var source = row.GetProperty("source_path").GetString()!;
            Assert.Contains(source, new[] { sourcePath, registration.Value });
            sources.Add(source, Source(source));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                RawRepositorySnapshot.Create([sources[source], Source("lean-report-inputs.json")]))).Snapshot;
            var file = RawLeanReportArtifact.ReadFile(reportPath, snapshot, validateMaterials: true)
                .Files[RepoPath.CreateKnown(source)];
            Assert.All(file.Declarations, declaration =>
            {
                Assert.NotEmpty(declaration.LoadTypeRepresentation());
                Assert.All(declaration.Axioms, axiom =>
                    Assert.Contains(axiom, new[] { "propext", "Classical.choice", "Quot.sound" }));
            });
            files.Add(source, file);
        }
        sources.Add("lean-report-inputs.json", Source("lean-report-inputs.json"));
        var joinedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(sources.Values))).Snapshot;
        var joined = InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(files), [registration]);
        Assert.True(Assert.Single(joined.Occurrences.Values).HasFourSlots);
        var wire = JsonNode.Parse(files[registration.Value].InformationTemplates!.Value.GetRawText())!;
        var record = Assert.Single(wire["records"]!.AsArray());
        Assert.Equal("declared_validated", record!["state"]!.GetValue<string>());
        Assert.Equal("source-equivalence", record["bridge_kind"]!.GetValue<string>());
        Assert.Equal("open", record["escape_continues"]!["kind"]!.GetValue<string>());
        var binding = record["certificate"]!["source_binding"]!;
        Assert.Equal(12, binding["telescope_size"]!.GetValue<int>());
        Assert.Equal(0, binding["level_count"]!.GetValue<int>());
        Assert.Equal(new[] { 0, 4, 5, 12, 13 },
            binding["coordinates"]!.AsArray().Select(n => n!.GetValue<int>()));
        var readout = Assert.Single(binding["readouts"]!.AsArray());
        Assert.Equal(14, readout!["state_binder"]!.GetValue<int>());
        Assert.Equal(15, readout["scope_size"]!.GetValue<int>());
        var compiled = JsonNode.Parse(File.ReadAllBytes(Path.Combine(root,
            ".lake/build/gaussian-source-evidence.json")))![0]!;
        Assert.True(JsonNode.DeepEquals(compiled, wire));

        // Actual current imports and materials, not a synthetic positive certificate.
        files.Remove(sourcePath);
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(files), [registration]));
        foreach (var mutation in new[] { "missing-n", "wrong-state", "wrong-actual" })
        {
            var changed = wire.DeepClone();
            var row = changed["records"]![0]!;
            var source = row["certificate"]!["source_binding"]!;
            switch (mutation)
            {
                case "missing-n": source["coordinates"] = new JsonArray(0, 4, 5, 13); break;
                case "wrong-state": source["readouts"]![0]!["state_binder"] = 13; break;
                case "wrong-actual": row["escape_from"]!["object_identity"] = new string('0', 64); break;
            }
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
                JsonSerializer.SerializeToElement(changed), registration.Value, joinedSnapshot));
        }
    }
}
