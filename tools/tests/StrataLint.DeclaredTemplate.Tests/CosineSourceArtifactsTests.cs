using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class CosineSourceArtifactsTests
{
    [Fact]
    public void OriginalCosineReportsPassProductionMaterialsAxiomsAndSourceJoin()
    {
        var directory = Environment.GetEnvironmentVariable("COSINE_SOURCE_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused native cosine reports were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        using var scratch = new TemporaryDirectory();
        var artifacts = Directory.GetFiles(directory!, "*.zip");
        Assert.Equal(6, artifacts.Length);
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
        const string prefix = "D5/S3/Fourier/Asymptotics/";
        var originals = new Dictionary<string, string>
        {
            ["CosineIntegralLattice"] = "e0d4dfd71fff6148ed327281e10e00eba7ac6b10bb74b32f0db75da35e73c684",
            ["CosineNormalizedRemainder"] = "18a9d7b6459793134253d1c16e78de919b5eb119c81bbe0f9456887cffd3ce48",
            ["CosineIntegralGram"] = "e5780e2f5a10d6a8b4181d20bd3617b9c775183eea45100b577bb4d1c6fd0f07"
        };
        var selected = originals.Keys.Select(name => RepoPath.CreateKnown("Reg/" + prefix + name + ".lean"))
            .ToArray();
        var evidence = InformationTemplateEvidence.Collect(joinedSnapshot, LeanAxiomReport.Create(files), selected);
        Assert.Equal(3, evidence.Inventory.Count);
        Assert.Equal(3, evidence.Occurrences.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        foreach (var (name, hash) in originals)
        {
            var source = prefix + name + ".lean";
            Assert.Equal(hash, Convert.ToHexStringLower(SHA256.HashData(Source(source).Bytes.AsSpan())));
            var wire = files["Reg/" + source].InformationTemplates!.Value;
            var record = Assert.Single(wire.GetProperty("records").EnumerateArray());
            var sourceName = (prefix + name).Replace('/', '.') + ".result";
            Assert.Equal(sourceName, record.GetProperty("key").GetProperty("theorem").GetString());
            Assert.Equal("declared_validated", record.GetProperty("state").GetString());
            Assert.Equal("source-equivalence", record.GetProperty("bridge_kind").GetString());
            Assert.Equal(sourceName, record.GetProperty("certificate").GetProperty("source_binding")
                .GetProperty("source_name").GetString());
            var incomplete = files.Where(pair => pair.Key != source)
                .ToDictionary(pair => pair.Key, pair => pair.Value);
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
                LeanAxiomReport.Create(incomplete), selected));
        }
    }
}
