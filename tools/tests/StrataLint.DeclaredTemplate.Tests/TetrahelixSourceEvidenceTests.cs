using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class TetrahelixSourceEvidenceTests
{
    [Fact]
    public void original_source_native_artifacts_pass_production_consumer_and_frozen_identity()
    {
        var directory = Environment.GetEnvironmentVariable("TETRAHELIX_SOURCE_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused original/Reg native artifacts were not supplied.");
        const string owner = "D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions";
        var sourcePath = owner.Replace('.', '/') + ".lean";
        var registration = RepoPath.CreateKnown("Reg/" + sourcePath);
        var root = TestRepositoryLayout.FindRoot();
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
            var module = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            var source = module.GetProperty("source_path").GetString()!;
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
        Assert.Equal("b0b9950cbe5055e4067a07d5f6598995daa854b0157a8d8778d36470842d6740", Convert.ToHexStringLower(
            SHA256.HashData(sources[sourcePath].Bytes.AsSpan())));
        var path = RepoPath.CreateKnown(sourcePath);
        var statementId = FrozenContentHash.Compute(FrozenHashDomains.Statement,
            CanonicalStatementWriter.WriteModule(path,
                CanonicalStatementWriter.DeclarationStatementIds(path, files[sourcePath])).AsSpan());
        var pin = JsonNode.Parse(File.ReadAllBytes(Path.Combine(root,
            "Golden/Frozen/state/" + sourcePath + ".json")))!;
        Assert.Equal(pin["statement_id"]!.GetValue<string>(), statementId);
        sources.Add("lean-report-inputs.json", Source("lean-report-inputs.json"));
        var joinedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(sources.Values))).Snapshot;
        var joined = InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(files), [registration]);
        Assert.Single(joined.Inventory);
        Assert.True(Assert.Single(joined.Occurrences.Values).HasFourSlots);
        var wire = JsonNode.Parse(files[registration.Value].InformationTemplates!.Value.GetRawText())!;
        var row = Assert.Single(wire["records"]!.AsArray())!;
        Assert.Equal("declared_validated", row["state"]!.GetValue<string>());
        Assert.Equal("source-equivalence", row["bridge_kind"]!.GetValue<string>());
        Assert.Equal("open", row["escape_continues"]!["kind"]!.GetValue<string>());
        Assert.Equal(owner + ".result", row["key"]!["theorem"]!.GetValue<string>());
        Assert.Equal("Reg." + owner, row["key"]!["registration_module"]!.GetValue<string>());
        var binding = row["certificate"]!["source_binding"]!;
        Assert.Equal(owner, binding["source_owner"]!.GetValue<string>());
        Assert.Equal(owner + ".result", binding["source_name"]!.GetValue<string>());
        Assert.Equal(0, binding["telescope_size"]!.GetValue<int>());
        Assert.Equal(0, binding["level_count"]!.GetValue<int>());
        Assert.Equal(Array.Empty<int>(), binding["coordinates"]!.AsArray().Select(n => n!.GetValue<int>()));
        Assert.Single(binding["readouts"]!.AsArray());
        // A compiled mirror alone cannot certify an absent original theorem.
        var incomplete = files.Where(pair => pair.Key != sourcePath)
            .ToDictionary(pair => pair.Key, pair => pair.Value);
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(incomplete), [registration]));
        // The consumer must reject a changed actual/source tie in otherwise native evidence.
        row["escape_from"]!["object_identity"] = new string('0', 64);
        files[registration.Value] = files[registration.Value] with {
            InformationTemplates = JsonSerializer.SerializeToElement(wire) };
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(files), [registration]));
    }
}
