using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class SourceV15TriggerTests
{
    // Always executes in the registered test project. SourceV15Trigger.lean checks
    // these native report wires against the current compiler's two real occurrences.
    [Fact]
    public void v15_allow_originals_pass_native_material_axiom_and_import_join()
    {
        var root = TestRepositoryLayout.FindRoot();
        using var fixture = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(root,
            "tools/tests/StrataLint.DeclaredTemplate.Tests/SourceV15Trigger.json")));
        using var scratch = new TemporaryDirectory();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        sources.Add("lean-report-inputs.json", Source("lean-report-inputs.json"));
        foreach (var artifact in fixture.RootElement.GetProperty("native").EnumerateArray())
        {
            var directory = Path.Combine(scratch.Path, artifact.GetProperty("module").GetString()!);
            using var stream = new MemoryStream(Convert.FromBase64String(
                artifact.GetProperty("archive_base64").GetString()!));
            using var zip = new ZipArchive(stream);
            zip.ExtractToDirectory(directory);
            var reportPath = Path.Combine(directory, "raw-lean-report.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath));
            var module = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            Assert.Equal(artifact.GetProperty("module").GetString(), module.GetProperty("module").GetString());
            var path = module.GetProperty("source_path").GetString()!;
            sources.Add(path, Source(path));
            var snapshot = Decode([sources[path], sources["lean-report-inputs.json"]]);
            var report = RawLeanReportArtifact.ReadFile(reportPath, snapshot, validateMaterials: true);
            var file = report.Files[RepoPath.CreateKnown(path)];
            Assert.All(file.Declarations, declaration =>
            {
                Assert.NotEmpty(declaration.LoadTypeRepresentation());
                Assert.All(declaration.Axioms, axiom =>
                    Assert.Contains(axiom, new[] { "propext", "Classical.choice", "Quot.sound" }));
            });
            files.Add(path, file);
        }
        var selected = fixture.RootElement.GetProperty("wires").EnumerateArray().Select(wire =>
        {
            Assert.Equal(15, wire.GetProperty("compatibility_version").GetInt32());
            var record = Assert.Single(wire.GetProperty("records").EnumerateArray());
            var path = record.GetProperty("registration_source_path").GetString()!;
            Assert.True(JsonElement.DeepEquals(wire, files[path].InformationTemplates!.Value));
            Assert.Equal("declared_validated", record.GetProperty("state").GetString());
            Assert.Equal("source-equivalence", record.GetProperty("bridge_kind").GetString());
            var binding = record.GetProperty("certificate").GetProperty("source_binding");
            Assert.True(binding.TryGetProperty("finite_projection", out _));
            Assert.Contains(binding.GetProperty("readouts").EnumerateArray(), readout =>
                readout.TryGetProperty("function_operand", out var function) && function.GetBoolean());
            if (path.Contains("EndStateOmitsPreemptingCause", StringComparison.Ordinal))
                Assert.Equal(2, binding.GetProperty("readouts").EnumerateArray().Count(readout =>
                    readout.TryGetProperty("state_operand", out _) &&
                    readout.GetProperty("boolean_predicate").GetBoolean()));
            return RepoPath.CreateKnown(path);
        }).ToArray();
        var joined = Decode(sources.Values);
        var evidence = InformationTemplateEvidence.Collect(joined, LeanAxiomReport.Create(files), selected);
        Assert.Equal(2, evidence.Inventory.Count);
        Assert.Equal(2, evidence.Occurrences.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        // A native join must require its original source, family support, arena and bridge owners.
        foreach (var missing in files.Keys.Where(path => !selected.Contains(RepoPath.CreateKnown(path))))
        {
            var incomplete = files.Where(pair => pair.Key != missing).ToDictionary(pair => pair.Key, pair => pair.Value);
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joined,
                LeanAxiomReport.Create(incomplete), selected));
        }
    }

    private static RepositorySnapshot Decode(IEnumerable<RawRepositoryEntry> entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;
}
