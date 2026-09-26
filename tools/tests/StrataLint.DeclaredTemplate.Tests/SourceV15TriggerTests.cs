using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class SourceV15TriggerTests
{
    // Always executes in the registered test project. SourceV15Trigger.lean checks
    // these native report wires against the current compiler's two real occurrences.
    [Fact]
    public void v15_reject_wrong_actual_functions_and_finite_bridge_after_native_join()
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
        var rejectedFiles = new Dictionary<string, LeanFileReport>(files);
        var rejected = fixture.RootElement.GetProperty("rejected").EnumerateArray().ToArray();
        Assert.Equal(2, rejected.Length);
        foreach (var record in rejected)
        {
            var path = record.GetProperty("registration_source_path").GetString()!;
            var expectedRule = path.Contains("EndStateOmitsPreemptingCause", StringComparison.Ordinal)
                ? "source.finite_bridge" : "source.actual_observation";
            Assert.Equal("declared_unresolved", record.GetProperty("state").GetString());
            Assert.Equal(JsonValueKind.Null, record.GetProperty("certificate").ValueKind);
            Assert.StartsWith("IE-C050 ClosedTruthReadout ", record.GetProperty("diagnostic").GetString());
            Assert.Contains("rule=" + expectedRule + " ", record.GetProperty("diagnostic").GetString());
            var wire = JsonNode.Parse(files[path].InformationTemplates!.Value.GetRawText())!;
            wire["records"] = new JsonArray(JsonNode.Parse(record.GetRawText()));
            rejectedFiles[path] = files[path] with { InformationTemplates = JsonSerializer.SerializeToElement(wire) };
        }
        var rejectedEvidence = InformationTemplateEvidence.Collect(joined,
            LeanAxiomReport.Create(rejectedFiles), selected);
        Assert.Equal(2, rejectedEvidence.Inventory.Count);
        Assert.Equal(2, rejectedEvidence.Occurrences.Count);
        Assert.All(rejectedEvidence.Occurrences.Values, occurrence =>
        {
            Assert.Equal(InformationTemplateBindingState.DeclaredUnresolved, occurrence.State);
            Assert.Null(occurrence.EvidenceRef);
            Assert.False(occurrence.HasFourSlots);
            Assert.StartsWith("IE-C050 ClosedTruthReadout ", occurrence.Diagnostic);
        });
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
