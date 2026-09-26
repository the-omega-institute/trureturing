using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class PhaseFisherSourceEvidenceTests
{
    // These are actual :report artifacts, including compiler type materials and axioms.
    // No synthetic positive report or copied certificate supplies the acceptance case.
    [SkippableFact]
    public void original_phase_fisher_pass_production_materials_join_and_reject_corruption()
    {
        var directory = Environment.GetEnvironmentVariable("PHASE_FISHER_SOURCE_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused phase_fisher :report artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        using var scratch = new TemporaryDirectory();
        var artifacts = Directory.GetFiles(directory!, "*.zip").Order(StringComparer.Ordinal).ToArray();
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
            (Source: "D5/S3/Quantum/Entanglement/PhaseHistoryBound.lean",
                Name: "D5.S3.Quantum.Entanglement.PhaseHistoryBound.actual_source_moments",
                Telescope: 4, State: 3, Scope: 9, Levels: 0, Coordinates: new[] { 0 }),
            (Source: "D5/S3/Quantum/Entanglement/PhaseHistoryBound.lean",
                Name: "D5.S3.Quantum.Entanglement.PhaseHistoryBound.phase_history_bound",
                Telescope: 8, State: 6, Scope: 8, Levels: 1, Coordinates: new[] { 0, 3 }),
            (Source: "D5/S3/Quantum/Information/FixedSupportFisherGap.lean",
                Name: "D5.S3.Quantum.Information.FixedSupportFisherGap.result",
                Telescope: 15, State: 16, Scope: 17, Levels: 1, Coordinates: new[] { 0, 5 }),
        };
        var selected = cases.Select(c => RepoPath.CreateKnown("Reg/" + c.Source)).Distinct().ToArray();
        var evidence = InformationTemplateEvidence.Collect(joined, LeanAxiomReport.Create(files), selected);
        Assert.Equal(3, evidence.Inventory.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        foreach (var item in cases)
        {
            var path = "Reg/" + item.Source;
            var wire = JsonNode.Parse(files[path].InformationTemplates!.Value.GetRawText())!;
            var record = Assert.Single(wire["records"]!.AsArray(), r => r!["key"]!["theorem"]!.GetValue<string>() == item.Name)!;
            Assert.Equal(item.Name, record["key"]!["theorem"]!.GetValue<string>());
            Assert.Equal("declared_validated", record["state"]!.GetValue<string>());
            Assert.Equal("source-equivalence", record["bridge_kind"]!.GetValue<string>());
            var binding = record["certificate"]!["source_binding"]!;
            Assert.Equal(item.Source[..^5].Replace('/', '.'), binding["source_owner"]!.GetValue<string>());
            Assert.Equal(item.Telescope, binding["telescope_size"]!.GetValue<int>());
            var readout = Assert.Single(binding["readouts"]!.AsArray())!;
            Assert.Equal(item.State, readout["state_binder"]!.GetValue<int>());
            Assert.Equal(item.Scope, readout["scope_size"]!.GetValue<int>());
            Assert.Equal(item.Levels, binding["level_count"]!.GetValue<int>());
            Assert.Equal(item.Coordinates,
                binding["coordinates"]!.AsArray().Select(n => n!.GetValue<int>()).ToArray());
            foreach (var mutation in new[] { "state-out-of-scope", "wrong-source", "wrong-owner", "no-slot", "bad-path", "wrong-universe", "captured-coordinate" })
            {
                var changed = wire.DeepClone();
                var changedRecord = Assert.Single(changed["records"]!.AsArray(), r =>
                    r!["key"]!["theorem"]!.GetValue<string>() == item.Name)!;
                var changedBinding = changedRecord["certificate"]!["source_binding"]!;
                switch (mutation)
                {
                    case "state-out-of-scope": changedBinding["readouts"]![0]!["state_binder"] = item.Scope; break;
                    case "wrong-source": changedBinding["source_name"] = "D5.Other.result"; break;
                    case "wrong-owner": changedBinding["source_owner"] = "D5.Other"; break;
                    case "no-slot": changedRecord["escape_from"] = null; break;
                    case "wrong-universe": changedBinding["level_count"] = -1; break;
                    case "captured-coordinate": changedBinding["coordinates"]![0] = item.Scope; break;
                    case "bad-path": changedBinding["readouts"]![0]!["path"]![0] = "invalid"; break;
                }
                var changedFiles = new Dictionary<string, LeanFileReport>(files) {
                    [path] = files[path] with { InformationTemplates = JsonSerializer.SerializeToElement(changed) }
                };
                Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joined,
                    LeanAxiomReport.Create(changedFiles), selected));
            }
            var missing = files.Where(pair => pair.Key != item.Source)
                .ToDictionary(pair => pair.Key, pair => pair.Value);
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joined,
                LeanAxiomReport.Create(missing), selected));
            var severed = new Dictionary<string, LeanFileReport>(files) {
                [path] = files[path] with { Imports = ImmutableArray<string>.Empty }
            };
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joined,
                LeanAxiomReport.Create(severed), selected));
        }
    }
}
