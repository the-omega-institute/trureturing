using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class IntegralSourceEvidenceTests
{
    // These are actual :report artifacts, including compiler type materials and axioms.
    // No synthetic positive report or copied certificate supplies the acceptance case.
    [SkippableFact]
    public void original_integrals_pass_production_materials_join_and_reject_corruption()
    {
        var directory = Environment.GetEnvironmentVariable("INTEGRAL_SOURCE_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused integral :report artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        using var scratch = new TemporaryDirectory();
        var artifacts = Directory.GetFiles(directory!, "*.zip").Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(4, artifacts.Length);
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
            (Source: "D5/S3/Weil/Mertens/Gamma.lean",
                Name: "integral_log_mul_exp_neg_eq_deriv_Gamma", Telescope: 0, State: 0),
            (Source: "D5/S3/Weil/ZetaGamma/ArchimedeanJumpDecomposition.lean",
                Name: "D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_cos",
                Telescope: 3, State: 3),
        };
        var selected = cases.Select(c => RepoPath.CreateKnown("Reg/" + c.Source)).ToArray();
        var evidence = InformationTemplateEvidence.Collect(joined, LeanAxiomReport.Create(files), selected);
        Assert.Equal(2, evidence.Inventory.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        foreach (var item in cases)
        {
            var path = "Reg/" + item.Source;
            var wire = JsonNode.Parse(files[path].InformationTemplates!.Value.GetRawText())!;
            var record = Assert.Single(wire["records"]!.AsArray())!;
            Assert.Equal(item.Name, record["key"]!["theorem"]!.GetValue<string>());
            Assert.Equal("declared_validated", record["state"]!.GetValue<string>());
            Assert.Equal("source-equivalence", record["bridge_kind"]!.GetValue<string>());
            var binding = record["certificate"]!["source_binding"]!;
            Assert.Equal(item.Source[..^5].Replace('/', '.'), binding["source_owner"]!.GetValue<string>());
            Assert.Equal(item.Telescope, binding["telescope_size"]!.GetValue<int>());
            var readout = Assert.Single(binding["readouts"]!.AsArray())!;
            Assert.Equal(item.State, readout["state_binder"]!.GetValue<int>());
            Assert.Equal(item.State + 1, readout["scope_size"]!.GetValue<int>());
            Assert.Equal(item.Telescope == 0 ? Array.Empty<int>() : new[] { 0, 1 },
                binding["coordinates"]!.AsArray().Select(n => n!.GetValue<int>()).ToArray());
            foreach (var mutation in new[] { "state-out-of-scope", "wrong-source", "wrong-owner", "no-slot", "bad-path" })
            {
                var changed = wire.DeepClone();
                var changedRecord = changed["records"]![0]!;
                var changedBinding = changedRecord["certificate"]!["source_binding"]!;
                switch (mutation)
                {
                    case "state-out-of-scope": changedBinding["readouts"]![0]!["state_binder"] = item.State + 1; break;
                    case "wrong-source": changedBinding["source_name"] = "D5.Other.result"; break;
                    case "wrong-owner": changedBinding["source_owner"] = "D5.Other"; break;
                    case "no-slot": changedRecord["escape_from"] = null; break;
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
        }
    }
}
