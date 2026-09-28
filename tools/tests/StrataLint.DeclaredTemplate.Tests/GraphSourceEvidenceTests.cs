using System.Collections.Immutable;
using System.IO.Compression;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class GraphSourceEvidenceTests(Xunit.Abstractions.ITestOutputHelper output)
{
    [Fact]
    public void four_complete_originals_pass_current_materials_and_frozen_identity_join()
    {
        var root = TestRepositoryLayout.FindRoot();
        string[] modules = ["D5.S3.Combinatorics.Graph.OctahedralCochainSharpness",
            "D5.S3.Combinatorics.Graph.TripartiteH1Repair"];
        using var stdout = new MemoryStream();
        using var stderr = new MemoryStream();
        try
        {
            // The test owns production through the normal cache-guarded facets;
            // no supplied artifact directory or synthetic positive evidence.
            var produced = BoundedProcessRunner.Run("/bin/bash",
                ["tools/scripts/worktree/lean-cache-run.sh", "lake", "-d", "Reg", "build",
                    .. modules.SelectMany(m => new[] { "+" + m + ":report", "+Reg." + m + ":report" })],
                root, TimeSpan.FromSeconds(300), 4 * 1024 * 1024,
                standardOutput: stdout, standardError: stderr);
            Assert.True(produced.ExitCode == 0, "Native graph report production failed.");
        }
        finally
        {
            output.WriteLine(Encoding.UTF8.GetString(stdout.ToArray()));
            output.WriteLine(Encoding.UTF8.GetString(stderr.ToArray()));
        }
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        sources.Add("lean-report-inputs.json", Source("lean-report-inputs.json"));
        using var scratch = new TemporaryDirectory();
        foreach (var module in modules.SelectMany(m => new[] { m, "Reg." + m }))
        {
            var artifact = Path.Combine(root, ".lake/build/lean-inspector/modules", module + ".zip");
            var extracted = Path.Combine(scratch.Path, module);
            ZipFile.ExtractToDirectory(artifact, extracted);
            var reportPath = Path.Combine(extracted, "raw-lean-report.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath));
            var row = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            var source = row.GetProperty("source_path").GetString()!;
            sources.Add(source, Source(source));
            var snapshot = Decode([sources[source], sources["lean-report-inputs.json"]]);
            var file = RawLeanReportArtifact.ReadFile(reportPath, snapshot, validateMaterials: true)
                .Files[RepoPath.CreateKnown(source)];
            Assert.All(file.Declarations, declaration =>
            {
                Assert.NotEmpty(declaration.LoadTypeRepresentation());
                Assert.All(declaration.Axioms, axiom =>
                    Assert.Contains(axiom, new[] { "propext", "Classical.choice", "Quot.sound" }));
            });
            if (source.StartsWith("D5/", StringComparison.Ordinal))
                SourceFamilyEvidenceTests.AssertFrozenOriginal(root, source, file);
            files.Add(source, file);
        }
        var joined = Decode(sources.Values);
        var selected = modules.Select(m => RepoPath.CreateKnown("Reg/" + m.Replace('.', '/') + ".lean")).ToArray();
        var evidence = InformationTemplateEvidence.Collect(joined, LeanAxiomReport.Create(files), selected);
        Assert.Equal(4, evidence.Inventory.Count);
        Assert.Equal(4, evidence.Occurrences.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        var names = new HashSet<string>(StringComparer.Ordinal);
        foreach (var module in modules)
        {
            var source = module.Replace('.', '/') + ".lean";
            var path = "Reg/" + source;
            var wire = JsonNode.Parse(files[path].InformationTemplates!.Value.GetRawText())!;
            foreach (var (node, index) in wire["records"]!.AsArray().Select((n, i) => (n!, i)))
            {
                var name = node["key"]!["theorem"]!.GetValue<string>();
                Assert.True(names.Add(name));
                Assert.Equal("declared_validated", node["state"]!.GetValue<string>());
                Assert.Equal("source-equivalence", node["bridge_kind"]!.GetValue<string>());
                Assert.Equal("open", node["escape_continues"]!["kind"]!.GetValue<string>());
                Assert.Equal(module, node["certificate"]!["source_binding"]!["source_owner"]!.GetValue<string>());
                Assert.Equal(name, node["certificate"]!["source_binding"]!["source_name"]!.GetValue<string>());
                foreach (var mutation in new[] { "certificate", "source", "owner", "slot", "identity", "path" })
                {
                    var changed = wire.DeepClone();
                    var record = changed["records"]![index]!;
                    switch (mutation)
                    {
                        case "certificate": record["certificate"] = null; break;
                        case "source": record["certificate"]!["source_binding"]!["source_name"] = "D5.Other.result"; break;
                        case "owner": record["certificate"]!["source_binding"]!["source_owner"] = "D5.Other"; break;
                        case "slot": record["escape_from"] = null; break;
                        case "identity": record["statement_identity"] = new string('0', 64); break;
                        case "path": record["certificate"]!["source_binding"]!["readouts"]![0]!["path"] = new JsonArray("absent"); break;
                    }
                    var mutated = new Dictionary<string, LeanFileReport>(files) {
                        [path] = files[path] with { InformationTemplates = JsonSerializer.SerializeToElement(changed) }
                    };
                    Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joined,
                        LeanAxiomReport.Create(mutated), selected));
                }
            }
            var missing = files.Where(p => p.Key != source).ToDictionary(p => p.Key, p => p.Value);
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joined,
                LeanAxiomReport.Create(missing), selected));
        }
        Assert.Equal(new[] { modules[0] + ".antipodal_repair_sharpness", modules[1] + ".ker_d1_eq_im_d0",
            modules[1] + ".sharp_three_edge_witness", modules[1] + ".universal_repair" },
            names.Order(StringComparer.Ordinal));
    }

    private static RepositorySnapshot Decode(IEnumerable<RawRepositoryEntry> entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;
}
