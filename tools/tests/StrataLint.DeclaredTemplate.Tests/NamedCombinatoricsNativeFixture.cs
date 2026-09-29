using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

internal static class NamedCombinatoricsNativeFixture
{
    internal static void Check(string name, string sourceHash, int[] coordinates, bool frozen,
        params string[] supportingModules)
    {
        var directory = Environment.GetEnvironmentVariable("NAMED_COMBINATORICS_NATIVE");
        Skip.If(string.IsNullOrEmpty(directory), "Supply current scoped native module artifacts.");
        var owner = "D5.S3.Combinatorics." + name;
        var sourcePath = owner.Replace('.', '/') + ".lean";
        var registration = RepoPath.CreateKnown("Reg/" + sourcePath);
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        using var scratch = new TemporaryDirectory();
        foreach (var moduleName in new[] { owner, "Reg." + owner }.Concat(supportingModules))
        {
            var artifact = Path.Combine(directory!, moduleName + ".zip");
            Assert.True(File.Exists(artifact), "Missing current client native artifact: " + artifact);
            var extracted = Path.Combine(scratch.Path, moduleName);
            ZipFile.ExtractToDirectory(artifact, extracted);
            var reportPath = Path.Combine(extracted, "raw-lean-report.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath));
            var module = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            Assert.Equal(moduleName, module.GetProperty("module").GetString());
            var source = module.GetProperty("source_path").GetString()!;
            Assert.Equal(moduleName.Replace('.', '/') + ".lean", source);
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
        Assert.Equal(sourceHash, Convert.ToHexStringLower(SHA256.HashData(sources[sourcePath].Bytes.AsSpan())));
        if (frozen) SourceFamilyEvidenceTests.AssertFrozenOriginal(root, sourcePath, files[sourcePath]);
        sources.Add("lean-report-inputs.json", Source("lean-report-inputs.json"));
        var joinedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(sources.Values))).Snapshot;
        var joined = InformationTemplateEvidence.Collect(joinedSnapshot, LeanAxiomReport.Create(files), [registration]);
        Assert.Single(joined.Inventory);
        Assert.True(Assert.Single(joined.Occurrences.Values).HasFourSlots);
        var original = files[registration.Value];
        var wire = JsonNode.Parse(original.InformationTemplates!.Value.GetRawText())!;
        var row = Assert.Single(wire["records"]!.AsArray())!;
        Assert.Equal("declared_validated", row["state"]!.GetValue<string>());
        Assert.Equal("source-equivalence", row["bridge_kind"]!.GetValue<string>());
        Assert.Equal("open", row["escape_continues"]!["kind"]!.GetValue<string>());
        Assert.Equal(owner + ".result", row["key"]!["theorem"]!.GetValue<string>());
        var binding = row["certificate"]!["source_binding"]!;
        Assert.Equal(owner, binding["source_owner"]!.GetValue<string>());
        Assert.Equal(owner + ".result", binding["source_name"]!.GetValue<string>());
        Assert.Equal(coordinates, binding["coordinates"]!.AsArray().Select(n => n!.GetValue<int>()));
        Assert.Single(binding["readouts"]!.AsArray());
        Assert.Equal(owner + ".claim", binding["definition_entry"]!["name"]!.GetValue<string>());
        // A mirror cannot certify an absent mathematical statement.
        var incomplete = files.Where(pair => pair.Key != sourcePath).ToDictionary(pair => pair.Key, pair => pair.Value);
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(incomplete), [registration]));
        // An imported registration proof requires its actual native owner report.
        foreach (var support in supportingModules)
        {
            var supportPath = support.Replace('.', '/') + ".lean";
            var absentOwner = files.Where(pair => pair.Key != supportPath)
                .ToDictionary(pair => pair.Key, pair => pair.Value);
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
                LeanAxiomReport.Create(absentOwner), [registration]));
        }
        // Corrupt independent source, observation and dependency ties in native wire.
        foreach (var mutate in new Action<JsonNode>[] {
            r => r["escape_from"]!["object_identity"] = new string('0', 64),
            r => r["certificate"]!["source_binding"]!["definition_entry"]!["body_identity"] = new string('0', 64),
            r => r["certificate"]!["source_binding"]!["source_name"] = owner + ".claim",
            r => r["certificate"]!["extraction_inputs"]!.AsArray().Clear() })
        {
            var corrupt = wire.DeepClone();
            mutate(corrupt["records"]![0]!);
            files[registration.Value] = original with { InformationTemplates = JsonSerializer.SerializeToElement(corrupt) };
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
                LeanAxiomReport.Create(files), [registration]));
        }
        files[registration.Value] = original with { Imports = [] };
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(files), [registration]));
    }
}
