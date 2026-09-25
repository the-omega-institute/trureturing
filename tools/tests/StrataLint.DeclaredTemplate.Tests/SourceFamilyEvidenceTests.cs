using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class SourceFamilyEvidenceTests
{
    // SourceFamilyEvidence.lean checks this literal against the real imported-source exporter.
    private static JsonArray CompiledWire(string fixture = "CompiledSourceWire.lean")
    {
        var literal = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
            "tools/lean-inspector/LeanInformationAuditRegTests/" + fixture));
        var first = literal.IndexOf("r##\"", StringComparison.Ordinal) + 4;
        var last = literal.LastIndexOf("\"##", StringComparison.Ordinal);
        Assert.True(first >= 4 && last > first);
        return JsonNode.Parse(literal[first..last])!.AsArray();
    }

    private static JsonObject OriginalCyclicInventory()
    {
        var literal = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
            "tools/lean-inspector/LeanInformationAuditRegTests/CyclicSourceInventory.lean"));
        var first = literal.IndexOf("r##\"", StringComparison.Ordinal) + 4;
        var last = literal.LastIndexOf("\"##", StringComparison.Ordinal);
        Assert.True(first >= 4 && last > first);
        return JsonNode.Parse(literal[first..last])!.AsObject();
    }

    private static JsonArray AllWire() => new(CompiledWire()
        .Where(w => w!["records"]![0]!["registration_source_path"]!.GetValue<string>() !=
            "Reg/D5/S1/Words/Patterns/CyclicStackPreimagesCore.lean")
        .Concat(CompiledWire("CompiledCyclicWire.lean")).Select(w => w!.DeepClone()).ToArray());

    private static void AssertOriginalCyclicInventory(JsonArray wire)
    {
        var inventory = OriginalCyclicInventory();
        var expected = new Dictionary<string, string>();
        foreach (var source in inventory["sources"]!.AsArray())
        {
            var path = source!["path"]!.GetValue<string>();
            var bytes = File.ReadAllBytes(Path.Combine(TestRepositoryLayout.FindRoot(), path));
            Assert.Equal(source["sha256"]!.GetValue<string>(),
                Convert.ToHexStringLower(SHA256.HashData(bytes)));
            Assert.Equal(source["bytes"]!.GetValue<int>(), bytes.Length);
            var owner = source["expected_reg_owner"]!.GetValue<string>();
            foreach (var name in source["expected_original_declarations"]!.AsArray())
                expected.Add(name!.GetValue<string>(), owner);
        }
        var records = wire.SelectMany(w => w!["records"]!.AsArray()).ToArray();
        Assert.Equal(expected.Keys.Order(StringComparer.Ordinal), records.Select(r =>
            r!["key"]!["theorem"]!.GetValue<string>()).Order(StringComparer.Ordinal));
        foreach (var record in records)
        {
            var name = record!["key"]!["theorem"]!.GetValue<string>();
            var owner = expected[name];
            Assert.Equal(owner, record["key"]!["registration_module"]!.GetValue<string>());
            Assert.Equal("declared_validated", record["state"]!.GetValue<string>());
            var source = record["certificate"]!["source_binding"]!;
            Assert.Equal(name, source["source_name"]!.GetValue<string>());
            Assert.Equal(owner[4..], source["source_owner"]!.GetValue<string>());
            Assert.DoesNotContain(name, inventory["retired_names"]!.AsArray()
                .Select(n => n!.GetValue<string>()));
        }
    }

    [Fact]
    public void all_original_cyclic_names_and_owners_pass_compiled_strict_join()
    {
        var wire = CompiledWire("CompiledCyclicWire.lean");
        AssertOriginalCyclicInventory(wire);
        var (snapshot, report, selected) = Inputs(wire);
        var evidence = InformationTemplateEvidence.Collect(snapshot, report, selected);
        Assert.Equal(26, evidence.Inventory.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
    }

    private static (RepositorySnapshot Snapshot, LeanAxiomReport Report, RepoPath[] Selected)
        Inputs(JsonArray wires)
    {
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var selected = new List<RepoPath>();
        foreach (var wire in wires)
        {
            var records = wire!["records"]!.AsArray();
            var registration = records[0]!["registration_source_path"]!.GetValue<string>();
            var owner = records[0]!["certificate"]!["source_binding"]!["source_owner"]!.GetValue<string>();
            var source = owner.Replace('.', '/') + ".lean";
            var declarations = records.SelectMany(record => new[] {
                new LeanDeclaration(record!["unit_name"]!.GetValue<string>(), "def", "retained unit", []),
                new LeanDeclaration(record["realization_name"]!.GetValue<string>(), "def", "audit record", []),
            }).ToImmutableArray();
            files.Add(registration, new([owner], declarations) {
                InformationTemplates = JsonSerializer.SerializeToElement(wire) });
            files.Add(source, new([], records.Select(record =>
                new LeanDeclaration(record!["key"]!["theorem"]!.GetValue<string>(),
                    "theorem", "original compiler declaration", [])).ToImmutableArray()));
            selected.Add(RepoPath.CreateKnown(registration));
        }
        var entries = files.Keys.Append("lean-report-inputs.json").Select(path =>
            new RawRepositoryEntry(path, ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path)))));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;
        return (snapshot, LeanAxiomReport.Create(files), selected.ToArray());
    }

    [Fact]
    public void four_original_compiled_occurrences_pass_strict_import_join()
    {
        var wire = CompiledWire();
        var (snapshot, report, selected) = Inputs(wire);
        var evidence = InformationTemplateEvidence.Collect(snapshot, report, selected);
        Assert.Equal(4, evidence.Inventory.Count);
        var scope = wire[0]!["records"]![0]!["certificate"]!["source_binding"]!;
        Assert.Equal(13, scope["telescope_size"]!.GetValue<int>());
        Assert.Equal(2, scope["level_count"]!.GetValue<int>());
        Assert.Equal(new[] { 0, 1, 11 }, scope["coordinates"]!.AsArray().Select(n => n!.GetValue<int>()));
        foreach (var module in wire)
        {
            var path = module!["records"]![0]!["registration_source_path"]!.GetValue<string>();
            var read = InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(module), path, snapshot);
            Assert.All(read.Records, row => Assert.True(row.HasFourSlots));
        }
    }

    // Opt in with a directory of the focused Lake :report module artifacts.
    // This consumes the production exports; it does not build or aggregate reports.
    [Fact]
    public void generated_source_artifacts_pass_real_import_material_and_axiom_join()
    {
        var directory = Environment.GetEnvironmentVariable("SOURCE_FAMILY_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused native module artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        using var scratch = new TemporaryDirectory();
        var artifacts = Directory.GetFiles(directory!, "*.zip").Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(20, artifacts.Length);
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
        var joinedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(sources.Values))).Snapshot;
        var selected = new List<RepoPath>();
        AssertOriginalCyclicInventory(CompiledWire("CompiledCyclicWire.lean"));
        foreach (var wire in AllWire())
        {
            var path = wire!["records"]![0]!["registration_source_path"]!.GetValue<string>();
            selected.Add(RepoPath.CreateKnown(path));
            Assert.True(JsonNode.DeepEquals(wire,
                JsonNode.Parse(files[path].InformationTemplates!.Value.GetRawText())));
        }
        var evidence = InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(files), selected);
        Assert.Equal(28, evidence.Inventory.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        // A present theorem file is insufficient when its actual import path is absent.
        foreach (var missing in new[] {
            "D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.lean",
            "Reg/Support/FiniteHistoryFamily.lean" })
        {
            var incomplete = files.Where(pair => pair.Key != missing)
                .ToDictionary(pair => pair.Key, pair => pair.Value);
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
                LeanAxiomReport.Create(incomplete), selected));
        }
    }

    [Theory]
    [InlineData("stale-version")]
    [InlineData("cross-occurrence")]
    [InlineData("corrupt-readout")]
    [InlineData("wrong-source-owner")]
    [InlineData("wrong-actual")]
    public void compiled_source_evidence_mutations_fail_closed(string mutation)
    {
        var wire = CompiledWire();
        var (snapshot, report, selected) = Inputs(wire);
        var module = wire[0]!;
        var row = module["records"]![0]!;
        switch (mutation)
        {
            case "stale-version": module["compatibility_version"] = 9; break;
            case "cross-occurrence": row["certificate"]!["key"]!["catalog"] = "Other"; break;
            case "corrupt-readout": row["certificate"]!["source_binding"]!["readouts"]![0]!["occurrence_identity"] = "invalid"; break;
            case "wrong-source-owner": row["certificate"]!["source_binding"]!["source_owner"] = "D5.Other"; break;
            case "wrong-actual": row["escape_from"]!["object_identity"] = new string('0', 64); break;
        }
        var files = report.Files.ToDictionary(pair => pair.Key.Value, pair => pair.Value);
        var path = selected[0].Value;
        files[path] = files[path] with { InformationTemplates = JsonSerializer.SerializeToElement(module) };
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(snapshot,
            LeanAxiomReport.Create(files), selected));
    }

    [Fact]
    public void unselected_corrupt_source_module_is_not_validated()
    {
        var (snapshot, report, selected) = Inputs(CompiledWire());
        var files = report.Files.ToDictionary(pair => pair.Key.Value, pair => pair.Value);
        files[selected[1].Value] = files[selected[1].Value] with {
            InformationTemplates = JsonSerializer.SerializeToElement(new { corrupt = true }) };
        Assert.Single(InformationTemplateEvidence.Collect(snapshot,
            LeanAxiomReport.Create(files), [selected[0]]).Inventory);
    }
}
