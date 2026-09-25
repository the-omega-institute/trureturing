using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class SourceFamilyEvidenceTests
{
    // SourceFamilyEvidence.lean checks this literal against the real imported-source exporter.
    private static JsonArray CompiledWire()
    {
        var literal = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(),
            "tools/lean-inspector/LeanInformationAuditRegTests/CompiledSourceWire.lean"));
        var first = literal.IndexOf("r##\"", StringComparison.Ordinal) + 4;
        var last = literal.LastIndexOf("\"##", StringComparison.Ordinal);
        Assert.True(first >= 4 && last > first);
        return JsonNode.Parse(literal[first..last])!.AsArray();
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
