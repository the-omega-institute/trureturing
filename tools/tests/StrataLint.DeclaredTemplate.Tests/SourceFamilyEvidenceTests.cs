using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

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
        .Concat(CompiledWire("CompiledCyclicWire.lean"))
        .Concat(CompiledWire("CompiledQuantumWire.lean")).Select(w => w!.DeepClone()).ToArray());

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

    internal static void AssertFrozenOriginal(string root, string source, LeanFileReport file)
    {
        var path = RepoPath.CreateKnown(source);
        var statementId = FrozenContentHash.Compute(FrozenHashDomains.Statement,
            CanonicalStatementWriter.WriteModule(path,
                CanonicalStatementWriter.DeclarationStatementIds(path, file)).AsSpan());
        var pin = JsonNode.Parse(File.ReadAllBytes(Path.Combine(root,
            "Golden/Frozen/state/" + source + ".json")))!;
        Assert.Equal(pin["statement_id"]!.GetValue<string>(), statementId);
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
            files.Add(source, new([], records.SelectMany(record =>
            {
                var theorem = new LeanDeclaration(record!["key"]!["theorem"]!.GetValue<string>(),
                    "theorem", "original compiler declaration", []);
                var entry = record["certificate"]!["source_binding"]!["definition_entry"];
                if (entry is null) return new[] { theorem };
                // Synthetic import-join fixture. Native tests below separately
                // load and hash-check the actual compiler statement materials.
                var claimName = owner + ".claim";
                var nameKey = claimName.Split('.').Aggregate("n0", (parent, part) =>
                    $"ns({parent},{System.Text.Encoding.UTF8.GetByteCount(part)}:{part})");
                var reference = "ec(" + nameKey + ",[])";
                var rawType = theorem.Name.EndsWith("NiceErrorBasisNonNormalStabilizer.result", StringComparison.Ordinal)
                    ? "ea(ec(ns(n0,3:Not),[])," + reference + ")" : reference;
                return new[] { theorem with { TypeRepresentation = "statement-v1(uparams=[],type=" + rawType + ")" },
                    new LeanDeclaration(claimName, "def", "statement-v1(uparams=[],type=es(l0),value=fixture)", []) {
                        NameKey = nameKey } };
            }).ToImmutableArray()));
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
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void generated_source_artifacts_pass_real_import_material_and_axiom_join(bool historical)
    {
        var directory = Environment.GetEnvironmentVariable(historical
            ? "QUANTUM_HISTORICAL_ARTIFACTS" : "SOURCE_FAMILY_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused native module artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path)
        {
            var isolatedSource = Path.Combine(directory!, "sources", path);
            var file = historical && File.Exists(isolatedSource) ? isolatedSource : Path.Combine(root, path);
            return new(path, ImmutableArray.CreateRange(File.ReadAllBytes(file)));
        }
        using var scratch = new TemporaryDirectory();
        var artifacts = Directory.GetFiles(directory!, "*.zip").Order(StringComparer.Ordinal).ToArray();
        Assert.Equal(historical ? 5 : 24, artifacts.Length);
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
        var quantumFixture = historical ? "CompiledQuantumHistoricalWire.lean" : "CompiledQuantumWire.lean";
        var quantum = CompiledWire(quantumFixture);
        var quantumRecord = Assert.Single(Assert.Single(quantum)!["records"]!.AsArray())!;
        const string quantumOwner = "D5.S3.Quantum.Information.ActualQubitChordObstruction";
        var quantumName = quantumOwner + (historical
            ? ".actual_two_probe_chord_obstruction" : ".actual_two_probe_chord_and_qfi");
        Assert.Equal(quantumName, quantumRecord["key"]!["theorem"]!.GetValue<string>());
        Assert.Equal("Reg." + quantumOwner,
            quantumRecord["key"]!["registration_module"]!.GetValue<string>());
        var originalBytes = Source(quantumOwner.Replace('.', '/') + ".lean").Bytes.ToArray();
        Assert.Equal(historical ? 22806 : 36217, originalBytes.Length);
        Assert.Equal(historical
            ? "e38587117aa2fd85bf40596abc5c556725faafbfabcaddb21ae96b9f9211f61b"
            : "4f45e964a8a60de2e526fa8ecc9d7290e89b061a1a687359917d065453126fb0",
            Convert.ToHexStringLower(SHA256.HashData(originalBytes)));
        var quantumPath = RepoPath.CreateKnown(quantumOwner.Replace('.', '/') + ".lean");
        if (!historical)
        {
            var statementId = FrozenContentHash.Compute(FrozenHashDomains.Statement,
                CanonicalStatementWriter.WriteModule(quantumPath,
                    CanonicalStatementWriter.DeclarationStatementIds(quantumPath, files[quantumPath.Value])).AsSpan());
            var pin = JsonNode.Parse(File.ReadAllBytes(Path.Combine(root,
                "Golden/Frozen/state/" + quantumPath.Value + ".json")))!;
            Assert.Equal(pin["statement_id"]!.GetValue<string>(), statementId);
        }
        foreach (var wire in historical ? quantum : AllWire())
        {
            var path = wire!["records"]![0]!["registration_source_path"]!.GetValue<string>();
            selected.Add(RepoPath.CreateKnown(path));
            Assert.True(JsonNode.DeepEquals(wire,
                JsonNode.Parse(files[path].InformationTemplates!.Value.GetRawText())));
            if (!historical)
            {
                var original = wire["records"]![0]!["certificate"]!["source_binding"]!["source_owner"]!
                    .GetValue<string>().Replace('.', '/') + ".lean";
                AssertFrozenOriginal(root, original, files[original]);
            }
        }
        var evidence = InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(files), selected);
        Assert.Equal(historical ? 1 : 29, evidence.Inventory.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        // A present theorem file is insufficient when its actual import path is absent.
        foreach (var missing in historical ? new[] {
            "D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.lean",
            "Reg/Support/QubitChordChannels.lean" } : new[] {
            "D5/S3/ConceptDynamics/InformationEscape/CyclicStackFamily.lean",
            "Reg/Support/FiniteHistoryFamily.lean",
            "D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily.lean",
            "Reg/Support/QubitChordChannels.lean" })
        {
            var incomplete = files.Where(pair => pair.Key != missing)
                .ToDictionary(pair => pair.Key, pair => pair.Value);
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
                LeanAxiomReport.Create(incomplete), selected));
        }
    }

    [Fact]
    public void original_torus_compiled_wire_passes_strict_join()
    {
        var wire = CompiledWire("CompiledTorusWire.lean");
        var (snapshot, report, selected) = Inputs(wire);
        var evidence = InformationTemplateEvidence.Collect(snapshot, report, selected);
        var row = Assert.Single(evidence.Occurrences.Values);
        Assert.True(row.HasFourSlots);
        var source = wire[0]!["records"]![0]!["certificate"]!["source_binding"]!;
        Assert.Equal(3, source["telescope_size"]!.GetValue<int>());
        Assert.Equal(1, source["level_count"]!.GetValue<int>());
        Assert.Equal(new[] { 0, 2 }, source["coordinates"]!.AsArray().Select(n => n!.GetValue<int>()));
        var bytes = File.ReadAllBytes(Path.Combine(TestRepositoryLayout.FindRoot(),
            "D5/S3/Fourier/Asymptotics/TorusOrbitEquidistribution.lean"));
        Assert.Equal("c3f04b199c1259b849fe76e72cc7bb3c29c0dafbbc452f1f66a1023a924d3bbe",
            Convert.ToHexStringLower(SHA256.HashData(bytes)));
    }

    [Theory]
    [InlineData("sibling-coordinate")]
    [InlineData("missing-context")]
    [InlineData("non-ancestor")]
    [InlineData("coordinate-count")]
    [InlineData("coordinate-bound")]
    public void compiled_torus_lexical_wire_mutations_reject(string mutation)
    {
        var wire = CompiledWire("CompiledTorusWire.lean");
        var (snapshot, _, selected) = Inputs(wire);
        var source = wire[0]!["records"]![0]!["certificate"]!["source_binding"]!;
        switch (mutation)
        {
            case "sibling-coordinate": source["coordinate_paths"]![0] = new JsonArray("arg", "body"); break;
            case "missing-context": source["readouts"]![0]!.AsObject().Remove("scope_paths"); break;
            case "non-ancestor": source["readouts"]![0]!["scope_paths"]![0] = new JsonArray("arg", "body"); break;
            case "coordinate-count": source["coordinate_paths"] = new JsonArray(); break;
            case "coordinate-bound": source["coordinates"]![1] = 256; break;
        }
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
            JsonSerializer.SerializeToElement(wire[0]), selected[0].Value, snapshot));
    }

    [Fact]
    public void generated_torus_artifacts_pass_production_material_axiom_and_import_join()
    {
        var directory = Environment.GetEnvironmentVariable("TORUS_SOURCE_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused Torus native module artifacts were not supplied.");
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
        var registration = RepoPath.CreateKnown("Reg/D5/S3/Fourier/Asymptotics/TorusOrbitEquidistribution.lean");
        var report = LeanAxiomReport.Create(files);
        const string originalSource = "D5/S3/Fourier/Asymptotics/TorusOrbitEquidistribution.lean";
        AssertFrozenOriginal(root, originalSource, files[originalSource]);
        var joined = InformationTemplateEvidence.Collect(joinedSnapshot, report, [registration]);
        Assert.True(Assert.Single(joined.Occurrences.Values).HasFourSlots);
        Assert.Equal(CompiledWire("CompiledTorusWire.lean")[0]!.ToJsonString(),
            JsonNode.Parse(files[registration.Value].InformationTemplates!.Value.GetRawText())!.ToJsonString());
        files.Remove("D5/S3/Fourier/Asymptotics/TorusOrbitEquidistribution.lean");
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(files), [registration]));
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
    [Fact]
    public void four_original_named_claims_pass_compiled_strict_join()
    {
        var wire = CompiledWire("CompiledNamedClaimWire.lean");
        var (snapshot, report, selected) = Inputs(wire);
        var evidence = InformationTemplateEvidence.Collect(snapshot, report, selected);
        Assert.Equal(4, evidence.Inventory.Count);
        Assert.All(evidence.Occurrences.Values, row =>
        {
            Assert.True(row.HasFourSlots);
            Assert.Equal(row.SourceOwner + ".claim", row.SourceDefinitionName);
        });
        Assert.All(wire, module =>
        {
            var source = module!["records"]![0]!["certificate"]!["source_binding"]!;
            Assert.Equal(0, source["telescope_size"]!.GetValue<int>());
            Assert.Equal(0, source["level_count"]!.GetValue<int>());
        });
    }

    [Theory]
    [InlineData("missing-definition")]
    [InlineData("wrong-definition-kind")]
    [InlineData("duplicate-definition")]
    [InlineData("duplicate-name-other-kind")]
    [InlineData("cross-source-entry")]
    [InlineData("stale-version")]
    public void original_named_claim_evidence_rejects_wrong_join(string mutation)
    {
        var wire = CompiledWire("CompiledNamedClaimWire.lean");
        var (snapshot, report, selected) = Inputs(wire);
        var files = report.Files.ToDictionary(pair => pair.Key.Value, pair => pair.Value);
        var sourceBinding = wire[0]!["records"]![0]!["certificate"]!["source_binding"]!;
        var definitionName = sourceBinding["definition_entry"]!["name"]!.GetValue<string>();
        var sourcePath = sourceBinding["source_owner"]!.GetValue<string>().Replace('.', '/') + ".lean";
        var source = files[sourcePath];
        if (mutation == "missing-definition")
            files[sourcePath] = source with {
                Declarations = source.Declarations.Where(d => d.Name != definitionName).ToImmutableArray() };
        if (mutation == "wrong-definition-kind")
            files[sourcePath] = source with {
                Declarations = source.Declarations.Select(d => d.Name == definitionName
                    ? d with { Kind = "theorem" } : d).ToImmutableArray() };
        if (mutation == "duplicate-definition")
            files[sourcePath] = source with {
                Declarations = source.Declarations.Add(source.Declarations.Single(d => d.Name == definitionName)) };
        if (mutation == "duplicate-name-other-kind")
            files[sourcePath] = source with {
                Declarations = source.Declarations.Add(
                    new LeanDeclaration(definitionName, "theorem", "duplicate", [])) };
        if (mutation == "cross-source-entry")
            sourceBinding["definition_entry"] = wire[1]!["records"]![0]!["certificate"]!
                ["source_binding"]!["definition_entry"]!.DeepClone();
        if (mutation == "stale-version") wire[0]!["compatibility_version"] = 11;
        files[selected[0].Value] = files[selected[0].Value] with {
            InformationTemplates = JsonSerializer.SerializeToElement(wire[0]) };
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(snapshot,
            LeanAxiomReport.Create(files), selected));
    }

    [Theory]
    [InlineData("missing-path")]
    [InlineData("stale-root-path")]
    [InlineData("wrong-path")]
    [InlineData("twice-entered")]
    [InlineData("sibling-readout")]
    [InlineData("lost-negation-identity")]
    public void original_negative_claim_wire_rejects_changed_entry(string mutation)
    {
        var wire = CompiledWire("CompiledNamedClaimWire.lean");
        var (snapshot, _, selected) = Inputs(wire);
        var module = wire.Single(m => m!["records"]![0]!["key"]!["theorem"]!
            .GetValue<string>().EndsWith("NiceErrorBasisNonNormalStabilizer.result", StringComparison.Ordinal))!;
        var source = module["records"]![0]!["certificate"]!["source_binding"]!;
        Assert.Equal(new[] { "arg" }, source["definition_entry"]!["path"]!.AsArray()
            .Select(n => n!.GetValue<string>()));
        switch (mutation)
        {
            case "missing-path": source["definition_entry"]!.AsObject().Remove("path"); break;
            case "stale-root-path": source["definition_entry"]!["path"] = new JsonArray(); break;
            case "wrong-path": source["definition_entry"]!["path"] = new JsonArray("fn"); break;
            case "twice-entered": source["definition_entry"]!["path"] = new JsonArray("arg", "arg"); break;
            case "sibling-readout": source["readouts"]![0]!["path"]![0] = "fn"; break;
            case "lost-negation-identity": source["source_type_identity"] = new string('0', 64); break;
        }
        var path = module["records"]![0]!["registration_source_path"]!.GetValue<string>();
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
            JsonSerializer.SerializeToElement(module), path, snapshot));
    }

    [Theory]
    [InlineData(null)]
    [InlineData("nonroot-reference")]
    [InlineData("self-consistent-identities")]
    [InlineData("self-consistent-root-identities")]
    [InlineData("self-consistent-universes")]
    public void generated_named_claim_artifacts_pass_production_material_axiom_and_import_join(string? mutation)
    {
        var directory = Environment.GetEnvironmentVariable("NAMED_CLAIM_SOURCE_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused named-claim module artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        using var scratch = new TemporaryDirectory();
        var artifacts = Directory.GetFiles(directory!, "*.zip");
        Assert.Equal(8, artifacts.Length);
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
            if (source.StartsWith("D5/", StringComparison.Ordinal))
            {
                AssertFrozenOriginal(root, source, file);
            }
        }
        sources.Add("lean-report-inputs.json", Source("lean-report-inputs.json"));
        var joinedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(sources.Values))).Snapshot;
        var selected = new List<RepoPath>();
        foreach (var wire in CompiledWire("CompiledNamedClaimWire.lean"))
        {
            var path = wire!["records"]![0]!["registration_source_path"]!.GetValue<string>();
            selected.Add(RepoPath.CreateKnown(path));
            Assert.True(JsonNode.DeepEquals(wire,
                JsonNode.Parse(files[path].InformationTemplates!.Value.GetRawText())));
        }
        var evidence = InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(files), selected);
        Assert.Equal(4, evidence.Inventory.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.True(occurrence.HasFourSlots));
        if (mutation is not null)
        {
            var rootMutation = mutation == "self-consistent-root-identities";
            var registration = rootMutation
                ? "Reg/D5/S3/Constants/Billiards/CollidingBlocksRecords.lean"
                : "Reg/D5/S3/Quantum/Information/NiceErrorBasisNonNormalStabilizer.lean";
            var module = JsonNode.Parse(files[registration].InformationTemplates!.Value.GetRawText())!;
            var row = Assert.Single(module["records"]!.AsArray())!;
            var binding = row["certificate"]!["source_binding"]!;
            var entry = binding["definition_entry"]!;
            Assert.Equal(rootMutation ? Array.Empty<string>() : new[] { "arg" },
                entry["path"]!.AsArray().Select(n => n!.GetValue<string>()));
            var wrong = new string('0', 64);
            Assert.NotEqual(wrong, row["statement_identity"]!.GetValue<string>());
            Assert.NotEqual(wrong, entry["reference_identity"]!.GetValue<string>());
            entry["reference_identity"] = wrong;
            if (mutation != "nonroot-reference")
            {
                var wrongStatement = rootMutation ? wrong : new string('1', 64);
                if (mutation == "self-consistent-universes")
                {
                    // Valid compactRawIdentity encodings of this very same name
                    // with one rigid parameter, including the literal Not root.
                    // These are corruptions, not replacement compiler evidence.
                    binding["level_count"] = 1;
                    entry["reference_identity"] = "4a3b9ddbe1d91b091777c9f7fbb3ee9a1170703228c45ca3beed291326f91e84";
                    wrongStatement = "5f7d56fa34d4fe9e905e14f46d48a81db6947caf3cb50809bd1efd7d3cfcb697";
                }
                row["statement_identity"] = wrongStatement;
                binding["source_type_identity"] = wrongStatement;
                row["escape_from"]!["type_identity"] = wrongStatement;
                row["certificate"]!["extraction_inputs"]!.AsArray().Single(input =>
                    input!["name"]!.GetValue<string>() == row["key"]!["theorem"]!.GetValue<string>())!
                    ["type_identity"] = wrongStatement;
            }
            // All old closed-shape and same-wire joins still accept the mutation.
            InformationTemplateEvidence.Read(JsonSerializer.SerializeToElement(module), registration, joinedSnapshot);
            files[registration] = files[registration] with {
                InformationTemplates = JsonSerializer.SerializeToElement(module) };
            var error = Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
                LeanAxiomReport.Create(files), selected));
            Assert.Contains(mutation == "self-consistent-universes"
                ? "source definition raw declaration differs" : "reference identity differs from current declaration",
                error.Message, StringComparison.Ordinal);
            return;
        }
        foreach (var source in files.Keys.Where(p => p.StartsWith("D5/", StringComparison.Ordinal)))
        {
            var incomplete = files.Where(pair => pair.Key != source)
                .ToDictionary(pair => pair.Key, pair => pair.Value);
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
                LeanAxiomReport.Create(incomplete), selected));
        }
    }

}
