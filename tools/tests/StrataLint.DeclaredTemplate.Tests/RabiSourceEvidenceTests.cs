using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class RabiSourceEvidenceTests
{
    [SkippableFact]
    public void original_source_native_artifacts_pass_production_consumer_and_frozen_identity()
    {
        var directory = Environment.GetEnvironmentVariable("RABI_SOURCE_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused original/Reg native artifacts were not supplied.");
        const string owner = "D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials";
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
            // Corrupt the actual native material archive, retaining its addressed entry name.
            var materialsPath = RawLeanReportArtifact.MaterialsPath(reportPath);
            var pristineMaterials = File.ReadAllBytes(materialsPath);
            using (var archive = ZipFile.Open(materialsPath, ZipArchiveMode.Update))
            {
                var entry = archive.Entries.First();
                var name = entry.FullName;
                entry.Delete();
                using var writer = new StreamWriter(archive.CreateEntry(name).Open());
                writer.Write("corrupted-native-statement-material");
            }
            Assert.Throws<InvalidDataException>(() =>
                RawLeanReportArtifact.ReadFile(reportPath, snapshot, validateMaterials: true));
            File.WriteAllBytes(materialsPath, pristineMaterials);
            files.Add(source, file);
        }
        Assert.Equal("0323904e42d3bad872983c1fa35607c5b682b0b7f1072319ee4d3b1ca5fd5d2d", Convert.ToHexStringLower(
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
        // Only rule policy comes from the fixture; all inspected declarations are native.
        var policy = new RuleFixture().BuildForRuleCompatibility().Policy;
        CurrentRuleContext Current(Dictionary<string, LeanFileReport> reports)
        {
            var closure = Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(
                joinedSnapshot, LeanAxiomReport.Create(reports))).Capability;
            return CurrentRuleContext.Create(joinedSnapshot, policy, closure);
        }
        foreach (var (axiom, rule) in new[] { ("sorryAx", 2), ("unregisteredNativeAxiom", 20) })
        {
            Assert.Empty(RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(rule),
                Current(files)).Diagnostics);
            var original = files[registration.Value];
            var poisoned = new Dictionary<string, LeanFileReport>(files) {
                [registration.Value] = original with { Declarations = original.Declarations.Select(d =>
                    d.Name.EndsWith(".registration", StringComparison.Ordinal)
                        ? d with { Axioms = d.Axioms.Add(axiom) } : d).ToImmutableArray() }
            };
            Assert.NotEmpty(RuleCatalog.Default.EvaluateCurrentSingle(RuleId.CreateKnown(rule),
                Current(poisoned)).Diagnostics);
        }
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
        Assert.Equal(new[] { 0, 1, 3 },
            binding["coordinates"]!.AsArray().Select(n => n!.GetValue<int>()));
        var readout = Assert.Single(binding["readouts"]!.AsArray())!;
        Assert.Equal(0, readout["state_binder"]!.GetValue<int>());
        Assert.Equal(4, readout["scope_size"]!.GetValue<int>());
        Assert.Equal(new[] { "arg" },
            readout["state_operand"]!.AsArray().Select(n => n!.GetValue<string>()));
        Assert.False(readout["boolean_predicate"]!.GetValue<bool>());
        Assert.Equal(owner + ".claim", binding["definition_entry"]!["name"]!.GetValue<string>());
        Assert.Equal(Array.Empty<string>(),
            binding["definition_entry"]!["path"]!.AsArray().Select(n => n!.GetValue<string>()));
        foreach (var mutation in new[] { "state", "source", "owner", "slot", "path", "entry", "reference" })
        {
            var changed = wire.DeepClone();
            var changedRow = Assert.Single(changed["records"]!.AsArray())!;
            var changedBinding = changedRow["certificate"]!["source_binding"]!;
            switch (mutation)
            {
                case "state": changedBinding["readouts"]![0]!["state_binder"] = 4; break;
                case "source": changedBinding["source_name"] = "D5.Other.result"; break;
                case "owner": changedBinding["source_owner"] = "D5.Other"; break;
                case "slot": changedRow["escape_from"] = null; break;
                case "path": changedBinding["readouts"]![0]!["path"]![0] = "invalid"; break;
                case "entry": changedBinding["definition_entry"]!["name"] = owner + ".result"; break;
                case "reference": changedBinding["definition_entry"]!["reference_identity"] = new string('0', 64); break;
            }
            var changedFiles = new Dictionary<string, LeanFileReport>(files) {
                [registration.Value] = files[registration.Value] with {
                    InformationTemplates = JsonSerializer.SerializeToElement(changed) }
            };
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
                LeanAxiomReport.Create(changedFiles), [registration]));
        }
        var severed = new Dictionary<string, LeanFileReport>(files) {
            [registration.Value] = files[registration.Value] with { Imports = ImmutableArray<string>.Empty }
        };
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(severed), [registration]));
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
