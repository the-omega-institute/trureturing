using System.Collections.Immutable;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class LegacyRelationsNativeTests
{
    // Supply focused :report artifacts from the current tree. This check never
    // treats the full-law support proofs as completed registration certificates.
    [SkippableFact]
    public void assigned_occurrences_keep_honest_native_status_and_reject_missing_evidence()
    {
        var directory = Environment.GetEnvironmentVariable("LEGACY_RELATIONS_ARTIFACTS");
        Skip.If(string.IsNullOrEmpty(directory), "Focused native artifacts were not supplied.");
        var root = TestRepositoryLayout.FindRoot();
        var files = new Dictionary<string, LeanFileReport>();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        sources.Add("lean-report-inputs.json", Source("lean-report-inputs.json"));
        using var scratch = new TemporaryDirectory();
        var artifacts = Directory.GetFiles(directory!, "*.zip").Order(StringComparer.Ordinal).ToArray();
        Assert.NotEmpty(artifacts);
        foreach (var artifact in artifacts)
        {
            var extracted = Path.Combine(scratch.Path, Path.GetFileNameWithoutExtension(artifact));
            ZipFile.ExtractToDirectory(artifact, extracted);
            var reportPath = Path.Combine(extracted, "raw-lean-report.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath));
            var row = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            var source = row.GetProperty("source_path").GetString()!;
            sources.Add(source, Source(source));
            var snapshot = Decode([sources[source], sources["lean-report-inputs.json"]]);
            var report = RawLeanReportArtifact.ReadFile(reportPath, snapshot, validateMaterials: true);
            Assert.Throws<FormatException>(() => RawLeanReportArtifact.ReadFile(reportPath,
                Decode([sources["lean-report-inputs.json"]]), validateMaterials: true));
            var file = report.Files[RepoPath.CreateKnown(source)];
            Assert.All(file.Declarations, declaration =>
            {
                Assert.NotEmpty(declaration.LoadTypeRepresentation());
                Assert.All(declaration.Axioms, axiom =>
                    Assert.Contains(axiom, new[] { "propext", "Classical.choice", "Quot.sound" }));
            });
            files.Add(source, file);
        }
        string[] assigned = [
            "Reg/D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause/InformationRoot.lean",
            "Reg/D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause/TemplateShadow.lean",
            "Reg/D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange/InformationRoot.lean",
            "Reg/D5/S3/ConceptDynamics/Completion/CommutingCompletionExchange/TemplateShadow.lean",
            "Reg/D5/S3/ConceptDynamics/InformationEscape/SystemUnit.lean"
        ];
        var joined = Decode(sources.Values);
        var selected = assigned.Select(RepoPath.CreateKnown).ToArray();
        var evidence = InformationTemplateEvidence.Collect(joined, LeanAxiomReport.Create(files), selected);
        Assert.Equal(5, evidence.Inventory.Count);
        Assert.Equal(5, evidence.Occurrences.Count);
        Assert.All(evidence.Occurrences.Values, occurrence => Assert.False(occurrence.HasFourSlots));
        foreach (var path in assigned)
        {
            var wire = files[path].InformationTemplates!.Value;
            var row = Assert.Single(wire.GetProperty("records").EnumerateArray());
            Assert.Equal("undeclared", row.GetProperty("state").GetString());
            Assert.Equal(JsonValueKind.Null, row.GetProperty("certificate").ValueKind);
            var changed = JsonNode.Parse(wire.GetRawText())!;
            changed["records"]![0]!["state"] = "declared_validated";
            changed["records"]![0]!["diagnostic"] = null;
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Read(
                JsonSerializer.SerializeToElement(changed), path, joined));
            var original = path.EndsWith("/TemplateShadow.lean", StringComparison.Ordinal)
                ? "D5/S3/ConceptDynamics/InformationEscape/TemplateShadow.lean"
                : path.Contains("EndStateOmitsPreemptingCause", StringComparison.Ordinal)
                ? "D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.lean"
                : path.Contains("CommutingCompletionExchange", StringComparison.Ordinal)
                    ? "D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.lean"
                    : "D5/S3/ConceptDynamics/InformationEscape/SystemUnit.lean";
            var missing = files.Where(pair => pair.Key != original)
                .ToDictionary(pair => pair.Key, pair => pair.Value);
            Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(
                joined, LeanAxiomReport.Create(missing), selected));
        }
        foreach (var support in new[] { "Preemption", "Completion", "System" })
        {
            var path = $"Reg/Support/LegacyRelations/{support}.lean";
            Assert.Contains(files[path].Declarations, declaration =>
                declaration.Name == $"Reg.Support.LegacyRelations.{support}.registration");
        }
    }

    private static RepositorySnapshot Decode(IEnumerable<RawRepositoryEntry> entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(entries))).Snapshot;
}
