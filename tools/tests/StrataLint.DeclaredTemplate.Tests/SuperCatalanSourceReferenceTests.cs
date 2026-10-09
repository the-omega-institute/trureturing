using System.Collections.Immutable;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class SuperCatalanSourceReferenceTests
{
    [SkippableFact]
    public void original_current_native_source_reference_has_accepted_four_slots()
    {
        var directory = Environment.GetEnvironmentVariable("NAMED_SOURCE_REFERENCE_NATIVE");
        Skip.If(string.IsNullOrEmpty(directory), "Supply the original current source and registration report bundles.");
        const string owner = "D5.S3.Combinatorics.Graph.SuperCatalanActionGraphRecurrence";
        var root = TestRepositoryLayout.FindRoot();
        var sources = new Dictionary<string, RawRepositoryEntry>();
        var files = new Dictionary<string, LeanFileReport>();
        using var scratch = new TemporaryDirectory();
        foreach (var moduleName in new[] { owner, "Reg." + owner })
        {
            var extracted = Path.Combine(scratch.Path, moduleName);
            ZipFile.ExtractToDirectory(Path.Combine(directory!, moduleName + ".evidence.zip"), extracted);
            var reportPath = Path.Combine(extracted, "raw-lean-report.json");
            using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath));
            var module = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
            Assert.Equal(moduleName, module.GetProperty("module").GetString());
            var source = module.GetProperty("source_path").GetString()!;
            Assert.Equal(moduleName.Replace('.', '/') + ".lean", source);
            // The separately delivered Reg source is subject data, not judge code.
            var sourceFile = moduleName.StartsWith("Reg.", StringComparison.Ordinal)
                ? Path.Combine(directory!, moduleName + ".source.lean") : Path.Combine(root, source);
            var bytes = File.ReadAllBytes(sourceFile);
            Assert.Equal("sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes)),
                module.GetProperty("source_sha256").GetString());
            sources.Add(source, new(source, ImmutableArray.CreateRange(bytes)));
            var input = new RawRepositoryEntry("lean-report-inputs.json",
                ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, "lean-report-inputs.json"))));
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                RawRepositorySnapshot.Create([sources[source], input]))).Snapshot;
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
        var joinedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(sources.Values))).Snapshot;
        var registration = RepoPath.CreateKnown("Reg/" + owner.Replace('.', '/') + ".lean");
        var report = LeanAxiomReport.Create(files);
        var joined = InformationTemplateEvidence.Collect(joinedSnapshot, report, [registration]);
        var occurrence = Assert.Single(joined.Occurrences.Values);
        Assert.Single(joined.Inventory);
        Assert.Equal(owner + ".result", occurrence.Key.Theorem);
        Assert.True(occurrence.HasFourSlots);
        Assert.Equal(InformationTemplateBindingState.DeclaredValidated, occurrence.State);
        Assert.Equal("2355ba49275ae211b06460be451dd5e6ef06a6ab795a16d0e54d9f24024fe815", occurrence.StatementIdentity);
        var sourcePath = owner.Replace('.', '/') + ".lean";
        var sourceReport = files[sourcePath];
        SourceFamilyEvidenceTests.AssertFrozenOriginal(root, sourcePath, sourceReport);
        // Independent raw source changes cannot be hidden behind the certificate.
        var theorem = sourceReport.Declarations.Single(d => d.Name == owner + ".result");
        var changedTheorem = theorem with { TypeRepresentation = theorem.LoadTypeRepresentation()
            .Replace("5:claim", "5:other", StringComparison.Ordinal) };
        files[sourcePath] = sourceReport with { Declarations = sourceReport.Declarations
            .Select(d => d.Name == theorem.Name ? changedTheorem : d).ToImmutableArray() };
        Assert.Throws<FormatException>(() => InformationTemplateEvidence.Collect(joinedSnapshot,
            LeanAxiomReport.Create(files), [registration]));
    }
}
