using System.Collections.Immutable;
using System.IO.Compression;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.DeclaredTemplate.Tests;

public sealed class SolidPartitionSourceEvidenceTests
{
    // Original PR #10360 at abc4dc58: all dimensions, both positive guards and both columns.
    // Validate the exact original source against its accompanying frozen identity.
    [Fact]
    public void exact_frozen_original_passes_native_join_and_corruptions_reject()
    {
        NamedCombinatoricsNativeFixture.Check("SolidPartitionFirstColumn",
            "56fe53e1809ecdc679c78f85d2dcea658dd6a5aa67afa9b5161deeb4b8237683", [0], true);
        var directory = Environment.GetEnvironmentVariable("NAMED_COMBINATORICS_NATIVE")!;
        var root = TestRepositoryLayout.FindRoot();
        const string owner = "D5.S3.Combinatorics.SolidPartitionFirstColumn";
        RawRepositoryEntry Source(string path) => new(path,
            ImmutableArray.CreateRange(File.ReadAllBytes(Path.Combine(root, path))));
        using var scratch = new TemporaryDirectory();
        foreach (var moduleName in new[] { owner, "Reg." + owner })
        {
            var extracted = Path.Combine(scratch.Path, moduleName);
            ZipFile.ExtractToDirectory(Path.Combine(directory, moduleName + ".zip"), extracted);
            var reportPath = Path.Combine(extracted, "raw-lean-report.json");
            var sourcePath = moduleName.Replace('.', '/') + ".lean";
            var source = Source(sourcePath);
            var config = Source("lean-report-inputs.json");
            var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                RawRepositorySnapshot.Create([source, config]))).Snapshot;
            RawLeanReportArtifact.ReadFile(reportPath, snapshot, validateMaterials: true);
            if (moduleName.StartsWith("Reg.", StringComparison.Ordinal))
            {
                using var document = JsonDocument.Parse(File.ReadAllBytes(reportPath));
                var row = Assert.Single(document.RootElement.GetProperty("modules").EnumerateArray());
                var record = Assert.Single(row.GetProperty("information_templates")
                    .GetProperty("records").EnumerateArray());
                var binding = record.GetProperty("certificate").GetProperty("source_binding");
                // The raw type is `claim`; the all-dimensional telescope is inside its named body.
                Assert.Equal(0, binding.GetProperty("telescope_size").GetInt32());
                Assert.Equal(0, binding.GetProperty("level_count").GetInt32());
                var readout = Assert.Single(binding.GetProperty("readouts").EnumerateArray());
                Assert.Equal(4, readout.GetProperty("scope_size").GetInt32());
                Assert.Equal(1, readout.GetProperty("state_binder").GetInt32());
                Assert.Equal(new[] { "body", "body", "body", "body", "fn", "arg", "arg" },
                    readout.GetProperty("path").EnumerateArray().Select(e => e.GetString()));
                Assert.Equal("Reg." + owner + ".registration", record.GetProperty("realization_name").GetString());
            }
            var changedSource = new RawRepositoryEntry(sourcePath,
                ImmutableArray.CreateRange(source.Bytes.Concat(Encoding.UTF8.GetBytes("\n-- changed\n"))));
            var changedSnapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                RawRepositorySnapshot.Create([changedSource, config]))).Snapshot;
            var sourceError = Assert.Throws<FormatException>(() =>
                RawLeanReportArtifact.ReadFile(reportPath, changedSnapshot, validateMaterials: true));
            Assert.Contains("source hash does not match", sourceError.Message, StringComparison.Ordinal);
            using (var archive = ZipFile.Open(RawLeanReportArtifact.MaterialsPath(reportPath), ZipArchiveMode.Update))
            {
                var entry = archive.Entries.First();
                var name = entry.FullName;
                entry.Delete();
                using var stream = archive.CreateEntry(name).Open();
                stream.Write(Encoding.UTF8.GetBytes("statement-v1(changed)"));
            }
            var materialError = Assert.Throws<InvalidDataException>(() =>
                RawLeanReportArtifact.ReadFile(reportPath, snapshot, validateMaterials: true));
            Assert.Contains("hash mismatch", materialError.ToString(), StringComparison.OrdinalIgnoreCase);
        }
    }
}
