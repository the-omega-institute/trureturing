using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class FileMapEmitterTests
{
    [Fact]
    public void DependencyProjectionIsByteStableAndDerivedFromEveryEntry()
    {
        var manifest = FileMapLoader.Parse(Encoding.UTF8.GetBytes("""
            schema_version = 2

            [residence_policy]
            case_id = "RESIDENCE-EPOCH"
            desired = "data-must-live-outside-tools"
            known_violation_count = 1
            status = "known-violations-frozen-under-monitoring"

            [[files]]
            pattern = "Blueprint/**/*.md"
            kind = "generated"
            admission_plane = "content"
            produced_by = "ScribeEmitter"
            consumed_by = ["ScribeEmitter", "reader"]
            verified_by = ["ScribeEmitter"]
            runtime_disposition = "committed-source"
            artifact_id = "none"

            [[files]]
            pattern = "D5/**/*.lean"
            kind = "truth"
            admission_plane = "content"
            produced_by = "none"
            consumed_by = ["Lean"]
            verified_by = ["lean-build"]
            runtime_disposition = "committed-source"
            artifact_id = "none"

            [[files]]
            pattern = "tools/FixtureData/*.toml"
            kind = "data"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["TomlGoldenLoader"]
            verified_by = ["TomlGoldenLoader"]
            residence_violation = true
            runtime_disposition = "committed-source"
            artifact_id = "none"
            """ + "\n"), "fixture.toml");

        var first = FileMapProjectionWriter.Write(manifest);
        var second = FileMapProjectionWriter.Write(manifest);
        var markdown = Encoding.UTF8.GetString(first.AsSpan());

        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
        Assert.Contains(
            "ScribeEmitter --produces--> [Blueprint/**/*.md | generated]",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "[D5/**/*.lean | truth] --verified-by--> lean-build",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "desired=data-must-live-outside-tools; current=1; status=known-violations-frozen-under-monitoring; case=RESIDENCE-EPOCH",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "[tools/FixtureData/*.toml | data | residence_violation=true]",
            markdown,
            StringComparison.Ordinal);
    }

    [Fact]
    public void FileMapEmitterCheckRejectsCommittedByteDrift()
    {
        var repository = RepositoryAccessor.Discover(RepositoryRootCriterion.FileMapDirectoryNotFound);
        var root = Path.Combine(Path.GetTempPath(), "stratalint-filemap-" + Guid.NewGuid().ToString("N"));
        try
        {
            var manifestPath = Path.Combine(root, FileMapLoader.RelativePath);
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(manifestPath)!);
            repository.CopyTo(RepositoryRelativePath.Create(FileMapLoader.RelativePath), manifestPath);
            using var output = new StringWriter();
            using var error = new StringWriter();

            Assert.Equal(0, FileMapEmitter.Emit(root, check: false, output, error));
            Assert.Equal(0, FileMapEmitter.Emit(root, check: true, output, error));
            Assert.Equal(string.Empty, error.ToString());

            var path = Path.Combine(root, FileMapEmitter.RelativePath);
            TemporaryFileSystem.File.AppendAllText(path, "drift\n", new UTF8Encoding(false, true));
            var drifted = TemporaryFileSystem.File.ReadAllBytes(path);

            Assert.Equal(1, FileMapEmitter.Emit(root, check: true, output, error));
            Assert.Equal(drifted, TemporaryFileSystem.File.ReadAllBytes(path));
            Assert.Contains("out of date", error.ToString(), StringComparison.Ordinal);
        }
        finally
        {
            if (TemporaryFileSystem.Directory.Exists(root)) TemporaryFileSystem.Directory.Delete(root, recursive: true);
        }
    }

    [Fact]
    public void GeneratedInventoryIsDerivedFromCanonicalProducerOutputs()
    {
        var paths = GeneratedArtifactInventory.All
            .Select(static artifact => artifact.Path)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var expected = DocumentDefinitions.All
            .Select(static definition => definition.RelativePath.Value)
            .Concat(
            [
                CanonicalValuesWriter.RelativePath,
                DagEmitter.RelativePath,
                DagEmitter.TruthGraphRelativePath,
                "Generated/truth-export.v1.json",
                FileMapEmitter.RelativePath,
                ScribeEmitter.AttestationRelativePath,
            ])
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(expected, paths);
    }
}
