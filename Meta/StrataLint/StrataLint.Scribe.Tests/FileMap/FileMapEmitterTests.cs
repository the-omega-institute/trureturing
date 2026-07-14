using System.Text;

namespace StrataLint.Scribe.Tests;

public sealed class FileMapEmitterTests
{
    [Fact]
    public void DependencyProjectionIsByteStableAndDerivedFromEveryEntry()
    {
        var manifest = FileMapLoader.Parse(Encoding.UTF8.GetBytes("""
            schema_version = 1

            [[files]]
            pattern = "Blueprint/**/*.md"
            kind = "generated"
            produced_by = "ScribeEmitter"
            consumed_by = ["reader"]
            verified_by = ["emit-check"]

            [[files]]
            pattern = "D5/**/*.lean"
            kind = "truth"
            produced_by = "none"
            consumed_by = ["Lean"]
            verified_by = ["lean-build"]
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
    }

    [Fact]
    public void FileMapEmitterWritesChecksAndDoesNotOverwriteDrift()
    {
        var sourceRoot = FindRepositoryRoot();
        var root = Path.Combine(Path.GetTempPath(), "stratalint-filemap-" + Guid.NewGuid().ToString("N"));
        try
        {
            var manifestPath = Path.Combine(root, FileMapLoader.RelativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(manifestPath)!);
            File.Copy(Path.Combine(sourceRoot, FileMapLoader.RelativePath), manifestPath);
            using var output = new StringWriter();
            using var error = new StringWriter();

            Assert.Equal(0, FileMapEmitter.Emit(root, check: false, output, error));
            Assert.Equal(0, FileMapEmitter.Emit(root, check: true, output, error));
            Assert.Equal(string.Empty, error.ToString());

            var path = Path.Combine(root, FileMapEmitter.RelativePath);
            File.AppendAllText(path, "drift\n", new UTF8Encoding(false, true));
            var drifted = File.ReadAllBytes(path);

            Assert.Equal(1, FileMapEmitter.Emit(root, check: true, output, error));
            Assert.Equal(drifted, File.ReadAllBytes(path));
            Assert.Contains("out of date", error.ToString(), StringComparison.Ordinal);
        }
        finally
        {
            if (Directory.Exists(root)) Directory.Delete(root, recursive: true);
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
                CanonicalAnchorCatalogWriter.RelativePath,
                CanonicalValuesWriter.RelativePath,
                FileMapEmitter.RelativePath,
                ScribeEmitter.AttestationRelativePath,
            ])
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(expected, paths);
        Assert.All(GeneratedArtifactInventory.All, static artifact =>
            Assert.Equal("emit-check", artifact.VerifiedBy));
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, FileMapLoader.RelativePath)))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository FILEMAP.");
    }
}
