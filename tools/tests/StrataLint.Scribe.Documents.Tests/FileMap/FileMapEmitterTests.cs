namespace StrataLint.Scribe.Tests;

public sealed class FileMapEmitterTests
{
    [Fact]
    public void GeneratedInventoryIsDerivedFromCanonicalProducerOutputs()
    {
        var paths = GeneratedArtifactInventory.Create(DocumentAssembly.Definitions)
            .Select(static artifact => artifact.Path)
            .Order(StringComparer.Ordinal)
            .ToArray();
        var expected = DocumentAssembly.Definitions
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
