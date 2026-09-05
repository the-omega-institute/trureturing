namespace StrataLint.Scribe.Tests;

public sealed class DagEmitterTests
{
    [Fact]
    public void TheProjectionIsDeclaredInTheGeneratedArtifactInventory()
    {
        // FileMapPolicy cross-checks this inventory against Meta/FILEMAP.toml, so an artifact that
        // ships without an entry is an ungoverned generated file.
        var inventory = GeneratedArtifactInventory.Create(DocumentAssembly.Definitions);
        var artifact = Assert.Single(
            inventory.Where(static item => item.Path == DagEmitter.RelativePath));

        Assert.Equal(nameof(DagEmitter), artifact.Producer);

        var truthArtifact = Assert.Single(
            inventory.Where(static item => item.Path == DagEmitter.TruthGraphRelativePath));
        Assert.Equal(nameof(DagEmitter), truthArtifact.Producer);
    }
}
