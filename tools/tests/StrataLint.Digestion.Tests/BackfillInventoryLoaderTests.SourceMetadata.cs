using StrataLint.Engine;

namespace StrataLint.Digestion.Tests;

public sealed partial class BackfillInventoryLoaderTests
{
    [Fact]
    public void SourceMetadataRejectsHistoricalSchemaInCandidate()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (sourcePath,
                "source_id = \"delta-v0.1\"\n"
                + "path = \"docs/delta.md\"\n"
                + "atomizer = \"none\"\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));

        Assert.Equal($"source metadata keys are not canonical: {sourcePath}", exception.Message);
    }

    [Fact]
    public void SourceMetadataRejectsInvalidGenreRegistryCheck()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var exception = Assert.Throws<FormatException>(() => BackfillInventoryLoader.Load(Snapshot(
            (sourcePath,
                "source_id = \"delta-v0.1\"\n"
                + "path = \"docs/delta.md\"\n"
                + "atomizer = \"pzg-v1\"\n"
                + "genre_registry_check = \"unknown\"\n"
                + "unregistered_genres = []\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta"))));

        Assert.Equal($"invalid genre_registry_check: {sourcePath}", exception.Message);
    }
}
