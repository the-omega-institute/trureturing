using StrataLint.Engine;

namespace StrataLint.Tests;

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
    public void SourceMetadataAcceptsHistoricalSchemaOnlyInBaseline()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            (sourcePath,
                "source_id = \"delta-v0.1\"\n"
                + "path = \"docs/delta.md\"\n"
                + "atomizer = \"none\"\n"
                + "acknowledged_stale = [\"old-one\"]\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta")));

        var source = Assert.Single(document.RequireDigestionSources());
        Assert.Equal(["old-one"], source.AcknowledgedStale.ToArray());
        AssertGenreRegistryProjectionUnavailable(source);
    }

    [Fact]
    public void BaselineCurrentSchemaGenreProjectionIsAlsoUnavailable()
    {
        var sourcePath = $"{BackfillInventoryLoader.RootPath}delta-v0.1/source.toml";
        var document = BackfillInventoryLoader.LoadBaseline(Snapshot(
            (sourcePath,
                "source_id = \"delta-v0.1\"\n"
                + "path = \"docs/delta.md\"\n"
                + "atomizer = \"pzg-v1\"\n"
                + "genre_registry_check = \"collected\"\n"
                + "unregistered_genres = [\"未登记体\"]\n"),
            Atom("delta-v0.1", "residual-open", "delta-atom", "theorem/delta")));

        AssertGenreRegistryProjectionUnavailable(
            Assert.Single(document.RequireDigestionSources()));
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
