using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void IngestAdmitsDeclaredDialectOpenGenresAndRecordsTheirProjection()
    {
        const string atomizerId = "dialect:qdo";
        var fixture = new RuleFixture();
        var sourceBytes = Encoding.UTF8.GetBytes(
            "# QDO\n\n## 定理 40.1\n\nknown。\n\n## 未登记体 40.2\n\nopen。\n");
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            DirectoryLedgerTestSupport.ReplaceWithProjection(files, EmptyRegisteredLedger(atomizerId));
            files.Remove(RuleFixture.FixtureCasPath);
        }

        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("residual_open_added=2", result.Output, StringComparison.Ordinal);
        Assert.Contains("open_genres=1", result.Output, StringComparison.Ordinal);
        Assert.Contains("INGEST_OPEN_GENRE source=fixture-source token=\"未登记体\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("code=unregistered-genre detail=\"未登记体\"", result.Output, StringComparison.Ordinal);
        var written = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var source = Assert.Single(written.RequireDigestionSources());
        Assert.Equal(GenreRegistryCheckKind.Collected, source.GenreRegistryCheck.Kind);
        Assert.Equal(["未登记体"], source.GenreRegistryCheck.UnregisteredGenres.ToArray());
        Assert.Equal(
            ["theorem/40.1", "unregistered/%E6%9C%AA%E7%99%BB%E8%AE%B0%E4%BD%93/40.2"],
            source.Entries.Select(static entry => entry.AstPath).Order(StringComparer.Ordinal).ToArray());
        Assert.All(source.Entries, static entry => Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            entry.ProjectedStatus));
    }

    [Fact]
    public void IngestRoundTripsObserverOpenGenreWithTomlEscapes()
    {
        const string token = "**新\"判\\词。**";
        var fixture = new RuleFixture();
        var sourceBytes = Encoding.UTF8.GetBytes($"# Observer\n\n{token} unknown。\n");
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(sourceBytes);
        foreach (var files in new[] { fixture.Files, fixture.Baseline })
        {
            DirectoryLedgerTestSupport.ReplaceWithProjection(
                files,
                EmptyRegisteredLedger(AtomizerRegistry.ObserverId));
            files.Remove(RuleFixture.FixtureCasPath);
        }

        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(Array.Empty<string>()),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.AlignDigestionStatus(["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var source = Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path)
            .RequireDigestionSources());
        Assert.Equal([token], source.GenreRegistryCheck.UnregisteredGenres.ToArray());
        Assert.Equal(
            UnregisteredGenreLocator.ForToken(token),
            Assert.Single(source.Entries).AstPath);
        // The loader already requires the committed bytes to equal the writer's canonical
        // output, so asserting the writer proves what the file holds without reading a
        // path the conservative test-map parser cannot resolve.
        Assert.Contains(
            "unregistered_genres = [\"**新\\\"判\\\\词。**\"]",
            Encoding.UTF8.GetString(
                BackfillInventoryWriter.WriteSourceMetadata(source).AsSpan()),
            StringComparison.Ordinal);
    }

}
