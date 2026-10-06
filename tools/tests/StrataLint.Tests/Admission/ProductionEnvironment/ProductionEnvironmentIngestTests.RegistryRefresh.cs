using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Theory]
    [InlineData("fixture-source")]
    [InlineData(RuleFixture.FixtureDigestionSourcePath)]
    public void RegistryRefreshRewritesOnlyTheSelectedSourceMetadata(string selector)
    {
        var fixture = RegistryRefreshFixture();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var reports = new FakeLeanReportSource(null);
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), null),
            reports,
            new FakeScribeEmissionVerifier(null));

        var applied = environment.AlignDigestionStatus(["--refresh-source", selector]);

        Assert.True(applied.Success, applied.Error);
        Assert.Equal(
            "REGISTRY_REFRESH source=fixture-source "
                + "path=Meta/Digestion/backfill/fixture-source/source.toml changed=true applied=true\n",
            applied.Output);
        Assert.Equal(0, reports.CallCount);
        var after = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var source = Assert.Single(after.RequireDigestionSources());
        Assert.Equal(GenreRegistryCheckKind.Collected, source.GenreRegistryCheck.Kind);
        Assert.Equal(["更正命题"], source.GenreRegistryCheck.UnregisteredGenres.ToArray());
        Assert.Equal(
            BackfillInventoryWriter.WriteAtom(Assert.Single(before.RequireDigestionEntries())).ToArray(),
            BackfillInventoryWriter.WriteAtom(Assert.Single(after.RequireDigestionEntries())).ToArray());

        fixture.Files["Meta/Digestion/backfill/fixture-source/source.toml"] =
            Encoding.UTF8.GetString(BackfillInventoryWriter.WriteSourceMetadata(source).AsSpan());
        var again = RegistryRefreshEnvironment(temporary.Path, fixture)
            .AlignDigestionStatus(["--refresh-source", selector]);
        Assert.True(again.Success, again.Error);
        Assert.Contains("changed=false", again.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void RegistryRefreshPlanReportsTheChangeWithoutWriting()
    {
        var fixture = RegistryRefreshFixture();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path));

        var plan = RegistryRefreshEnvironment(temporary.Path, fixture)
            .AlignDigestionStatus(["--refresh-source", "fixture-source", "--plan"]);

        Assert.True(plan.Success, plan.Error);
        Assert.Contains("changed=true applied=false", plan.Output, StringComparison.Ordinal);
        Assert.Equal(before, RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    [Fact]
    public void RegistryRefreshRejectsAmbiguousSourcePathWithoutWriting()
    {
        var fixture = RegistryRefreshFixture();
        var document = BackfillInventoryLoader.Load(Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(Snapshot(fixture.Files))).Snapshot);
        var source = Assert.Single(document.RequireDigestionSources());
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files,
            document.WithDigestionSources([source, source with { SourceId = "second-source", Entries = [] }]));
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path));
        var result = RegistryRefreshEnvironment(temporary.Path, fixture).AlignDigestionStatus(
            ["--refresh-source", source.SourcePath]);
        Assert.False(result.Success);
        Assert.Contains("exactly one existing source", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    [Theory]
    [InlineData("missing-source")]
    [InlineData("docs/develop/theory/unregistered.md")]
    [InlineData("")]
    public void RegistryRefreshRejectsInvalidSelectorWithoutWriting(string selector)
    {
        var fixture = RegistryRefreshFixture();
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path));
        var result = RegistryRefreshEnvironment(temporary.Path, fixture).AlignDigestionStatus(
            ["--refresh-source", selector]);
        Assert.False(result.Success);
        Assert.Contains("REGISTRY_REFRESH_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    [Fact]
    public void RegistryRefreshRejectsDanglingSourceWithoutWriting()
    {
        var fixture = RegistryRefreshFixture();
        fixture.Files.Remove(RuleFixture.FixtureDigestionSourcePath);
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var before = RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path));
        var result = RegistryRefreshEnvironment(temporary.Path, fixture).AlignDigestionStatus(
            ["--refresh-source", "fixture-source"]);
        Assert.False(result.Success);
        Assert.Contains("source path is dangling", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, RegistryBytes(BackfillInventoryLoader.LoadRoot(temporary.Path)));
    }

    private static byte[] RegistryBytes(BackfillInventoryDocument document) =>
        document.RequireDigestionSources().SelectMany(source => BackfillInventoryWriter.WriteSourceMetadata(source))
            .Concat(document.RequireDigestionEntries().SelectMany(entry => BackfillInventoryWriter.WriteAtom(entry))).ToArray();

    private static RuleFixture RegistryRefreshFixture()
    {
        var fixture = new RuleFixture();
        const string atomizer = "dialect:qdo";
        const string source = "# QDO\n\n## 更正命题 40.2\n\nopen。\n";
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = source;
        var atom = Assert.Single(AtomizerRegistry.Atomize(atomizer, Encoding.UTF8.GetBytes(source), DigestionTestSupport.Rules).Claims);
        InstallDirectoryLedger(fixture, atomizer, atom);
        fixture.Files["docs/develop/theory/unregistered.md"] = "# New\n\n**定理 1.1**。new。\n";
        return fixture;
    }

    private static ProductionCliEnvironment RegistryRefreshEnvironment(string root, RuleFixture fixture) =>
        new(root, new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), null),
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(null));
}
