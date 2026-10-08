using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CoverAtomTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CoverIgnoresUnrelatedMalformedLedgerRecords(bool sameSource)
    {
        var inputs = new CoverSpec().Materialize();
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        var sourceId = sameSource
            ? Assert.Single(inputs.Document.RequireDigestionSources()).SourceId
            : "unrelated";
        var unrelatedPath = BackfillInventoryLoader.RootPath + sourceId
            + "/residual-open/" + new string('e', 64) + ".yaml";
        currentFiles[unrelatedPath] = "malformed: [\n";
        if (!sameSource)
            currentFiles[BackfillInventoryLoader.RootPath + sourceId + "/source.toml"] = "malformed = [\n";
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]),
            CoverWorld.Raw(currentFiles), CoverWorld.Raw(currentFiles));

        var result = CoverAtomCommand.Run(temporary.Path, repository,
            new FakeLeanReportSource(inputs.Report), CoverWorld.FixtureUtc,
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid]);

        Assert.True(result.Success, result.Error);
        Assert.Equal("malformed: [\n", File.ReadAllText(Path.Combine(temporary.Path, unrelatedPath)));
        Assert.DoesNotContain(repository.ScopedCurrentReads.SelectMany(static paths => paths),
            path => path == unrelatedPath || path == BackfillInventoryLoader.RootPath.TrimEnd('/'));
    }

    [Fact]
    public void CoverRejectsDuplicateTargetAcrossSources()
    {
        var inputs = new CoverSpec().Materialize();
        var source = Assert.Single(inputs.Document.RequireDigestionSources());
        var entry = Assert.Single(source.Entries);
        var duplicate = source with
        {
            SourceId = "duplicate", SourcePath = "docs/DUPLICATE.md",
            Entries = [entry with { SourceId = "duplicate", SourcePath = "docs/DUPLICATE.md" }],
        };
        var files = DirectoryLedgerTestSupport.Project(inputs.Files);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, inputs.Document.WithDigestionSources([source, duplicate]));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]), CoverWorld.Raw(files), CoverWorld.Raw(files));

        var result = CoverAtomCommand.Run(temporary.Path, repository,
            new FakeLeanReportSource(inputs.Report), CoverWorld.FixtureUtc,
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid]);

        Assert.False(result.Success);
        Assert.Contains("ambiguous", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
    }

    [Fact]
    public void CoverReadsTargetRecordsAndTheirInputsAndNoRevisionOrChangeSet()
    {
        const string unrelated = "docs/reports/unrelated.json";
        var inputs = new CoverSpec().Materialize();
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        var baselineFiles = DirectoryLedgerTestSupport.Project(inputs.Baseline);
        currentFiles[unrelated] = "{}\n";
        baselineFiles[unrelated] = "{}\n";
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create(Array.Empty<string>()),
            CoverWorld.Raw(currentFiles),
            CoverWorld.Raw(baselineFiles));

        var result = CoverAtomCommand.Run(
            temporary.Path,
            repository,
            new FakeLeanReportSource(inputs.Report),
            CoverWorld.FixtureUtc,
            ["--cover-atom", CoverWorld.DefaultAtomId, "--gid", inputs.Gid]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, repository.WholeTreeReadCount);
        Assert.Equal(2, repository.ScopedCurrentReads.Count);
        var source = Assert.Single(inputs.Document.RequireDigestionSources());
        Assert.Equal(
            [
                DigestionQuerySelection.Literal(BackfillInventoryLoader.RootPath + source.SourceId
                    + "/residual-open/" + CoverWorld.DefaultAtomId + ".yaml"),
                DigestionQuerySelection.Literal(BackfillInventoryLoader.RootPath + source.SourceId + "/source.toml"),
            ],
            repository.ScopedCurrentReads[0]);
        Assert.Equal(
            [
                TheoryAtomizerDataLoader.DataPath,
                "D5",
                "Reg",
                "Trureturing.lean",
                "Golden/Frozen/state",
                DigestionQuerySelection.Literal(source.SourcePath),
            ],
            repository.ScopedCurrentReads[1]);
        Assert.All(repository.ScopedCurrentReads.SelectMany(static scope => scope),
            static path => Assert.DoesNotContain("docs/reports", path, StringComparison.Ordinal));
        Assert.Empty(repository.ReadRevisionCalls);
        Assert.Empty(repository.ReadChangesCalls);
    }

    [Fact]
    public void ScopedReadsReturnOnlyTheRequestedPaths()
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["Meta/domains.yaml"] = "domains\n",
            ["Meta/Digestion/atomizers.toml"] = "rules\n",
            ["D5/S0/Carrier/Probe.lean"] = "theorem probe : True := True.intro\n",
            ["D5.lean"] = "sibling of the D5 directory\n",
            ["docs/source.md"] = "source\n",
            ["docs/reports/unrelated.json"] = "{}\n",
        };
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create(Array.Empty<string>()), CoverWorld.Raw(files), CoverWorld.Raw(files));

        var current = repository.ReadCurrent(["Meta", "D5", "docs/source.md"]);

        Assert.Equal(
            ["D5/S0/Carrier/Probe.lean", "Meta/Digestion/atomizers.toml", "Meta/domains.yaml", "docs/source.md"],
            current.Entries.Select(static entry => entry.Path).Order(StringComparer.Ordinal).ToArray());
    }
}
