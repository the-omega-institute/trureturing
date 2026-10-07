using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.AtomContextFixture;

namespace StrataLint.Tests;

public sealed class SearchAtomsCommandTests
{
    [Fact]
    public void TextSearchNeedsOnlyScopedPathsAndTheirStoredText()
    {
        var id = new string('a', 64);
        var raw = RawRepositorySnapshot.Create([
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/source/residual-open/{id}.yaml", "invalid: ["),
            RawRepositoryEntry.FromText("Meta/Digestion/backfill/source/source.toml", "invalid = ["),
            RawRepositoryEntry.FromText(TheoryAtomizerDataLoader.DataPath, "invalid = ["),
            RawRepositoryEntry.FromText(DigestionCasStore.RootPath + id, "stored needle"),
        ]);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var result = SearchAtomsCommand.Run(gateway, ["--source", "source", "--text", "needle"]);
        Assert.True(result.Success, result.Error);
        Assert.Contains(id, result.Output, StringComparison.Ordinal);
        Assert.All(gateway.ScopedCurrentReads.SelectMany(static scope => scope), path =>
            Assert.Equal(DigestionQuerySelection.Literal(DigestionCasStore.RootPath + id), path));
    }
    [Theory]
    [InlineData("digest-status")]
    [InlineData("echo-verify")]
    public void RetiredGlobalQueriesHaveNoCliEntry(string command)
    {
        var console = new BufferedConsole();
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), null, null);
        var exit = CliApplication.Run([command], new ProductionCliEnvironment("/repo", gateway,
            new FakeLeanReportSource(null)), console);
        Assert.Equal(2, exit);
        Assert.Equal($"UNKNOWN_COMMAND {command}\n", console.Error);
        Assert.DoesNotContain(command, CliApplication.ImplementedCommands);
        Assert.Equal(0, gateway.ReadCount);
    }
    [Fact]
    public void SearchExcludesNoncanonicalNestedPaths()
    {
        var fixture = Create();
        var rogue = new string('a', 64);
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Append(
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/source/extra/residual-open/{rogue}.yaml", "invalid: [")));
        var result = SearchAtomsCommand.Run(new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null), ["--source", "source"]);
        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain(rogue, result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void TextSearchFindsPersistedChildAbsentFromCurrentAtomization()
    {
        var fixture = Create();
        var bytes = Encoding.UTF8.GetBytes("Explicit nested child needle.");
        var id = DigestionFingerprint.Compute(bytes).RawSha256[7..];
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Concat([
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/source/residual-open/{id}.yaml", "invalid: ["),
            new RawRepositoryEntry(DigestionCasStore.RootPath + id, [.. bytes]),
        ]));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var result = SearchAtomsCommand.Run(gateway, ["--source", "source", "--text", "needle"]);
        Assert.True(result.Success, result.Error);
        Assert.Contains(id, result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(static scope => scope),
            path => path.EndsWith(".yaml", StringComparison.Ordinal));
    }

    [Fact]
    public void SearchCombinesExplicitSourcesAndAppliesStateAndLimit()
    {
        var first = new string('a', 64);
        var second = new string('b', 64);
        var closed = new string('c', 64);
        var raw = RawRepositorySnapshot.Create([
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/a/residual-open/{first}.yaml", "invalid: ["),
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/b/residual-open/{second}.yaml", "invalid: ["),
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/b/absorbed-closed/{closed}.yaml", "invalid: ["),
        ]);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var result = SearchAtomsCommand.Run(gateway, ["--source", "b", "--source", "a", "--limit", "1"]);
        Assert.True(result.Success, result.Error);
        Assert.Contains(first, result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(second, result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(closed, result.Output, StringComparison.Ordinal);
        var selected = SearchAtomsCommand.Run(gateway, ["--source", "b", "--state", "absorbed-closed"]);
        Assert.True(selected.Success, selected.Error);
        Assert.Contains(closed, selected.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(second, selected.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void DefaultSearchIncludesIncompleteTailCoverage()
    {
        var id = new string('a', 64);
        var raw = RawRepositorySnapshot.Create([
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/source/partial-tail/{id}.yaml", "invalid: ["),
        ]);
        var result = SearchAtomsCommand.Run(new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null),
            ["--source", "source"]);
        Assert.True(result.Success, result.Error);
        Assert.Contains(id, result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void SearchListsOpenPathsWithoutReadingOrParsingTheirRecords()
    {
        var fixture = Create();
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Select(entry =>
            entry.Path.EndsWith(".yaml", StringComparison.Ordinal)
                ? new RawRepositoryEntry(entry.Path, [.. Encoding.UTF8.GetBytes("invalid: [")]) : entry));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var report = new FakeLeanReportSource(null);
        var console = new BufferedConsole();

        var exit = CliApplication.Run(["search-atoms", "--source", "source"],
            new ProductionCliEnvironment("/repo", gateway, report), console);

        Assert.Equal(0, exit);
        foreach (var atom in fixture.Atomized.Claims) Assert.Contains(Id(atom), console.Output, StringComparison.Ordinal);
        Assert.Equal(0, report.CallCount);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(static scope => scope),
            path => path.EndsWith(".yaml", StringComparison.Ordinal) || path == BackfillInventoryLoader.RootPath.TrimEnd('/'));
    }

    [Fact]
    public void TextSearchUsesOnlyTheSelectedTheoryAndReturnsMatchingAtoms()
    {
        var fixture = Create();
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Concat(
            fixture.Atomized.Claims.Select(atom => new RawRepositoryEntry(DigestionCasStore.RootPath + Id(atom), atom.RawBytes)))), null);
        var console = new BufferedConsole();

        var exit = CliApplication.Run(["search-atoms", "--source", "docs/source.md", "--text", "Middle"],
            new ProductionCliEnvironment("/repo", gateway, new FakeLeanReportSource(null)), console);

        Assert.Equal(0, exit);
        Assert.Contains(Id(fixture.Atomized.Claims[1]), console.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(Id(fixture.Atomized.Claims[0]), console.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(Id(fixture.Atomized.Claims[2]), console.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(static scope => scope),
            path => path.EndsWith(".yaml", StringComparison.Ordinal) || path.Contains(TheoryAtomizerDataLoader.DataPath, StringComparison.Ordinal));
    }

    [Fact]
    public void SearchRequiresAnExplicitScopeBeforeReading()
    {
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), null, null);
        var console = new BufferedConsole();

        var exit = CliApplication.Run(["search-atoms"],
            new ProductionCliEnvironment("/repo", gateway, new FakeLeanReportSource(null)), console);

        Assert.NotEqual(0, exit);
        Assert.Contains("--source", console.Error, StringComparison.Ordinal);
        Assert.Equal(0, gateway.ReadCount);
    }
}
