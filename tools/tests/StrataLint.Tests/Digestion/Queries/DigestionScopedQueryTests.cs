using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.AtomContextFixture;

namespace StrataLint.Tests;

public sealed class DigestionScopedQueryTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void QueryIgnoresUnrelatedBrokenTheory(bool context)
    {
        var fixture = Create();
        var target = Id(fixture.Atomized.Claims[1]);
        var raw = RawRepositorySnapshot.Create(WithCas(fixture).Entries.Concat(
        [
            Entry("Meta/Digestion/backfill/unrelated/source.toml", "invalid = ["),
            Entry("Meta/Digestion/backfill/unrelated/residual-open/" + new string('a', 64) + ".yaml", "invalid: ["),
            Entry("docs/unrelated.md", "unrelated theory"),
        ]));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var environment = new ProductionCliEnvironment("/repo", gateway, new FakeLeanReportSource(null));

        var result = context ? environment.AtomContext(["--atom-id", target])
            : environment.ShowAtom(["--atom-id", target]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("Middle.", result.Output, StringComparison.Ordinal);
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(static paths => paths),
            path => path == BackfillInventoryLoader.RootPath.TrimEnd('/'));
    }

    [Fact]
    public void ShowDoesNotParseOtherRecordsInItsOwnTheory()
    {
        var fixture = Create();
        var target = Id(fixture.Atomized.Claims[1]);
        var raw = RawRepositorySnapshot.Create(WithCas(fixture).Entries.Select(entry =>
            entry.Path.EndsWith(Id(fixture.Atomized.Claims[0]) + ".yaml", StringComparison.Ordinal)
                ? Entry(entry.Path, "invalid: [") : entry));
        var environment = new ProductionCliEnvironment("/repo",
            new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null), new FakeLeanReportSource(null));

        var result = environment.ShowAtom(["--atom-id", target]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("Middle.", result.Output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SourceSelectorLimitsDuplicateIdentitySearch(bool context)
    {
        var fixture = Create();
        var target = Id(fixture.Atomized.Claims[1]);
        var raw = WithCas(fixture);
        var duplicate = raw.Entries.Where(entry => entry.Path.StartsWith("Meta/Digestion/backfill/source/", StringComparison.Ordinal))
            .Select(entry => Entry(entry.Path.Replace("/source/", "/other/", StringComparison.Ordinal),
                Encoding.UTF8.GetString(entry.Bytes.AsSpan()).Replace("source_id = \"source\"", "source_id = \"other\"", StringComparison.Ordinal)
                    .Replace("docs/source.md", "docs/other.md", StringComparison.Ordinal)));
        var environment = new ProductionCliEnvironment("/repo",
            new FakeRepositoryGateway(RawChangeSet.Create([]), RawRepositorySnapshot.Create(raw.Entries.Concat(duplicate)), null),
            new FakeLeanReportSource(null));

        var unscoped = context ? environment.AtomContext(["--atom-id", target]) : environment.ShowAtom(["--atom-id", target]);
        var scoped = context ? environment.AtomContext(["--source", "source", "--atom-id", target])
            : environment.ShowAtom(["--atom-id", target, "--source", "docs/source.md"]);

        Assert.False(unscoped.Success);
        Assert.True(scoped.Success, scoped.Error);
        Assert.Contains("source_id=source", scoped.Output, StringComparison.Ordinal);
    }

    private static RawRepositoryEntry Entry(string path, string text) =>
        new(path, [.. Encoding.UTF8.GetBytes(text)]);

    [Fact]
    public void ContextLoadsReferencedChildFromAnotherTheory()
    {
        var fixture = Create(ListClaims, expand: true);
        var child = fixture.Ledger.RequireDigestionEntries().Single(entry =>
            entry.AtomId == Id(fixture.Atomized.ClausePlans.Single().Children[0]));
        var source = fixture.Ledger.RequireDigestionSources().Single();
        fixture = fixture with { Ledger = fixture.Ledger.WithDigestionSources(
        [
            source with { Entries = [.. source.Entries.Where(entry => entry.AtomId != child.AtomId)] },
            source with { SourceId = "imported", SourcePath = "docs/imported.md",
                Entries = [child with { SourceId = "imported", SourcePath = "docs/imported.md" }] },
        ]) };
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Concat(
            fixture.Atomized.ClausePlans.Single().Children.Select(atom =>
                new RawRepositoryEntry(DigestionCasStore.RootPath + Id(atom), atom.RawBytes))));
        var environment = new ProductionCliEnvironment("/repo",
            new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null), new FakeLeanReportSource(null));

        var result = environment.AtomContext(["--atom-id", Id(fixture.Atomized.Claims[0]), "--source", "source"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains($"NEXT atom_id={child.AtomId}", result.Output, StringComparison.Ordinal);
        Assert.Contains("Alpha", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void PathSearchSeesUntrackedRecordsAndCurrentDeletion()
    {
        using var temporary = new TemporaryDirectory();
        TestGit.Run(temporary.Path, "init");
        var fixture = Create();
        var target = Id(fixture.Atomized.Claims[1]);
        foreach (var entry in WithCas(fixture).Entries)
        {
            var path = Path.Combine(temporary.Path, entry.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, entry.Bytes.ToArray());
        }
        var environment = new ProductionCliEnvironment(temporary.Path,
            new GitRepositoryGateway(temporary.Path), new FakeLeanReportSource(null));
        var untracked = environment.ShowAtom(["--atom-id", target]);
        Assert.True(untracked.Success, untracked.Error);
        TestGit.Run(temporary.Path, "add", ".");
        var record = WithCas(fixture).Entries.Single(entry => entry.Path.EndsWith(target + ".yaml", StringComparison.Ordinal));
        File.Delete(Path.Combine(temporary.Path, record.Path));

        var deleted = environment.ShowAtom(["--atom-id", target]);

        Assert.False(deleted.Success);
        Assert.Contains("absent", deleted.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ContextDoesNotReadDistantRecordsInItsTheory()
    {
        var fixture = Create();
        var target = Id(fixture.Atomized.Claims[0]);
        var distant = Id(fixture.Atomized.Claims[2]);
        var raw = RawRepositorySnapshot.Create(WithCas(fixture).Entries.Select(entry =>
            entry.Path.EndsWith(distant + ".yaml", StringComparison.Ordinal) ? Entry(entry.Path, "broken: [" + target) : entry));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var result = new ProductionCliEnvironment("/repo", gateway, new FakeLeanReportSource(null))
            .AtomContext(["--atom-id", target]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("Middle.", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(static paths => paths),
            path => path == BackfillInventoryLoader.RootPath + "source");
    }

    [Fact]
    public void SourceSelectorIsLiteral()
    {
        var fixture = Create();
        using var temporary = new TemporaryDirectory();
        TestGit.Run(temporary.Path, "init");
        foreach (var entry in WithCas(fixture).Entries)
        {
            var path = Path.Combine(temporary.Path, entry.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, entry.Bytes.ToArray());
        }
        var environment = new ProductionCliEnvironment(temporary.Path,
            new GitRepositoryGateway(temporary.Path), new FakeLeanReportSource(null));

        var result = environment.ShowAtom(["--atom-id", Id(fixture.Atomized.Claims[0]), "--source", "sourc?"]);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
    }

    [Fact]
    public void ContextRejectsChangedMatchedRecord()
    {
        var fixture = Create();
        var target = Id(fixture.Atomized.Claims[1]);
        var original = WithCas(fixture);
        var changed = RawRepositorySnapshot.Create(original.Entries.Select(entry =>
            entry.Path.EndsWith(target + ".yaml", StringComparison.Ordinal)
                ? Entry(entry.Path, Encoding.UTF8.GetString(entry.Bytes.AsSpan()) + "\n") : entry));
        var reads = 0;
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), null, null,
            currentReader: () => ++reads > 2 ? changed : original);

        var result = new ProductionCliEnvironment("/repo", gateway, new FakeLeanReportSource(null))
            .AtomContext(["--atom-id", target]);

        Assert.False(result.Success);
        Assert.Contains("changed during", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ContextIncludesDirectAndChainOccurrencesOfSameRecord()
    {
        var seed = Create(ListClaims, expand: true);
        var child = seed.Atomized.ClausePlans.Single().Children[0];
        var fixture = Create(Encoding.UTF8.GetString(child.RawBytes.AsSpan()) + ListClaims, expand: true);
        Assert.Contains(fixture.Atomized.Claims, atom => Id(atom) == Id(child));
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Concat(
            fixture.Atomized.ClausePlans.SelectMany(static plan => plan.Children)
                .Select(atom => new RawRepositoryEntry(DigestionCasStore.RootPath + Id(atom), atom.RawBytes))));

        var result = new ProductionCliEnvironment("/repo",
            new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null), new FakeLeanReportSource(null))
            .AtomContext(["--atom-id", Id(child)]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("occurrences=2", result.Output, StringComparison.Ordinal);
    }

    private static RawRepositorySnapshot WithCas(AtomContextFixture fixture) =>
        RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Concat(fixture.Atomized.Claims.Select(atom =>
            new RawRepositoryEntry(DigestionCasStore.RootPath + Id(atom), atom.RawBytes))));
}
