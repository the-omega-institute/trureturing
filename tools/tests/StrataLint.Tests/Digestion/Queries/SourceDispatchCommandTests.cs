using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.AtomContextFixture;

namespace StrataLint.Tests;

public sealed partial class SourceDispatchCommandTests
{
    [Fact]
    public void BatchIsReversibleIdempotentLocalAndPreservesEveryOtherByte()
    {
        using var temporary = new TemporaryDirectory();
        var raw = RawRepositorySnapshot.Create([
            Metadata("alpha"), Metadata("beta"),
            RawRepositoryEntry.FromText("Meta/Digestion/backfill/unrelated/source.toml", "invalid = ["),
            RawRepositoryEntry.FromText("Meta/Digestion/backfill/alpha/residual-open/" + new string('a', 64) + ".yaml", "invalid: ["),
            RawRepositoryEntry.FromText(DigestionCasStore.RootPath + new string('a', 64), "immutable CAS"),
        ]);
        Write(temporary.Path, raw);
        var before = Image(temporary.Path);
        var gateway = Gateway(raw);
        var result = SourceDispatchCommand.Run(temporary.Path, gateway,
            ["--source", "alpha", "--source", "docs/beta.md", "--source", "alpha", "--default", "excluded"]);
        Assert.True(result.Success, result.Error);
        Assert.Contains("changed=2", result.Output, StringComparison.Ordinal);
        Assert.Empty(SearchAtomsCommand.Run(Gateway(Read(temporary.Path)),
            ["--source", "alpha", "--selection", "default-dispatch"]).Output);
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.All(gateway.ScopedCurrentReads.SelectMany(scope => scope),
            path => Assert.EndsWith("/source.toml", path, StringComparison.Ordinal));
        var after = Read(temporary.Path);
        foreach (var original in raw.Entries)
        {
            var current = after.Entries.Single(entry => entry.Path == original.Path);
            var suffix = original.Path == MetadataPath("alpha") || original.Path == MetadataPath("beta")
                ? Encoding.UTF8.GetBytes("default_dispatch = \"excluded\"\n") : [];
            Assert.Equal(original.Bytes.Concat(suffix), current.Bytes);
        }
        var calls = 0;
        result = SourceDispatchCommand.Run(temporary.Path, Gateway(after),
            ["--source", "alpha", "--source", "beta", "--default", "excluded"],
            commit: (_, _) => calls++);
        Assert.True(result.Success, result.Error);
        Assert.Contains("changed=0", result.Output, StringComparison.Ordinal);
        Assert.Equal(0, calls);
        Assert.Equal(Image(after), Image(Read(temporary.Path)));
        result = SourceDispatchCommand.Run(temporary.Path, Gateway(after),
            ["--source", "alpha", "--source", "beta", "--default", "eligible"]);
        Assert.True(result.Success, result.Error);
        Assert.Equal(before, Image(temporary.Path));
        Assert.Contains(new string('a', 64), SearchAtomsCommand.Run(Gateway(Read(temporary.Path)),
            ["--source", "alpha", "--selection", "default-dispatch"]).Output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("../invalid")]
    [InlineData("docs/shared.md")]
    [InlineData("bad")]
    public void InvalidMixedBatchRejectsBeforeWritingAnySource(string selector)
    {
        using var temporary = new TemporaryDirectory();
        var raw = RawRepositorySnapshot.Create([
            Metadata("alpha"), Metadata("one", path: "docs/shared.md"), Metadata("two", path: "docs/shared.md"),
            RawRepositoryEntry.FromText(MetadataPath("bad"), "invalid = ["),
        ]);
        Write(temporary.Path, raw);
        var before = Image(temporary.Path);
        var commits = 0;
        var result = SourceDispatchCommand.Run(temporary.Path, Gateway(raw),
            ["--source", "alpha", "--source", selector, "--default", "excluded"],
            commit: (_, _) => commits++);
        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal(0, commits);
        Assert.Equal(before, Image(temporary.Path));
    }

    [Theory]
    [InlineData("\"eligible\"")]
    [InlineData("\"unknown\"")]
    [InlineData("true")]
    [InlineData("[\"excluded\"]")]
    [InlineData("\"excluded\"\ndefault_dispatch = \"excluded\"")]
    public void StrictSelectedMetadataRejectsInvalidChoiceWithoutPartialWrite(string encoded)
    {
        using var temporary = new TemporaryDirectory();
        var raw = RawRepositorySnapshot.Create([
            Metadata("alpha"),
            RawRepositoryEntry.FromText(MetadataPath("beta"),
                Encoding.UTF8.GetString(Metadata("beta").Bytes.AsSpan()) + "default_dispatch = " + encoded + "\n"),
        ]);
        Write(temporary.Path, raw);
        var before = Image(temporary.Path);
        var result = SourceDispatchCommand.Run(temporary.Path, Gateway(raw),
            ["--source", "alpha", "--source", "beta", "--default", "excluded"]);
        Assert.False(result.Success);
        Assert.Equal(before, Image(temporary.Path));
    }

    [Fact]
    public void OptimisticConflictChecksEvenUnchangedSelectedSourceBeforeAnyWrite()
    {
        using var temporary = new TemporaryDirectory();
        var raw = RawRepositorySnapshot.Create([Metadata("alpha"), Metadata("beta", excluded: true)]);
        Write(temporary.Path, raw);
        var alpha = File.ReadAllBytes(Path.Combine(temporary.Path, MetadataPath("alpha")));
        var result = SourceDispatchCommand.Run(temporary.Path, Gateway(raw),
            ["--source", "alpha", "--source", "beta", "--default", "excluded"],
            beforeCommit: () => File.AppendAllText(Path.Combine(temporary.Path, MetadataPath("beta")), "changed\n"));
        Assert.False(result.Success);
        Assert.Contains("changed before dispatch update", result.Error, StringComparison.Ordinal);
        Assert.Equal(alpha, File.ReadAllBytes(Path.Combine(temporary.Path, MetadataPath("alpha"))));
        Assert.EndsWith("changed\n", File.ReadAllText(Path.Combine(temporary.Path, MetadataPath("beta"))), StringComparison.Ordinal);
    }

    [Fact]
    public void FailureOnSecondCommitRollsBackWholeBatch()
    {
        using var temporary = new TemporaryDirectory();
        var raw = RawRepositorySnapshot.Create([Metadata("alpha"), Metadata("beta")]);
        Write(temporary.Path, raw);
        var before = Image(temporary.Path);
        var commits = 0;
        var result = SourceDispatchCommand.Run(temporary.Path, Gateway(raw),
            ["--source", "alpha", "--source", "beta", "--default", "excluded"], commit: (pending, target) =>
            {
                if (++commits == 2) throw new IOException("injected second write failure");
                File.Move(pending, target, overwrite: true);
            });
        Assert.False(result.Success);
        Assert.Contains("injected second write failure", result.Error, StringComparison.Ordinal);
        Assert.Equal(2, commits);
        Assert.Equal(before, Image(temporary.Path));
        Assert.Empty(Directory.EnumerateFiles(temporary.Path, "*.tmp", SearchOption.AllDirectories));
    }

    [Fact]
    public void PrefixRelatedSourcesWorkThroughProductionBatchAndSearch()
    {
        using var temporary = new TemporaryDirectory();
        TestGit.Run(temporary.Path, "init");
        var first = new string('a', 64);
        var second = new string('b', 64);
        var raw = RawRepositorySnapshot.Create([
            Metadata("alpha"), Metadata("alpha-ml"),
            RawRepositoryEntry.FromText(MetadataPath("unrelated"), "invalid = ["),
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/alpha/residual-open/{first}.yaml", "invalid: ["),
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/alpha-ml/residual-open/{second}.yaml", "invalid: ["),
            RawRepositoryEntry.FromText(DigestionCasStore.RootPath + first, "immutable CAS"),
        ]);
        Write(temporary.Path, raw);
        var before = Image(temporary.Path);
        var environment = new ProductionCliEnvironment(temporary.Path,
            new GitRepositoryGateway(temporary.Path), new FakeLeanReportSource(null));
        string[] sources = ["--source", "alpha", "--source", "docs/alpha-ml.md", "--source", "alpha-ml"];
        var inspect = environment.SourceDispatch(sources);
        Assert.True(inspect.Success, inspect.Error);
        Assert.Contains("source_id=alpha default=eligible", inspect.Output, StringComparison.Ordinal);
        Assert.Contains("source_id=alpha-ml default=eligible", inspect.Output, StringComparison.Ordinal);
        var search = environment.SearchAtoms([.. sources, "--selection", "default-dispatch"]);
        Assert.True(search.Success, search.Error);
        Assert.Contains(first, search.Output, StringComparison.Ordinal);
        Assert.Contains(second, search.Output, StringComparison.Ordinal);
        var cached = environment.SearchAtoms(["--selection", "default-dispatch", "--atom-id", first, "--atom-id", second]);
        Assert.True(cached.Success, cached.Error);
        Assert.Equal(search.Output, cached.Output);
        var update = environment.SourceDispatch([.. sources, "--default", "excluded"]);
        Assert.True(update.Success, update.Error);
        Assert.Contains("changed=2", update.Output, StringComparison.Ordinal);
        var selected = environment.SearchAtoms([.. sources, "--selection", "default-dispatch"]);
        Assert.True(selected.Success, selected.Error);
        Assert.Empty(selected.Output);
        var again = environment.SourceDispatch([.. sources, "--default", "excluded"]);
        Assert.True(again.Success, again.Error);
        Assert.Contains("changed=0", again.Output, StringComparison.Ordinal);
        var restored = environment.SourceDispatch([.. sources, "--default", "eligible"]);
        Assert.True(restored.Success, restored.Error);
        Assert.Equal(before, Image(temporary.Path));
    }

    private static RawRepositoryEntry Metadata(string id, bool excluded = false, string? path = null) =>
        new(MetadataPath(id), BackfillInventoryWriter.WriteSourceMetadata(new(id, path ?? $"docs/{id}.md",
            "generic-v1", ["sha256:" + new string('d', 64)],
            GenreRegistryProjection.Available(GenreRegistryCheck.Collected(["Custom"])), [],
            excluded ? DigestionDefaultDispatch.Excluded : DigestionDefaultDispatch.Eligible)));
    private static string MetadataPath(string id) => BackfillInventoryLoader.RootPath + id + "/source.toml";
    private static FakeRepositoryGateway Gateway(RawRepositorySnapshot raw) => new(RawChangeSet.Create([]), raw, null);
    private static void Write(string root, RawRepositorySnapshot raw)
    {
        foreach (var entry in raw.Entries)
        {
            var path = Path.Combine(root, entry.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, entry.Bytes.ToArray());
        }
    }
    private static RawRepositorySnapshot Read(string root) => RawRepositorySnapshot.Create(
        Directory.EnumerateFiles(root, "*", SearchOption.AllDirectories).Select(path =>
            new RawRepositoryEntry(Path.GetRelativePath(root, path).Replace('\\', '/'), [.. File.ReadAllBytes(path)])));
    private static string Image(string root) => Image(Read(root));
    private static string Image(RawRepositorySnapshot raw) => string.Join("\n", raw.Entries
        .OrderBy(entry => entry.Path, StringComparer.Ordinal).Select(entry => entry.Path + ":" + Convert.ToHexString(entry.Bytes.AsSpan())));
}
