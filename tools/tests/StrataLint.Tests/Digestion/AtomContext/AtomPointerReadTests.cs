using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.AtomContextFixture;

namespace StrataLint.Tests;

public sealed class AtomPointerReadTests
{
    [Theory]
    [InlineData("delete")]
    [InlineData("edit")]
    [InlineData("move")]
    public void ColdAndWarmIdReadsUseOnlySavedRelationsAndBodies(string change)
    {
        var f = Create(ListClaims, expand: true);
        var raw = RawRepositorySnapshot.Create(f.RawSnapshot().Entries.Where(file => file.Path != SourcePath)
            .Concat(change == "delete" ? [] : new[] { RawRepositoryEntry.FromText(
                change == "move" ? "docs/moved.md" : SourcePath, "## Replacement scope\n\nUnrelated replacement.\n") }));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var id = Id(f.Atomized.ClausePlans.Single().Children[1]);
        for (var i = 0; i < 2; i++)
        {
            var result = AtomContextCommand.Run(gateway, ["--atom-id", id]);
            Assert.True(result.Success, result.Error);
            Assert.Contains("Beta;", result.Output, StringComparison.Ordinal);
            Assert.Contains("governed-list", result.Output, StringComparison.Ordinal);
        }
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(paths => paths), path =>
            path.Contains("docs/", StringComparison.Ordinal) || path == DigestionCasStore.RootPath
            || path == BackfillInventoryLoader.RootPath + "source");
        Assert.All(gateway.CurrentPathSearches.SelectMany(paths => paths), path =>
            Assert.Contains(".yaml", path, StringComparison.Ordinal));
    }

    [Fact]
    public void MissingPointerDoesNotFallBackToCurrentProse()
    {
        var f = Create();
        var raw = RawRepositorySnapshot.Create(f.RawSnapshot().Entries.Where(file => !file.Path.Contains("/context/", StringComparison.Ordinal)));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var result = AtomContextCommand.Run(gateway, ["--atom-id", Id(f.Atomized.Claims[1])]);
        Assert.False(result.Success);
        Assert.Contains("CONTEXT_UNAVAILABLE", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(paths => paths), path => path.Contains(SourcePath, StringComparison.Ordinal));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MissingOrCorruptNeighborIsNeverRenderedAsSourceBoundary(bool corrupt)
    {
        var f = Create();
        var path = DigestionCasStore.RootPath + Id(f.Atomized.Claims[0]);
        var raw = RawRepositorySnapshot.Create(f.RawSnapshot(false).Entries.Where(file => file.Path != path)
            .Concat(corrupt ? new[] { RawRepositoryEntry.FromText(path, "corrupt") } : []));
        var result = AtomContextCommand.Run(new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null),
            ["--atom-id", Id(f.Atomized.Claims[1])]);
        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Contains(corrupt ? "CAS_MISMATCH" : "CAS_MISSING", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void SavedVersionsKeepDistinctOccurrenceScopes()
    {
        var old = Create("# Old scope\n\n## Theorem 1.1\n\nSame.\n");
        var fresh = Create("# New scope\n\n## Theorem 1.1\n\nSame.\n");
        var common = old.Ledger.RequireDigestionEntries().Select(entry => entry.AtomId)
            .Intersect(fresh.Ledger.RequireDigestionEntries().Select(entry => entry.AtomId)).Single();
        var raw = DigestionContextPointerStore.Add(old.RawSnapshot(false), fresh.ContextIndex!);
        raw = RawRepositorySnapshot.Create(raw.Entries.Concat(fresh.ContextCas
            .Where(item => !raw.Entries.Any(file => file.Path == item.RelativePath))
            .Select(item => new RawRepositoryEntry(item.RelativePath, item.Bytes))));
        var decoded = DigestionQuerySelection.Load(raw);
        var contexts = DigestionAtomContextProjection.ResolveOccurrences(decoded.Snapshot, old.Ledger, common);
        Assert.Equal(2, contexts.Length);
        Assert.Equal(2, contexts.Select(context => context.SourceSha256).Distinct().Count());
        var scopes = contexts.SelectMany(context => context.GoverningContext)
            .Select(scope => Encoding.UTF8.GetString(scope.RawBytes.AsSpan())).ToArray();
        Assert.Contains(scopes, scope => scope.Contains("Old scope", StringComparison.Ordinal));
        Assert.Contains(scopes, scope => scope.Contains("New scope", StringComparison.Ordinal));
    }

    [Fact]
    public void ExplicitMigrationCapturesRegisteredHistoryWithoutChangingReceipts()
    {
        var f = new DecomposeFixture();
        var before = f.Current.Entries.Where(file => file.Path.EndsWith(".yaml", StringComparison.Ordinal)).ToArray();
        var migrated = AtomContextMigrationCommand.Run("fixture", f.Gateway, ["--source", "probe", "--write"], f.Apply);
        Assert.True(migrated.Success, migrated.Output + migrated.Error);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != "docs/probe.md"));
        Assert.True(AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]).Success);
        foreach (var file in before) Assert.Equal(file.Bytes, f.Current.Entries.Single(entry => entry.Path == file.Path).Bytes);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("wrong-version")]
    [InlineData("ambiguous")]
    public void MissingOrAmbiguousOccurrenceReferencesFailWithoutProseFallback(string fault)
    {
        var f = Create();
        var id = Id(f.Atomized.Claims[1]);
        var neighbor = Id(f.Atomized.Claims[0]);
        var path = DigestionContextPointerIndex.RelativePath("source", neighbor);
        var files = f.RawSnapshot(false).Entries.Where(file => file.Path != path).ToList();
        if (fault != "missing")
        {
            var version = f.ContextIndex! with { Entries = [f.ContextIndex!.Entries.Single(entry => entry.AtomId == neighbor)] };
            var bytes = DigestionContextPointerStore.WriteVersions([version]);
            if (fault == "wrong-version") bytes = DigestionContextPointerStore.WriteVersions([
                version with { SourceSha256 = "sha256:" + new string('f', 64) }]);
            else
            {
                var json = System.Text.Json.Nodes.JsonNode.Parse(bytes.AsSpan())!;
                var occurrences = json[0]!["Entries"]![0]!["Occurrences"]!.AsArray();
                occurrences.Add(occurrences[0]!.DeepClone());
                bytes = [.. Encoding.UTF8.GetBytes(json.ToJsonString() + "\n")];
            }
            files.Add(new RawRepositoryEntry(path, bytes));
        }
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), RawRepositorySnapshot.Create(files), null);
        var result = AtomContextCommand.Run(gateway, ["--atom-id", id]);
        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Contains("OCCURRENCE_MISSING", result.Error, StringComparison.Ordinal);
        Assert.Contains(fault == "missing" ? "CONTEXT_UNAVAILABLE" : fault == "wrong-version" ? "CONTEXT_VERSION_MISSING" : "duplicate context occurrence", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(paths => paths), pathspec => pathspec.Contains(SourcePath, StringComparison.Ordinal));
    }
}
