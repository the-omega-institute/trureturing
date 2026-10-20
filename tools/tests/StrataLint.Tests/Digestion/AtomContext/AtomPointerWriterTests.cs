using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AtomPointerWriterTests
{
    [Theory]
    [InlineData("duplicate")]
    [InlineData("unknown")]
    [InlineData("missing")]
    [InlineData("unsorted")]
    public void RelationFormatRejectsAmbiguousOrNoncanonicalVersions(string fault)
    {
        var f = AtomContextFixture.Create();
        var entry = f.ContextIndex!.Entries[0];
        var index = f.ContextIndex with { Entries = [entry] };
        var bytes = DigestionContextPointerStore.WriteVersions([index]);
        var json = Encoding.UTF8.GetString(bytes.AsSpan());
        json = fault switch
        {
            "duplicate" => json.Replace("\"SchemaVersion\":1", "\"SchemaVersion\":1,\"SchemaVersion\":1", StringComparison.Ordinal),
            "unknown" => json.Replace("\"SchemaVersion\":1", "\"Unknown\":0,\"SchemaVersion\":1", StringComparison.Ordinal),
            "missing" => json.Replace("\"SchemaVersion\":1,", "", StringComparison.Ordinal),
            "unsorted" => "[" + Encoding.UTF8.GetString(DigestionContextPointerStore.Write(index with { SourceSha256 = "sha256:" + new string('f', 64) }).AsSpan()) + ","
                + Encoding.UTF8.GetString(DigestionContextPointerStore.Write(index with { SourceSha256 = "sha256:" + new string('a', 64) }).AsSpan()) + "]",
            _ => throw new ArgumentException(fault),
        };
        Assert.Throws<FormatException>(() => DigestionContextPointerStore.ParseVersions(
            [.. Encoding.UTF8.GetBytes(json)], index.SourceId, entry.AtomId));
    }

    [Fact]
    public void DecompositionAndSettlementUseSavedContextAfterSourceDeletion()
    {
        var f = new DecomposeFixture();
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != "docs/probe.md"));
        var decomposed = DecomposeAtomCommand.Run("fixture", f.Gateway, f.Args(), f.Apply);
        Assert.True(decomposed.Success, decomposed.Error);
        var parent = f.Document.RequireDigestionEntries().Single(entry => entry.AtomId == f.Parent.AtomId);
        var id = parent.Receipts.ChainAtoms[0];
        var shown = AtomContextCommand.Run(f.Gateway, ["--atom-id", id]);
        Assert.True(shown.Success, shown.Error);
        var context = DigestionAtomContextProjection.Resolve(f.Snapshot, f.Document, id);
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, f.Current);
        var request = $"atom_id = '{id}'\njustification = 'context checked'\nprevious_atom_id = '{context.Previous?.AtomId ?? "source-boundary"}'\nnext_atom_id = '{context.Next?.AtomId ?? "source-boundary"}'\n";
        var result = SettleAtomCommandTests.Run(temporary.Path, f.Current, request);
        Assert.True(result.Success, result.Error);
    }

    [Fact]
    public void RepeatedPointersFollowTheExactVersionOccurrence()
    {
        var f = AtomContextFixture.Create(AtomContextFixture.ThreeClaims + AtomContextFixture.ThreeClaims);
        var id = AtomContextFixture.Id(f.Atomized.Claims[1]);
        var loaded = DigestionQuerySelection.ReadContext(new FakeRepositoryGateway(RawChangeSet.Create([]), f.RawSnapshot(false), null), id);
        var index = DigestionContextPointerStore.Load(loaded.Snapshot, "source", id).Single();
        Assert.Equal(2, index.Entries[0].Occurrences.Length);
        var followed = index.Entries[0].Occurrences.Select(item => DigestionContextPointerStore.Follow(loaded.Snapshot, index, item, true)!.StartByte).ToArray();
        Assert.NotEqual(followed[0], followed[1]);
    }

    [Fact]
    public void MigrationReportsMissingHistoryAndIsByteIdempotent()
    {
        var f = new DecomposeFixture();
        var absent = DecomposeFixture.Entry("Old unsupported history.\n");
        f.Add(absent, "Old unsupported history.\n");
        var first = AtomContextMigrationCommand.Run("fixture", f.Gateway, ["--source", "probe", "--write"], f.Apply);
        Assert.False(first.Success);
        Assert.Contains("reason=no-supported-occurrence-in-observed-version", first.Output, StringComparison.Ordinal);
        Assert.Contains(absent.AtomId, first.Output, StringComparison.Ordinal);
        var before = f.Current.Entries.ToDictionary(file => file.Path, file => file.Bytes);
        var second = AtomContextMigrationCommand.Run("fixture", f.Gateway, ["--source", "probe", "--write"], f.Apply);
        Assert.False(second.Success);
        Assert.Contains("changed=0", second.Output, StringComparison.Ordinal);
        Assert.Equal(before.Keys.Order(), f.Current.Entries.Select(file => file.Path).Order());
        foreach (var file in f.Current.Entries) Assert.Equal(before[file.Path].ToArray(), file.Bytes.ToArray());
    }

    [Fact]
    public void MigrationSeparatesUnresolvedAtomsFromFailedSources()
    {
        var f = new DecomposeFixture();
        var absent = DecomposeFixture.Entry("Old unsupported history.\n");
        f.Add(absent, "Old unsupported history.\n");
        var source = f.Document.RequireDigestionSources().Single();
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Append(new RawRepositoryEntry(
            BackfillInventoryLoader.RootPath + "missing/source.toml", BackfillInventoryWriter.WriteSourceMetadata(
                source with { SourceId = "missing", SourcePath = "docs/missing.md" }))));
        var result = AtomContextMigrationCommand.Run("fixture", f.Gateway, ["--all"]);
        Assert.False(result.Success);
        Assert.Contains("ATOM_CONTEXT_MIGRATION_INCOMPLETE unresolved_atoms=1 failed_sources=1", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DecompositionMaintainsExteriorRanksAndRepeatedOccurrences()
    {
        const string before = "## Before\n\nBefore.\n\n";
        const string after = "## After\n\nAfter.\n";
        var text = before + DecomposeFixture.Bold + after + DecomposeFixture.Bold;
        var f = new DecomposeFixture();
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", text);
        f.CaptureContext();
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != "docs/probe.md"));
        var result = DecomposeAtomCommand.Run("fixture", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        var restored = RawRepositorySnapshot.Create(f.Current.Entries.Append(RawRepositoryEntry.FromText("docs/probe.md", text)));
        var snapshot = DecomposeFixture.Decode(restored);
        var expected = DigestionContextIndexBuilder.Build(snapshot, f.Document, "probe").Index;
        foreach (var entry in expected.Entries)
        {
            var actual = DigestionContextPointerStore.Load(f.Snapshot, "probe", entry.AtomId).Single().Entries[0];
            Assert.Equal(entry.Occurrences.Select(item => (item.StartByte, item.StreamIndex, item.StreamCount)),
                actual.Occurrences.Select(item => (item.StartByte, item.StreamIndex, item.StreamCount)));
            Assert.Equal(entry.Occurrences.SelectMany(item => item.GoverningContext.Select(scope => (scope.Relation, scope.AtomId))),
                actual.Occurrences.SelectMany(item => item.GoverningContext.Select(scope => (scope.Relation, scope.AtomId))));
        }
    }

    [Fact]
    public void NestedDecompositionAfterDeletionRetainsTheSavedVersion()
    {
        var f = new DecomposeFixture();
        var version = DigestionContextPointerStore.Load(f.Snapshot, "probe", f.Parent.AtomId).Single().SourceSha256;
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != "docs/probe.md"));
        var first = DecomposeAtomCommand.Run("fixture", f.Gateway, f.Args(), f.Apply);
        Assert.True(first.Success, first.Error);
        var child = f.Document.RequireDigestionEntries().Single(entry => entry.AtomId == f.Parent.AtomId).Receipts.ChainAtoms[0];
        var nested = DecomposeAtomCommand.Run("fixture", f.Gateway, [.. f.Args(child), "--split-at", "16"], f.Apply);
        Assert.True(nested.Success, nested.Error);
        foreach (var entry in f.Document.RequireDigestionEntries())
        {
            var context = DigestionAtomContextProjection.Resolve(f.Snapshot, f.Document, entry.AtomId);
            Assert.Equal(version, context.SourceSha256);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CompleteChainSettlementUsesStoredDescendantContextsAfterDeletion(bool nested)
    {
        var f = ParentSettlementTests.Create(nested);
        var parent = ParentSettlementTests.Target(f);
        var context = DigestionAtomContextProjection.Resolve(f.Snapshot, f.Document, parent.AtomId);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != "docs/probe.md"));
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, f.Current);
        var result = SettleAtomCommandTests.Run(temporary.Path, f.Current,
            ParentSettlementTests.Request(parent.AtomId, context.Previous?.AtomId, context.Next?.AtomId));
        Assert.True(result.Success, result.Error);
    }

    [Fact]
    public void DecomposingAReusedAtomUpdatesEverySavedSourceBinding()
    {
        const string text = "## Parent\n\n* A;\n* B.\n\n";
        const string after = "## After\n\nAfter.\n";
        var f = new DecomposeFixture(text);
        var source = f.Document.RequireDigestionSources().Single();
        var parent = f.Parent with { SourceId = "foreign", SourcePath = "docs/foreign.md" };
        f.Replace(parent);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Append(new RawRepositoryEntry(
            BackfillInventoryLoader.RootPath + "foreign/source.toml", BackfillInventoryWriter.WriteSourceMetadata(
                source with { SourceId = "foreign", SourcePath = "docs/foreign.md" })))
            .Append(RawRepositoryEntry.FromText("docs/foreign.md", text)));
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", text + after);
        var target = DecomposeFixture.Entry(after);
        f.Add(target, after);
        f.CaptureContext();
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => !file.Path.StartsWith("docs/", StringComparison.Ordinal)));
        var result = DecomposeAtomCommand.Run("fixture", f.Gateway, f.Args(parent.AtomId), f.Apply);
        Assert.True(result.Success, result.Error);
        var last = f.Document.RequireDigestionEntries().Single(entry => entry.AtomId == parent.AtomId).Receipts.ChainAtoms[^1];
        var context = AtomContextCommand.Run(f.Gateway, ["--atom-id", target.AtomId, "--source", "probe"]);
        Assert.True(context.Success, context.Error);
        Assert.Contains("PREVIOUS atom_id=" + last, context.Output, StringComparison.Ordinal);
        Assert.Single(DigestionContextPointerStore.Load(f.Snapshot, "probe", last));
    }
}
