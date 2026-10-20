using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.AtomContextFixture;

namespace StrataLint.Tests;

public sealed partial class SourceDispatchCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DefaultDispatchIsDistinctFromRawSearchAndLoadsOnlySelectedMetadata(bool excluded)
    {
        var id = new string('a', 64);
        var raw = RawRepositorySnapshot.Create([
            Metadata("alpha", excluded),
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/alpha/residual-open/{id}.yaml", "invalid: ["),
            RawRepositoryEntry.FromText(MetadataPath("unrelated"), "invalid = ["),
            RawRepositoryEntry.FromText(DigestionCasStore.RootPath + id, "stored needle"),
        ]);
        var gateway = Gateway(raw);
        var selected = SearchAtomsCommand.Run(gateway,
            ["--source", "alpha", "--selection", "default-dispatch", "--text", "needle"]);
        Assert.True(selected.Success, selected.Error);
        Assert.Equal(!excluded, selected.Output.Contains(id, StringComparison.Ordinal));
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(scope => scope),
            path => path.EndsWith(".yaml", StringComparison.Ordinal) || path.Contains("unrelated", StringComparison.Ordinal));
        var inspected = SearchAtomsCommand.Run(Gateway(raw), ["--source", "alpha", "--text", "needle"]);
        Assert.True(inspected.Success, inspected.Error);
        Assert.Contains(id, inspected.Output, StringComparison.Ordinal);
        var cached = SearchAtomsCommand.Run(Gateway(raw), ["--selection", "default-dispatch", "--atom-id", id]);
        Assert.True(cached.Success, cached.Error);
        Assert.Equal(!excluded, cached.Output.Contains(id, StringComparison.Ordinal));
        Assert.False(SearchAtomsCommand.Run(Gateway(raw), ["--atom-id", id]).Success);
    }

    [Theory]
    [InlineData(false, "bytes")]
    [InlineData(false, "dispatch")]
    [InlineData(false, "missing")]
    [InlineData(false, "invalid")]
    [InlineData(true, "bytes")]
    [InlineData(true, "dispatch")]
    [InlineData(true, "missing")]
    [InlineData(true, "invalid")]
    public void SelectionRejectsMetadataChangesBetweenResolutionAndRead(bool pathSelector, string mutation)
    {
        using var temporary = new TemporaryDirectory();
        var raw = RawRepositorySnapshot.Create([Metadata("alpha"), Metadata("beta")]);
        Write(temporary.Path, raw);
        var before = Image(temporary.Path);
        var mutated = RawRepositorySnapshot.Create(raw.Entries.Where(entry => mutation != "missing" || entry.Path != MetadataPath("alpha"))
            .Select(entry => entry.Path != MetadataPath("alpha") ? entry : mutation switch
            {
                "bytes" => RawRepositoryEntry.FromText(entry.Path, Encoding.UTF8.GetString(entry.Bytes.AsSpan()) + "# concurrent edit\n"),
                "dispatch" => Metadata("alpha", excluded: true),
                "invalid" => RawRepositoryEntry.FromText(entry.Path, "invalid = ["),
                _ => entry,
            }));
        string[] selectors = pathSelector ? ["--source", "docs/alpha.md"] : ["--source", "alpha", "--source", "beta"];
        FakeRepositoryGateway ChangingGateway()
        {
            var reads = 0;
            return new(RawChangeSet.Create([]), null, null, currentReader: () => ++reads <= 2 ? raw : mutated);
        }
        var commits = 0;
        var result = SourceDispatchCommand.Run(temporary.Path, ChangingGateway(),
            [.. selectors, "--default", "excluded"], commit: (_, _) => commits++);
        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal(0, commits);
        Assert.Equal(before, Image(temporary.Path));
        var search = SearchAtomsCommand.Run(ChangingGateway(), [.. selectors, "--selection", "default-dispatch"]);
        Assert.False(search.Success);
        Assert.Empty(search.Output);
    }

    [Fact]
    public void CachedSelectionWithNoCurrentAtomsDoesNotReadAnyMetadata()
    {
        var gateway = Gateway(RawRepositorySnapshot.Create([
            RawRepositoryEntry.FromText(MetadataPath("unrelated"), "invalid = ["),
        ]));
        var selected = SearchAtomsCommand.Run(gateway,
            ["--selection", "default-dispatch", "--atom-id", new string('a', 64)]);
        Assert.True(selected.Success, selected.Error);
        Assert.Empty(selected.Output);
        Assert.Empty(gateway.ScopedCurrentReads);
        Assert.Equal(0, gateway.WholeTreeReadCount);
    }

    [Fact]
    public void DefaultDispatchRejectsMissingMetadataAndAmbiguousCachedAtomOwners()
    {
        var id = new string('a', 64);
        var raw = RawRepositorySnapshot.Create([
            Metadata("alpha"), Metadata("beta", true),
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/alpha/residual-open/{id}.yaml", "invalid: ["),
            RawRepositoryEntry.FromText($"Meta/Digestion/backfill/beta/residual-open/{id}.yaml", "invalid: ["),
        ]);
        Assert.False(SearchAtomsCommand.Run(Gateway(raw), ["--source", "missing", "--selection", "default-dispatch"]).Success);
        Assert.False(SearchAtomsCommand.Run(Gateway(raw), ["--selection", "default-dispatch", "--atom-id", id]).Success);
    }

    [Fact]
    public void ExplicitInspectionAndForeignChildReuseRemainAvailable()
    {
        var fixture = Create(ListClaims, expand: true);
        var root = fixture.Ledger.RequireDigestionSources().Single();
        var parent = root.Entries.First(entry => !entry.Receipts.ChainAtoms.IsEmpty);
        var foreignId = parent.Receipts.ChainAtoms[0];
        var foreign = root.Entries.Single(entry => entry.AtomId == foreignId) with
        {
            SourceId = "foreign", SourcePath = "docs/foreign.md",
        };
        fixture = fixture with { Ledger = BackfillInventoryDocument.Create([
            root with { Entries = root.Entries.Where(entry => entry.AtomId != foreignId).ToImmutableArray() },
            root with { SourceId = "foreign", SourcePath = "docs/foreign.md", Entries = [foreign],
                DefaultDispatch = DigestionDefaultDispatch.Excluded },
        ], []) };
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Concat(
            fixture.Atomized.Claims.Concat(fixture.Atomized.ClausePlans.SelectMany(plan => plan.Children))
                .DistinctBy(Id).Select(atom => new RawRepositoryEntry(DigestionCasStore.RootPath + Id(atom), atom.RawBytes))));
        // Reading chains uses stored entries; the source dispatch choice never gates references.
        var loaded = DigestionQuerySelection.ReadAtom(Gateway(raw), parent.AtomId);
        var chains = DigestionQuerySelection.ReadChains(Gateway(raw), loaded);
        Assert.Contains(chains.Document.RequireDigestionEntries(), entry => entry.AtomId == foreignId);
        var inspected = ShowAtomCommand.Run(Gateway(raw), ["--atom-id", foreignId]);
        Assert.True(inspected.Success, inspected.Error);
        var selected = SearchAtomsCommand.Run(Gateway(raw), ["--source", "source", "--selection", "default-dispatch"]);
        Assert.True(selected.Success, selected.Error);
        Assert.Contains(parent.AtomId, selected.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void ExplicitIngestKeepsExcludedChoiceAndAllOldAtomCasBytes()
    {
        var fixture = Create();
        var root = fixture.Ledger.RequireDigestionSources().Single() with { DefaultDispatch = DigestionDefaultDispatch.Excluded };
        fixture = fixture with { Ledger = fixture.Ledger.WithDigestionSources([root]) };
        var raw = RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Select(entry => entry.Path == SourcePath
            ? RawRepositoryEntry.FromText(SourcePath, Encoding.UTF8.GetString(fixture.SourceBytes) + "\n## Extra\n\nAdditional fact.\n") : entry)
            .Concat(fixture.Atomized.Claims.Select(atom => new RawRepositoryEntry(DigestionCasStore.RootPath + Id(atom), atom.RawBytes))));
        using var temporary = new TemporaryDirectory();
        Write(temporary.Path, raw);
        var result = IngestCommand.RunReportFree(temporary.Path, Gateway(raw), ["--source", "source"]);
        Assert.True(result.Success, result.Error);
        var after = Read(temporary.Path);
        foreach (var original in raw.Entries.Where(file => !DigestionContextPointerStore.IsCanonicalPath(file.Path)))
            Assert.Equal(original.Bytes.ToArray(), after.Entries.Single(entry => entry.Path == original.Path).Bytes.ToArray());
        Assert.Equal(2, DigestionContextPointerStore.Load(DigestionQuerySelection.Load(after).Snapshot, "source",
            Id(fixture.Atomized.Claims[1])).Length);
        Assert.Contains("default_dispatch = \"excluded\"", File.ReadAllText(Path.Combine(temporary.Path, MetadataPath("source"))), StringComparison.Ordinal);
        Assert.Equal(DigestionDefaultDispatch.Excluded,
            DigestionQuerySelection.Load(after).Document.RequireDigestionSources().Single().DefaultDispatch);
    }

    [Fact]
    public void SourceMetadataReconstructionRetainsChoiceAndAuthorityIdentity()
    {
        var fixture = Create();
        var source = fixture.Ledger.RequireDigestionSources().Single();
        var excluded = source with { DefaultDispatch = DigestionDefaultDispatch.Excluded };
        var entry = source.Entries[0];
        var previousIdentity = BackfillInventoryWriter.WriteSourceMetadata(source with { AcknowledgedStale = [] })
            .Concat(BackfillInventoryWriter.WriteEntry(entry));
        Assert.Equal(previousIdentity, BackfillInventoryWriter.WriteStatusAuthorityIdentity(excluded, entry));
        Assert.Equal(BackfillInventoryWriter.WriteStatusAuthorityIdentity(source, entry).ToArray(),
            BackfillInventoryWriter.WriteStatusAuthorityIdentity(excluded, entry).ToArray());
        fixture = fixture with { Ledger = fixture.Ledger.WithDigestionSources([excluded]) };
        var replacement = fixture.Ledger.WithDigestionSources([source with { AcknowledgedStale = ["stale"] }]);
        var raw = IngestCommand.ReplaceLedger(fixture.RawSnapshot(), fixture.Ledger, replacement);
        Assert.Equal(DigestionDefaultDispatch.Excluded, DigestionQuerySelection.Load(raw).Document.RequireDigestionSources().Single().DefaultDispatch);
    }
}
