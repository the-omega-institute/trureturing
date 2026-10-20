using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class AtomPointerWriterTests
{
    [Fact]
    public void MigrationKeepsSavedGraphBytesWhenTheSameProseGetsNewChildChains()
    {
        const string prose = "First claim. Second claim.\n";
        var f = new DecomposeFixture(prose);
        var sourceText = "## Before\n\nBefore.\n\n" + prose + "## After\n\nAfter.\n";
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", sourceText);
        f.CaptureContext();
        var before = f.Current.Entries.Where(file => file.Path.Contains("/context/", StringComparison.Ordinal))
            .ToDictionary(file => file.Path, file => Encoding.UTF8.GetString(file.Bytes.AsSpan()).Trim()[1..^1]);
        var plan = DigestionDecomposition.Plan(f.Parent, DecomposeFixture.Atom(prose).RawBytes,
            AtomizerRegistry.Require(f.Parent.Atomizer).Atomize, f.Snapshot, [13]);
        foreach (var child in plan.Children)
        {
            var text = Encoding.UTF8.GetString(child.RawBytes.AsSpan());
            f.Add(DecomposeFixture.Entry(text), text);
        }
        f.Replace(f.Parent with { Receipts = f.Parent.Receipts with { ChainAtoms = [.. plan.Children.Select(child => child.Fingerprints.RawSha256[7..])] } });
        var migrated = AtomContextMigrationCommand.Run("fixture", f.Gateway, ["--source", "probe", "--write"], f.Apply);
        Assert.True(migrated.Success, migrated.Output + migrated.Error);
        foreach (var (path, bytes) in before)
            Assert.Contains(bytes, Encoding.UTF8.GetString(f.Current.Entries.Single(file => file.Path == path).Bytes.AsSpan()), StringComparison.Ordinal);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != "docs/probe.md"));
        foreach (var child in plan.Children)
        {
            var id = child.Fingerprints.RawSha256[7..];
            var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", id]);
            Assert.True(result.Success, result.Error);
            var context = DigestionQuerySelection.ReadContext(f.Gateway, id);
            Assert.NotEmpty(DigestionAtomContextProjection.ResolveOccurrences(context.Snapshot, context.Document, id));
        }
        var repeatedBefore = f.Current;
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", sourceText);
        var repeated = AtomContextMigrationCommand.Run("fixture", f.Gateway, ["--source", "probe", "--write"], f.Apply);
        Assert.True(repeated.Success, repeated.Output + repeated.Error);
        Assert.Contains("changed=0", repeated.Output, StringComparison.Ordinal);
        Assert.Equal(repeatedBefore.Entries.Select(file => (file.Path, Convert.ToHexString(file.Bytes.AsSpan()))),
            f.Current.Entries.Where(file => file.Path != "docs/probe.md").Select(file => (file.Path, Convert.ToHexString(file.Bytes.AsSpan()))));
        var childId = plan.Children[0].Fingerprints.RawSha256[7..];
        var childVersion = DigestionContextPointerStore.Load(f.Snapshot, "probe", childId).Single();
        Assert.NotNull(childVersion.GraphSha256);
        var neighborId = childVersion.Entries[0].Occurrences[0].PreviousAtomId!;
        var neighborPath = DigestionContextPointerIndex.RelativePath("probe", neighborId);
        var neighborVersions = DigestionContextPointerStore.Load(f.Snapshot, "probe", neighborId);
        Assert.Contains(neighborVersions, version => version.GraphSha256 is null);
        var oldOnly = DigestionContextPointerStore.WriteVersions(neighborVersions.Where(version => version.GraphSha256 is null));
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != neighborPath)
            .Append(new RawRepositoryEntry(neighborPath, oldOnly)));
        var missingGraph = AtomContextCommand.Run(f.Gateway, ["--atom-id", childId]);
        Assert.False(missingGraph.Success);
        Assert.Contains("CONTEXT_VERSION_MISSING", missingGraph.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void TargetedMigrationExcludesUnrelatedInvalidAccounts()
    {
        var f = new DecomposeFixture();
        var invalid = AddInvalidAccount(f);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => !file.Path.Contains("/context/", StringComparison.Ordinal)));
        var before = f.Current.Entries.Single(file => file.Path == DecomposeFixture.PathFor(invalid));
        var result = AtomContextMigrationCommand.Run("fixture", f.Gateway,
            ["--source", "probe", "--atom-id", f.Parent.AtomId, "--write"], f.Apply);
        Assert.True(result.Success, result.Output + result.Error);
        Assert.DoesNotContain(f.Gateway.ScopedCurrentReads.SelectMany(paths => paths),
            path => path == DigestionQuerySelection.Literal(DecomposeFixture.PathFor(invalid)));
        Assert.Equal(before.Bytes.ToArray(), f.Current.Entries.Single(file => file.Path == before.Path).Bytes.ToArray());
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != "docs/probe.md"));
        Assert.True(AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]).Success);
        var split = DecomposeAtomCommand.Run("fixture", f.Gateway, f.Args(), f.Apply);
        Assert.True(split.Success, split.Error);
        Assert.False(AtomContextCommand.Run(f.Gateway, ["--atom-id", invalid.AtomId]).Success);
        Assert.Throws<FormatException>(() => BackfillInventoryLoader.LoadForDigestion(f.Snapshot));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void TargetedMigrationStillRejectsAnInvalidTargetOrActualChain(bool chain)
    {
        var f = new DecomposeFixture();
        var invalid = AddInvalidAccount(f);
        if (chain) f.Replace(f.Parent with { Receipts = f.Parent.Receipts with { ChainAtoms = [invalid.AtomId] } });
        var result = AtomContextMigrationCommand.Run("fixture", f.Gateway,
            ["--source", "probe", "--atom-id", chain ? f.Parent.AtomId : invalid.AtomId, "--write"], f.Apply);
        Assert.False(result.Success);
        Assert.Contains("cannot be quarantined because coverage", result.Output + result.Error, StringComparison.Ordinal);
        Assert.Equal(0, f.Writes);
    }

    [Fact]
    public void TargetedMigrationPreservesSavedGraphsAndRejectsAnIncompatibleVersion()
    {
        var f = new DecomposeFixture();
        var saved = f.Current.Entries.Where(file => file.Path.Contains("/context/", StringComparison.Ordinal)).ToArray();
        var same = AtomContextMigrationCommand.Run("fixture", f.Gateway,
            ["--source", "probe", "--atom-id", f.Parent.AtomId, "--write"], f.Apply);
        Assert.True(same.Success, same.Output + same.Error);
        Assert.Contains("changed=0", same.Output, StringComparison.Ordinal);
        var first = saved[0];
        var versions = DigestionContextPointerStore.ParseVersions(first.Bytes, "probe", Path.GetFileNameWithoutExtension(first.Path));
        var incompatible = versions[0] with { SourcePath = "docs/other.md" };
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != first.Path)
            .Append(new RawRepositoryEntry(first.Path, DigestionContextPointerStore.WriteVersions([incompatible]))));
        var result = AtomContextMigrationCommand.Run("fixture", f.Gateway,
            ["--source", "probe", "--atom-id", f.Parent.AtomId, "--write"], f.Apply);
        Assert.False(result.Success);
        Assert.Contains("CONTEXT_VERSION_CONFLICT", result.Output + result.Error, StringComparison.Ordinal);
        Assert.Equal(1, f.Writes);
        Assert.Equal(DigestionContextPointerStore.WriteVersions([incompatible]).ToArray(),
            f.Current.Entries.Single(file => file.Path == first.Path).Bytes.ToArray());
    }

    private static DigestionLedgerEntry AddInvalidAccount(DecomposeFixture f)
    {
        const string body = "Unrelated historical claim.\n";
        var invalid = DecomposeFixture.Entry(body) with
        {
            Coverage = [new("D5/S1/Solenoid/RealFlowInjectivity.realFlow_injective", "sha256:" + new string('a', 64))],
            Receipts = new([], [], null, new("blocked", "supply witness", "multi-clause-guard")),
        };
        f.Add(invalid, body);
        return invalid;
    }

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
    public void IncompatibleHistoricalCutsDoNotBlockTheObservedFreshStream()
    {
        const string text = "## First\n\nFirst claim.\n\n## Second\n\nSecond claim.\n\n## Third\n\nThird claim.\n";
        var f = new DecomposeFixture(text);
        var middle = text.IndexOf("## Second", StringComparison.Ordinal);
        var third = text.IndexOf("## Third", StringComparison.Ordinal);
        var leftText = text[..third];
        var rightText = text[middle..];
        f.Add(DecomposeFixture.Entry(leftText), leftText);
        f.Add(DecomposeFixture.Entry(rightText), rightText);
        // The whole-source parent would contain both cuts; remove it so these
        // independent maximal historical spans expose the actual crossing.
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != DecomposeFixture.PathFor(f.Parent)));
        var claims = GenericAtomizer.Atomize(Encoding.UTF8.GetBytes(text)).Claims;
        foreach (var atom in claims)
        {
            var body = Encoding.UTF8.GetString(atom.RawBytes.AsSpan());
            f.Add(DecomposeFixture.Entry(body), body);
        }
        var result = AtomContextMigrationCommand.Run("fixture", f.Gateway, ["--source", "probe", "--write"], f.Apply);
        Assert.True(result.Success, result.Output + result.Error);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != "docs/probe.md"));
        foreach (var atom in claims)
        {
            var shown = AtomContextCommand.Run(f.Gateway, ["--atom-id", atom.Fingerprints.RawSha256[7..]]);
            Assert.True(shown.Success, shown.Error);
        }
    }

    [Fact]
    public void ExplicitHistoricalMigrationUsesOnlyTheNamedImmutableSource()
    {
        var f = new DecomposeFixture();
        var historical = f.Current;
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(file => file.Path != "docs/probe.md"
            && !file.Path.Contains("/context/", StringComparison.Ordinal)));
        var revision = new string('a', 40);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), null, historical,
            currentReader: () => f.Current);
        var result = AtomContextMigrationCommand.Run("fixture", gateway,
            ["--source", "probe", "--source-revision", revision, "--write"], f.Apply);
        Assert.True(result.Success, result.Output + result.Error);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(paths => paths),
            path => path == ":(literal)docs/probe.md");
        Assert.All(gateway.ScopedRevisionReads, read => Assert.Equal(revision, read.Revision));
        Assert.Single(gateway.ScopedRevisionReads);
        Assert.True(AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]).Success);
        var before = f.Current;
        var repeated = AtomContextMigrationCommand.Run("fixture", gateway,
            ["--source", "probe", "--source-revision", revision, "--write"], f.Apply);
        Assert.True(repeated.Success, repeated.Error);
        Assert.Contains("changed=0", repeated.Output, StringComparison.Ordinal);
        Assert.Equal(before.Entries.Select(file => (file.Path, Convert.ToHexString(file.Bytes.AsSpan()))),
            f.Current.Entries.Select(file => (file.Path, Convert.ToHexString(file.Bytes.AsSpan()))));
    }

    [Fact]
    public void MigrationCountsPreviouslySavedHistoryAsResolved()
    {
        var f = new DecomposeFixture();
        ParentSettlementTests.ReplaceFile(f, "docs/probe.md", "## Replacement\n\nNew claim.\n");
        var result = AtomContextMigrationCommand.Run("fixture", f.Gateway, ["--source", "probe", "--write"], f.Apply);
        Assert.True(result.Success, result.Output + result.Error);
        Assert.Contains("unresolved=0", result.Output, StringComparison.Ordinal);
        Assert.True(AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]).Success);
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
