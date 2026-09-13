using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ExplicitDecompositionTests
{
    private const string First = "**Theorem 1.1** Assume a positive variance.\n\n";
    private const string Second = "The mean is μ and the mass is k.\n\n";
    private const string Third = "The strict bound includes equality at the threshold.\n";

    [Fact]
    public void ExplicitCutsWriteExactChildrenAndReplayWithoutCuts()
    {
        var f = new DecomposeFixture(First + Second + Third);
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway,
            Cuts(f, First, Second), f.Apply);
        Assert.True(result.Success, result.Error);
        var parent = f.Document.RequireDigestionEntries().Single(e => e.AtomId == f.Parent.AtomId);
        var expected = new[] { First, Second, Third };
        Assert.Equal(expected.Select(text => DecomposeFixture.Entry(text).AtomId), parent.Receipts.ChainAtoms);
        for (var index = 0; index < expected.Length; index++)
        {
            var bytes = f.Current.Entries.Single(e => e.Path == DigestionCasStore.RootPath
                + parent.Receipts.ChainAtoms[index]).Bytes;
            Assert.Equal(Encoding.UTF8.GetBytes(expected[index]), bytes.ToArray());
        }
        Assert.Equal(f.Baseline.Entries.Single(e => e.Path == "docs/probe.md"),
            f.Current.Entries.Single(e => e.Path == "docs/probe.md"));
        var before = f.Current;
        var repeated = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(repeated.Success, repeated.Error);
        Assert.Same(before, f.Current);
        Assert.Equal(1, f.Writes);
    }

    [Fact]
    public void ExplicitDryRunUsesProductionDispatchWithoutWriting()
    {
        var f = new DecomposeFixture(First + Second + Third);
        var environment = new ProductionCliEnvironment("synthetic", f.Gateway,
            new FakeLeanReportSource(null), new FakeScribeEmissionVerifier(null));
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["decompose-atom", .. Cuts(f, First, Second), "--dry-run"],
            environment, console);
        Assert.Equal(0, exit);
        Assert.Contains("children=3", console.Output, StringComparison.Ordinal);
        Assert.Contains("dry_run=true", console.Output, StringComparison.Ordinal);
        Assert.Same(f.Baseline, f.Current);
    }

    [Theory]
    [InlineData("0")]
    [InlineData("-1")]
    [InlineData("2147483648")]
    [InlineData("abc")]
    [InlineData("99999")]
    [InlineData("duplicate")]
    [InlineData("descending")]
    [InlineData("utf8")]
    [InlineData("end")]
    public void InvalidExplicitCutsFailBeforeWriting(string defect)
    {
        var f = new DecomposeFixture(First + Second + Third);
        var cut = Encoding.UTF8.GetByteCount(First).ToString(System.Globalization.CultureInfo.InvariantCulture);
        string[] values = defect switch
        {
            "duplicate" => [cut, cut],
            "descending" => [cut, "1"],
            "utf8" => [(Encoding.UTF8.GetByteCount(First + "The mean is ") + 1).ToString(System.Globalization.CultureInfo.InvariantCulture)],
            "end" => [Encoding.UTF8.GetByteCount(First + Second + Third).ToString(System.Globalization.CultureInfo.InvariantCulture)],
            _ => [defect],
        };
        var before = f.Current;
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway,
            [.. f.Args(), .. values.SelectMany(value => new[] { "--split-at", value })], f.Apply);
        Assert.False(result.Success);
        Assert.Contains("SPLIT_AT_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Same(before, f.Current);
        Assert.Equal(0, f.Writes);
    }

    [Fact]
    public void ExplicitCutCannotReplaceCanonicalMarkedPlan()
    {
        var f = new DecomposeFixture();
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway,
            [.. f.Args(), "--split-at", "10"], f.Apply);
        Assert.False(result.Success);
        Assert.Contains("PLAN_CONFLICT", result.Error, StringComparison.Ordinal);
        Assert.Equal(0, f.Writes);
    }

    [Fact]
    public void ExplicitCutCannotReplacePersistedUnmarkedChain()
    {
        var f = Persist(First, Second, Third);
        var before = f.Current;
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, Cuts(f, First), f.Apply);
        Assert.False(result.Success);
        Assert.Contains("CHAIN_CONFLICT", result.Error, StringComparison.Ordinal);
        Assert.Same(before, f.Current);
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    [InlineData("\r")]
    public void AlignerValidatesPersistedUnmarkedChain(string newline)
    {
        var f = Persist(First.Replace("\n", newline, StringComparison.Ordinal),
            Second.Replace("\n", newline, StringComparison.Ordinal),
            Third.Replace("\n", newline, StringComparison.Ordinal));
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot,
            BackfillInventoryLoader.Load(DecomposeFixture.Decode(f.Baseline)), DigestionAlignmentMode.Ingest);
        Assert.Empty(alignment.Findings);
        Assert.Contains(f.Parent.AtomId, alignment.VerifiedClausePlanParents);
        Assert.All(f.Document.RequireDigestionEntries(), entry =>
            Assert.Equal(DigestionReceiptAlignment.Seen, alignment.AlignmentFor(entry.AtomId)));
    }

    [Fact]
    public void ContextUsesPersistedUnmarkedChildrenInSourceOrder()
    {
        var f = Persist(First, Second, Third);
        var middle = DecomposeFixture.Entry(Second).AtomId;
        var context = DigestionAtomContextProjection.Resolve(f.Snapshot, f.Document, middle);
        Assert.Equal(DecomposeFixture.Entry(First).AtomId, context.Previous!.Value.AtomId);
        Assert.Equal(middle, context.Current.AtomId);
        Assert.Equal(DecomposeFixture.Entry(Third).AtomId, context.Next!.Value.AtomId);
        Assert.Equal(2, context.Index);
        Assert.Equal(3, context.Count);
    }

    [Fact]
    public void UnmarkedChildrenInheritTheParentContentKind()
    {
        var f = Persist(First, Second, Third);
        var kinds = DigestionContentKindResolver.Resolve(f.Snapshot, f.Document);
        foreach (var text in new[] { First, Second, Third })
            Assert.Equal("theorem", kinds[DecomposeFixture.Entry(text).AtomId]);
    }

    [Fact]
    public void NestedExplicitChainSurvivesIngestAndContextQueries()
    {
        var f = new DecomposeFixture(First + Second + Third);
        var outer = DecomposeAtomCommand.Run("synthetic", f.Gateway, Cuts(f, First), f.Apply);
        Assert.True(outer.Success, outer.Error);
        var nestedId = DecomposeFixture.Entry(Second + Third).AtomId;
        var inner = DecomposeAtomCommand.Run("synthetic", f.Gateway,
            [.. f.Args(nestedId), "--split-at", Encoding.UTF8.GetByteCount(Second).ToString(System.Globalization.CultureInfo.InvariantCulture)], f.Apply);
        Assert.True(inner.Success, inner.Error);
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot,
            f.Document, DigestionAlignmentMode.Ingest);
        Assert.Empty(alignment.Findings);
        Assert.Contains(f.Parent.AtomId, alignment.VerifiedClausePlanParents);
        Assert.Contains(nestedId, alignment.VerifiedClausePlanParents);
        var thirdId = DecomposeFixture.Entry(Third).AtomId;
        var context = DigestionAtomContextProjection.Resolve(f.Snapshot, f.Document, thirdId);
        Assert.Equal(DecomposeFixture.Entry(Second).AtomId, context.Previous!.Value.AtomId);
        Assert.Equal(3, context.Count);
        Assert.Null(context.Next);
        Assert.Equal("theorem", DigestionContentKindResolver.Resolve(f.Snapshot, f.Document)[thirdId]);
        var ingest = DigestionIngestor.Plan(f.Document, f.Snapshot, f.Document);
        Assert.Equal(0, ingest.ResidualOpenAdded);
        Assert.Empty(ingest.CasObjects);
        Assert.Equal(DirectoryLedgerTestSupport.Image(f.Document), DirectoryLedgerTestSupport.Image(ingest.Document));
    }

    [Fact]
    public void ChildCasOnlyDeltaRevalidatesTheUnmarkedParent()
    {
        var f = Persist(First, Second, Third);
        var baseline = f.Snapshot;
        var ledger = f.Document;
        var childPath = DigestionCasStore.RootPath + DecomposeFixture.Entry(Second).AtomId;
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(e => e.Path != childPath)
            .Append(RawRepositoryEntry.FromText(childPath, "different bytes\n")));
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot,
            ledger, DigestionAlignmentMode.Admission, baselineSnapshot: baseline,
            changes: RawChangeSet.Create([childPath]));
        Assert.NotEmpty(alignment.Findings);
        Assert.DoesNotContain(f.Parent.AtomId, alignment.VerifiedClausePlanParents);
    }

    [Fact]
    public void InvalidUtf8ChildCasProducesAlignmentFindings()
    {
        var f = Persist(First, Second, Third);
        var baseline = f.Snapshot;
        var ledger = f.Document;
        var childPath = DigestionCasStore.RootPath + DecomposeFixture.Entry(Second).AtomId;
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(e => e.Path != childPath)
            .Append(new RawRepositoryEntry(childPath, [0xff])));
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot,
            ledger, DigestionAlignmentMode.Admission, baselineSnapshot: baseline,
            changes: RawChangeSet.Create([childPath]));
        Assert.NotEmpty(alignment.Findings);
        Assert.DoesNotContain(f.Parent.AtomId, alignment.VerifiedClausePlanParents);
    }

    [Fact]
    public void CanonicalSharedChildKeepsItsUnresolvedContentKind()
    {
        var f = SharedKinds(marked: true);
        var sharedId = DecomposeFixture.Entry("**Shared** Common.\n\n").AtomId;
        var kinds = DigestionContentKindResolver.Resolve(f.Snapshot, f.Document);
        Assert.DoesNotContain(sharedId, kinds.Keys);
    }

    [Fact]
    public void ExplicitSharedChildRejectsConflictingContentKinds()
    {
        var f = SharedKinds(marked: false);
        var error = Assert.Throws<FormatException>(() => DigestionContentKindResolver.Resolve(f.Snapshot, f.Document));
        Assert.Contains("CONTENT_KIND_CONFLICT", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SharedChildInheritsOnlyFromItsOwningSource()
    {
        var f = SharedKinds(marked: false);
        const string theorem = "## theorem 1.1\n\nAlpha.\n\n";
        const string remark = "## remark 1.2\n\nBeta.\n\n";
        const string shared = "Common.\n\n";
        var otherId = DecomposeFixture.Entry(remark + shared).AtomId;
        var prefixId = DecomposeFixture.Entry(remark).AtomId;
        var moved = f.Document.RequireDigestionEntries().Where(e => e.AtomId == otherId || e.AtomId == prefixId).ToArray();
        foreach (var entry in moved) f.Replace(entry with { SourceId = "z-other", SourcePath = "docs/other.md" });
        var source = new DigestionLedgerSource("z-other", "docs/other.md", AtomizerRegistry.GenericId, [],
            GenreRegistryProjection.Available(GenreRegistryCheck.Collected([])), []);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(e => e.Path != "docs/probe.md")
            .Concat(new RawRepositoryEntry[]
            {
                RawRepositoryEntry.FromText("docs/probe.md", theorem + shared),
                RawRepositoryEntry.FromText("docs/other.md", remark + shared),
                new("Meta/Digestion/backfill/z-other/source.toml", BackfillInventoryWriter.WriteSourceMetadata(source)),
            }));
        Assert.Equal("theorem", DigestionContentKindResolver.Resolve(f.Snapshot, f.Document)
            [DecomposeFixture.Entry(shared).AtomId]);
    }

    [Fact]
    public void ExplicitParentWithCanonicalNestedChildInheritsKinds()
    {
        const string prefix = "**Theorem 1.1** Prefix. ";
        const string list = "- alpha\n- beta\n";
        var f = new DecomposeFixture(prefix + list);
        var outer = DecomposeAtomCommand.Run("synthetic", f.Gateway, Cuts(f, prefix), f.Apply);
        Assert.True(outer.Success, outer.Error);
        var inner = DecomposeAtomCommand.Run("synthetic", f.Gateway,
            f.Args(DecomposeFixture.Entry(list).AtomId), f.Apply);
        Assert.True(inner.Success, inner.Error);
        var kinds = DigestionContentKindResolver.Resolve(f.Snapshot, f.Document);
        Assert.Equal("theorem", kinds[DecomposeFixture.Entry("- alpha\n").AtomId]);
        Assert.Equal("theorem", kinds[DecomposeFixture.Entry("- beta\n").AtomId]);
    }

    [Theory]
    [InlineData("gap")]
    [InlineData("overlap")]
    [InlineData("reversed")]
    [InlineData("missing-last")]
    [InlineData("wrong-bytes")]
    [InlineData("missing-cas")]
    [InlineData("self")]
    public void InvalidUnmarkedChainIsRejectedByAlignmentAndContext(string defect)
    {
        var f = new DecomposeFixture(First + Second + Third);
        var texts = defect switch
        {
            "gap" => new[] { First[..^1], Second, Third },
            "overlap" => [First + Second[..1], Second, Third],
            "reversed" => [Third, Second, First],
            "missing-last" => [First, Second],
            "wrong-bytes" => [First, Second.Replace("mass", "size", StringComparison.Ordinal), Third],
            _ => [First, Second, Third],
        };
        AddChain(f, texts);
        if (defect == "missing-cas")
            f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(e =>
                e.Path != DigestionCasStore.RootPath + DecomposeFixture.Entry(Second).AtomId));
        if (defect == "self")
            f.Replace(f.Parent with { Receipts = f.Parent.Receipts with { ChainAtoms = [f.Parent.AtomId] } });
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot,
            f.Document, DigestionAlignmentMode.Ingest);
        Assert.DoesNotContain(f.Parent.AtomId, alignment.VerifiedClausePlanParents);
        Assert.NotEmpty(alignment.Findings);
        Assert.Throws<DigestionAtomContextException>(() => DigestionAtomContextProjection.Resolve(
            f.Snapshot, f.Document, DecomposeFixture.Entry(First).AtomId));
    }

    private static string[] Cuts(DecomposeFixture f, params string[] prefixes)
    {
        var offset = 0;
        var arguments = f.Args().ToList();
        foreach (var prefix in prefixes)
        {
            offset += Encoding.UTF8.GetByteCount(prefix);
            arguments.Add("--split-at");
            arguments.Add(offset.ToString(System.Globalization.CultureInfo.InvariantCulture));
        }
        return [.. arguments];
    }

    private static DecomposeFixture Persist(params string[] children)
    {
        var f = new DecomposeFixture(string.Concat(children));
        AddChain(f, children);
        return f;
    }

    private static DecomposeFixture SharedKinds(bool marked)
    {
        var shared = marked ? "**Shared** Common.\n\n" : "Common.\n\n";
        const string theorem = "## theorem 1.1\n\nAlpha.\n\n";
        const string remark = "## remark 1.2\n\nBeta.\n\n";
        var f = new DecomposeFixture(theorem + shared, AtomizerRegistry.GenericId);
        var other = DecomposeFixture.Entry(remark + shared, AtomizerRegistry.GenericId);
        f.Add(other, remark + shared);
        var sharedEntry = DecomposeFixture.Entry(shared, AtomizerRegistry.GenericId);
        f.Add(sharedEntry, shared);
        foreach (var pair in new[] { (f.Parent, theorem), (other, remark) })
        {
            var prefix = DecomposeFixture.Entry(pair.Item2, AtomizerRegistry.GenericId);
            f.Add(prefix, pair.Item2);
            f.Replace(pair.Item1 with
            {
                Receipts = pair.Item1.Receipts with { ChainAtoms = [prefix.AtomId, sharedEntry.AtomId] },
            });
        }
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(e => e.Path != "docs/probe.md")
            .Append(RawRepositoryEntry.FromText("docs/probe.md", theorem + shared + remark + shared)));
        return f;
    }

    private static void AddChain(DecomposeFixture f, string[] children)
    {
        foreach (var text in children) f.Add(DecomposeFixture.Entry(text), text);
        f.Replace(f.Parent with
        {
            Receipts = f.Parent.Receipts with
            {
                ChainAtoms = [.. children.Select(text => DecomposeFixture.Entry(text).AtomId)],
            },
        });
    }
}
