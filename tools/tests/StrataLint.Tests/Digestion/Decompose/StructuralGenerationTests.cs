using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class StructuralGenerationTests
{
    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void NewIngestionOwnsNestedNegatedListAndCompleteTableProof(string newline)
    {
        var first = ("## 命题 1.1\n\n这些条件不需要：\n\n- 选择公理；\n  - **命题 99.1**。依赖子项；\n- 度量。\n\n"
            + "### 证明\n\n设 χ=z+xy。\n\n| 状态 | χ |\n|---|---:|\n| 😀 | 1 |\n\n"
            + "**证明补充**。因此成立。\n\n").Replace("\n", newline, StringComparison.Ordinal);
        var second = "## 引理 1.2\n\n下一条独立结论。\n".Replace("\n", newline, StringComparison.Ordinal);
        var f = new DecomposeFixture(first + second, AtomizerRegistry.GenericId);
        var empty = f.Document.WithDigestionSources([f.Document.RequireDigestionSources().Single() with { Entries = [] }]);
        var plan = ReportFreeDigestionIngestor.Plan(empty, f.Snapshot);
        Assert.Equal(2, plan.ResidualOpenAdded);
        Assert.Equal(new[] { first, second }.Order(), plan.CasObjects.Select(item => Encoding.UTF8.GetString(item.Bytes.AsSpan())).Order());
        Assert.All(plan.Document.RequireDigestionEntries(), entry => Assert.Empty(entry.Receipts.ChainAtoms));
        var atomized = GenericAtomizer.Atomize(Encoding.UTF8.GetBytes(first + second));
        Assert.Equal(Encoding.UTF8.GetBytes(first + second), atomized.Reassemble().ToArray());
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void CanonicalDryRunUsesInternalSectionsAndNeverCodeMathOrFrontMatterMarkers(string newline)
    {
        var prefix = "# Volume\n\n**作者：** Auric\n**机构：** Institute\n\n";
        var content = string.Concat(Enumerable.Range(1, 24).Select(index =>
            $"## theorem {index}.1\n\nClaim {index} α 😀.\n\n### Proof\n\n"
            + "```text\n**Fake** assertion\n## theorem 999.1\n```\n\n"
            + "$$\n**Math**\n$$\n\n"
            + "\\[\n**Legacy math**\n\\]\n\n"));
        var text = (prefix + content).Replace("\n", newline, StringComparison.Ordinal);
        var f = new DecomposeFixture(text, AtomizerRegistry.GenericId);
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(dryRun: true), f.Apply);
        Assert.True(result.Success, result.Error);
        Assert.Equal(25, result.Output.Split('\n').Count(line => line.StartsWith("DECOMPOSE_SEGMENT type=claim", StringComparison.Ordinal)));
        var plan = DigestionDecomposition.Plan(f.Parent, DecomposeFixture.Atom(text).RawBytes,
            GenericAtomizer.Atomize, f.Snapshot);
        Assert.Equal(Encoding.UTF8.GetBytes(text), plan.Segments.SelectMany(segment => segment.Atom.RawBytes).ToArray());
        Assert.All(plan.Children.Skip(1), child =>
        {
            var bytes = Encoding.UTF8.GetString(child.RawBytes.AsSpan());
            Assert.StartsWith("## theorem", bytes, StringComparison.Ordinal);
            Assert.Contains("### Proof", bytes, StringComparison.Ordinal);
            Assert.Contains("**Legacy math**", bytes, StringComparison.Ordinal);
        });
        Assert.Null(DigestionDecomposition.IntegrityFailure(plan));
        Assert.Same(f.Baseline, f.Current);
        Assert.Equal(0, f.Writes);
        var conflict = DecomposeAtomCommand.Run("synthetic", f.Gateway, [.. f.Args(), "--split-at", "10"], f.Apply);
        Assert.False(conflict.Success);
        Assert.Contains("PLAN_CONFLICT", conflict.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void StructuralGapsSurviveMaterializationReplayContextAlignmentAndClosure(string newline)
    {
        var text = ("# Bundle 😀\n\n## theorem 1.1\n\nFirst assertion α.\n\n"
            + "# Interlude\n\n## theorem 1.2\n\nSecond assertion β.\n\n# End\n")
            .Replace("\n", newline, StringComparison.Ordinal);
        var f = new DecomposeFixture(text, AtomizerRegistry.GenericId);
        var plan = DigestionDecomposition.Plan(f.Parent, DecomposeFixture.Atom(text).RawBytes,
            GenericAtomizer.Atomize, f.Snapshot);
        Assert.Equal(2, plan.Children.Length);
        Assert.Equal(3, plan.Segments.Count(segment => segment.Kind == DigestionSegmentKind.Structural));
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        Assert.Equal(1, f.Writes);
        Assert.Equal(2, f.CasWrites.Length);
        Assert.Equal(3, f.LedgerWrites.Length);
        var parent = f.Document.RequireDigestionEntries().Single(entry => entry.AtomId == f.Parent.AtomId);
        var ids = plan.Children.Select(child => child.Fingerprints.RawSha256[7..]).ToArray();
        Assert.Equal(ids, parent.Receipts.ChainAtoms);
        var before = f.Current;
        foreach (var dryRun in new[] { true, false, false })
        {
            var repeat = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(dryRun: dryRun), f.Apply);
            Assert.True(repeat.Success, repeat.Error);
            Assert.Contains("cas_objects=0 ledger_updates=0", repeat.Output, StringComparison.Ordinal);
            Assert.Same(before, f.Current);
            Assert.Equal(1, f.Writes);
        }
        // Replay uses stored identities and exact parent gaps, even if fresh grammar changes.
        var replay = DigestionDecomposition.Plan(parent, DecomposeFixture.Atom(text).RawBytes,
            (_) => throw new InvalidOperationException("fresh grammar must not run"), f.Snapshot);
        Assert.Equal(plan.Segments.Select(segment => (segment.Kind, segment.Atom.StartByte, segment.Atom.EndByte)),
            replay.Segments.Select(segment => (segment.Kind, segment.Atom.StartByte, segment.Atom.EndByte)));
        Assert.Equal(Encoding.UTF8.GetBytes(text), replay.Segments.SelectMany(segment => segment.Atom.RawBytes).ToArray());
        var context = AtomContextCommand.Run(f.Gateway, ["--atom-id", ids[0]]);
        Assert.True(context.Success, context.Error);
        Assert.Contains("BEGIN_CURRENT_TEXT\n" + Encoding.UTF8.GetString(plan.Children[0].RawBytes.AsSpan())
            + "END_CURRENT_TEXT", context.Output, StringComparison.Ordinal);
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot, DigestionAlignmentMode.Ingest);
        Assert.Empty(alignment.Findings);
        Assert.Contains(parent.AtomId, alignment.VerifiedClausePlanParents);
        var entries = f.Document.RequireDigestionEntries().ToDictionary(entry => entry.AtomId, StringComparer.Ordinal);
        Assert.Equal(ids.Append(parent.AtomId).Order(),
            DigestionDecomposition.ValidatedClosure([parent.AtomId], entries, f.Snapshot).Order());
        foreach (var prior in f.Baseline.Entries.Where(entry => entry.Path != DecomposeFixture.PathFor(f.Parent)))
            Assert.Equal(prior.Bytes.ToArray(), f.Current.Entries.Single(entry => entry.Path == prior.Path).Bytes.ToArray());
        Assert.Same(before, f.Current);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void StructuralReplayCannotHideMissingOrTruncatedClaimsAsGaps(bool truncate)
    {
        const string text = "# Bundle\n\n## theorem 1.1\n\nFirst α.\n\n"
            + "## theorem 1.2\n\nSecond β.\n\n## theorem 1.3\n\nThird γ.\n";
        var f = new DecomposeFixture(text, AtomizerRegistry.GenericId);
        Assert.True(DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply).Success);
        var parent = f.Document.RequireDigestionEntries().Single(entry => entry.AtomId == f.Parent.AtomId);
        var chain = parent.Receipts.ChainAtoms;
        if (truncate)
        {
            var path = DigestionCasStore.RootPath + chain[1];
            var bytes = f.Current.Entries.Single(entry => entry.Path == path).Bytes;
            var raw = Encoding.UTF8.GetString(bytes.AsSpan())[..^1];
            var child = DecomposeFixture.Entry(raw, AtomizerRegistry.GenericId);
            f.Add(child, raw);
            chain = chain.SetItem(1, child.AtomId);
        }
        else chain = chain.RemoveAt(1);
        f.Replace(parent with { Receipts = parent.Receipts with { ChainAtoms = chain } });
        var before = f.Current;
        var writes = f.Writes;
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.False(result.Success);
        Assert.Contains("clause plan", result.Error, StringComparison.Ordinal);
        Assert.Same(before, f.Current);
        Assert.Equal(writes, f.Writes);
        Assert.False(AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]).Success);
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot, DigestionAlignmentMode.Ingest);
        Assert.NotEmpty(alignment.Findings);
        Assert.DoesNotContain(parent.AtomId, alignment.VerifiedClausePlanParents);
    }

    [Fact]
    public void DependentListsAndApparentMarkersHaveNoCanonicalChildTasks()
    {
        const string text = "## 定理 41.1\n\n该等价不需要：\n\n- 商对象；\n- 满射；\n  - 截面；\n\n"
            + "```text\n**Fake** claim\n```\n\n$$\n**Not a lead**\n$$\n\n";
        var f = new DecomposeFixture(text, AtomizerRegistry.GenericId);
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(dryRun: true), f.Apply);
        Assert.False(result.Success);
        Assert.Contains("NO_CLAUSE_PLAN", result.Error, StringComparison.Ordinal);
        Assert.False(DigestionDecompositionPolicy.IsMultiClause(DecomposeFixture.Atom(text)));
        Assert.Equal(0, f.Writes);
    }
}
