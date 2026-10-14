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
        var atomized = GenericAtomizer.Atomize(Encoding.UTF8.GetBytes(first + second), TheoryAtomizerRules.None);
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
            GenericAtomizer.Atomize, f.Rules, f.Snapshot);
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
