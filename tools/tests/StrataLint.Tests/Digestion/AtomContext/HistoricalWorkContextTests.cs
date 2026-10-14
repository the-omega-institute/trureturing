using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class HistoricalWorkContextTests
{
    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void StoredNegatedListKeepsAllChildrenAndTheirGoverningContext(string newline)
    {
        string N(string value) => value.Replace("\n", newline, StringComparison.Ordinal);
        var children = new[]
        {
            N("### 推论 41.1\n\n该等价不需要：\n\n- 商对象；\n"),
            N("- 满射；\n"), N("- 截面；\n"), N("- 选择公理；\n"), N("- 线性结构；\n"), N("- 度量。\n"),
        };
        var f = Stored(children);
        foreach (var index in new[] { 1, 2 })
        {
            var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", Id(children[index])]);
            Assert.True(result.Success, result.Error);
            Assert.Contains("WORK_CONTEXT relation=governed-list transient=true", result.Output, StringComparison.Ordinal);
            Assert.Contains(N("该等价不需要：\n\n- 商对象；\n- 满射；\n- 截面；\n- 选择公理；\n- 线性结构；\n- 度量。\n"),
                result.Output, StringComparison.Ordinal);
            Assert.Contains($"PREVIOUS atom_id={Id(children[index - 1])}", result.Output, StringComparison.Ordinal);
            Assert.Contains($"NEXT atom_id={Id(children[index + 1])}", result.Output, StringComparison.Ordinal);
            Assert.Contains("BEGIN_CURRENT_TEXT\n" + children[index] + "END_CURRENT_TEXT", result.Output, StringComparison.Ordinal);
        }
        var before = f.Current;
        var repeated = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(repeated.Success, repeated.Error);
        Assert.Contains("cas_objects=0 ledger_updates=0", repeated.Output, StringComparison.Ordinal);
        Assert.Same(before, f.Current);
        Assert.Equal(children.Select(Id), f.Document.RequireDigestionEntries()
            .Single(entry => entry.AtomId == f.Parent.AtomId).Receipts.ChainAtoms);
        Assert.Equal(0, f.Writes);
    }

    [Theory]
    [InlineData("\n", false)]
    [InlineData("\r\n", false)]
    [InlineData("\n", true)]
    public void OldTableFragmentSurvivesFreshRootChangesWithDefinitionAndColumnHeader(string newline, bool repeated)
    {
        const string row = "| $F[2]$ | $1$";
        var section = ("## χ 坐标 😀\n\n定义如下：\n\n$$\nχ=z+xy\n$$\n\n它在五个状态上的值为：\n\n"
            + "| 状态 | χ |\n|---|---:|\n| $F[1]$ | $0$ |\n" + row + "|\n| $F[3]$ | $0$ |\n")
            .Replace("\n", newline, StringComparison.Ordinal);
        var f = new DecomposeFixture(row, AtomizerRegistry.GenericId);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Select(entry => entry.Path == "docs/probe.md"
            ? RawRepositoryEntry.FromText(entry.Path, repeated ? section + section : section) : entry));
        var previous = "| $F[1]$ | $0$";
        var next = "| $F[3]$ | $0$";
        f.Add(DecomposeFixture.Entry(previous, AtomizerRegistry.GenericId), previous);
        f.Add(DecomposeFixture.Entry(next, AtomizerRegistry.GenericId), next);
        var before = f.Current;
        var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId, "--source", "probe"]);
        Assert.True(result.Success, result.Error);
        Assert.Contains("WORK_CONTEXT relation=table-definition transient=true", result.Output, StringComparison.Ordinal);
        Assert.Contains($"PREVIOUS atom_id={Id(previous)}", result.Output, StringComparison.Ordinal);
        Assert.Contains($"NEXT atom_id={Id(next)}", result.Output, StringComparison.Ordinal);
        Assert.Contains("χ=z+xy", result.Output, StringComparison.Ordinal);
        Assert.Contains("| 状态 | χ |", result.Output, StringComparison.Ordinal);
        Assert.Contains("它在五个状态上的值为：", result.Output, StringComparison.Ordinal);
        Assert.Contains("BEGIN_CURRENT_TEXT\n" + row + "\nEND_CURRENT_TEXT", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("none reason=source-start", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("none reason=source-end", result.Output, StringComparison.Ordinal);
        if (repeated)
        {
            Assert.Contains("occurrences=2", result.Output, StringComparison.Ordinal);
            Assert.Contains("OCCURRENCE index=2", result.Output, StringComparison.Ordinal);
            Assert.Throws<DigestionAtomContextException>(() =>
                DigestionAtomContextProjection.Resolve(f.Snapshot, f.Document, f.Parent.AtomId));
        }
        Assert.Same(before, f.Current);
    }

    [Fact]
    public void WiderHistoricalParentRetainsSubtreeNeighborsAcrossNewSectionBoundaries()
    {
        var children = new[] { "## Alpha\n\nOne.\n\n", "## Beta\n\nTwo.\n" };
        var f = Stored(children);
        var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]);
        Assert.True(result.Success, result.Error);
        Assert.Contains("PREVIOUS none reason=source-start", result.Output, StringComparison.Ordinal);
        Assert.Contains("NEXT none reason=source-end", result.Output, StringComparison.Ordinal);
        Assert.Contains("BEGIN_CURRENT_TEXT\n" + string.Concat(children) + "END_CURRENT_TEXT", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain($"PREVIOUS atom_id={Id(children[0])}", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain($"NEXT atom_id={Id(children[1])}", result.Output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("## No longer present\n")]
    [InlineData("**Other**\n")]
    public void AbsentHistoricalBytesStayMissing(string replacement)
    {
        var f = new DecomposeFixture("- old fragment\n", AtomizerRegistry.GenericId);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Select(entry => entry.Path == "docs/probe.md"
            ? RawRepositoryEntry.FromText(entry.Path, replacement) : entry));
        var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]);
        Assert.False(result.Success);
        Assert.Contains("OCCURRENCE_MISSING", result.Error, StringComparison.Ordinal);
    }

    private static DecomposeFixture Stored(string[] children)
    {
        var f = new DecomposeFixture(string.Concat(children), AtomizerRegistry.GenericId);
        foreach (var text in children) f.Add(DecomposeFixture.Entry(text, AtomizerRegistry.GenericId), text);
        f.Replace(f.Parent with { Receipts = f.Parent.Receipts with { ChainAtoms = [.. children.Select(Id)] } });
        return f;
    }

    private static string Id(string text) => DecomposeFixture.Entry(text, AtomizerRegistry.GenericId).AtomId;
}
