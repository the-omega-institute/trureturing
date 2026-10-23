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
        f.CaptureContext();
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
        f.CaptureContext();
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
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void WideHistoricalParentReadsExteriorNeighborsWithoutInteriorRecords(string newline)
    {
        string N(string text) => text.Replace("\n", newline, StringComparison.Ordinal);
        var before = N("## Before 😀\n\n前置。\n\n");
        var after = N("## After 😀\n\n后置。\n");
        var parts = Enumerable.Range(1, 40).Select(index =>
            N($"**Theorem {index}.1** 内部断言 😀 {index}.\n\n")).ToArray();
        var parent = string.Concat(parts);
        var f = new DecomposeFixture(parent, AtomizerRegistry.GenericId);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Select(entry => entry.Path == "docs/probe.md"
            ? RawRepositoryEntry.FromText(entry.Path, before + parent + after) : entry));
        foreach (var text in new[] { before, after }) f.Add(DecomposeFixture.Entry(text, AtomizerRegistry.GenericId), text);
        f.CaptureContext();
        var interior = DecomposeFixture.Entry(parts[20].TrimEnd('\r', '\n'), AtomizerRegistry.GenericId);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Append(
            RawRepositoryEntry.FromText(DecomposeFixture.PathFor(interior), "invalid: [")));
        var original = f.Current;

        var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]);

        Assert.True(result.Success, result.Error);
        Assert.Contains($"PREVIOUS atom_id={Id(before)}", result.Output, StringComparison.Ordinal);
        Assert.Contains($"NEXT atom_id={Id(after)}", result.Output, StringComparison.Ordinal);
        Assert.Contains("BEGIN_CURRENT_TEXT\n" + parent + "END_CURRENT_TEXT", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(f.Gateway.ScopedCurrentReads.SelectMany(static paths => paths),
            path => path.Contains(interior.AtomId, StringComparison.Ordinal));
        Assert.Same(original, f.Current);
    }

    [Theory]
    [InlineData("## No longer present\n")]
    [InlineData("**Other**\n")]
    public void CapturedHistoricalBytesSurviveSourceReplacement(string replacement)
    {
        var f = new DecomposeFixture("- old fragment\n", AtomizerRegistry.GenericId);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Select(entry => entry.Path == "docs/probe.md"
            ? RawRepositoryEntry.FromText(entry.Path, replacement) : entry));
        var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", f.Parent.AtomId]);
        Assert.True(result.Success, result.Error);
        Assert.Contains("- old fragment", result.Output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("\n", false)]
    [InlineData("\r\n", false)]
    [InlineData("\n", true)]
    [InlineData("\r\n", true)]
    public void HistoricalTableBoundaryNeighborsKeepStoredIdentityBytesAndLiveState(string newline, bool fullRow)
    {
        string N(string value) => value.Replace("\n", newline, StringComparison.Ordinal);
        var header = N("## χ coordinates 😀\n\nDefinition: χ=z+xy.\n\nIts values are:\n\n| State | χ |\n|---|---:|\n");
        var bareRows = new[] { "| $F[1]$ | $0$", "| $F[2]$ | $1$", "| $F[3]$ | $2$" };
        var rows = bareRows.Select(row => fullRow ? row + "|" + newline : row).ToArray();
        var next = N("## theorem 2.1\n\nExterior assertion γ.\n");
        var text = header + string.Concat(bareRows.Select(row => row + "|" + newline))
            + N("\nThe table supplies this section's coordinates.\n\n") + next;
        var f = new DecomposeFixture(header, AtomizerRegistry.GenericId);
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Select(entry => entry.Path == "docs/probe.md"
            ? RawRepositoryEntry.FromText(entry.Path, text) : entry));
        foreach (var item in rows.Append(next)) f.Add(DecomposeFixture.Entry(item, AtomizerRegistry.GenericId), item);
        foreach (var item in new[] { header, next })
        {
            var entry = f.Document.RequireDigestionEntries().Single(entry => entry.AtomId == Id(item));
            f.Replace(entry with
            {
                Coverage = [new DigestionCoverageEdge("D5/S0/Carrier/Probe.exterior", null)],
                ProjectedStatus = new(DigestionMigrationState.Partial, DigestionTruthState.Open),
            });
        }
        f.CaptureContext();
        var before = f.Current;
        foreach (var (row, label, exterior) in new[] { (rows[0], "PREVIOUS", header), (rows[^1], "NEXT", next) })
        {
            var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", Id(row)]);
            Assert.True(result.Success, result.Error);
            Assert.Contains($"{label} atom_id={Id(exterior)} state=partial-open\n", result.Output, StringComparison.Ordinal);
            var interiorLabel = label == "PREVIOUS" ? "NEXT" : "PREVIOUS";
            Assert.Contains($"{interiorLabel} atom_id={Id(rows[1])} state=residual-open\n", result.Output, StringComparison.Ordinal);
            Assert.Contains($"BEGIN_{label}_TEXT\n" + exterior + $"END_{label}_TEXT", result.Output, StringComparison.Ordinal);
            Assert.Contains("BEGIN_CURRENT_TEXT\n" + row + (fullRow ? "" : "\n") + "END_CURRENT_TEXT", result.Output, StringComparison.Ordinal);
            Assert.Contains("WORK_CONTEXT relation=table-definition transient=true", result.Output, StringComparison.Ordinal);
            Assert.Contains("Definition: χ=z+xy.", result.Output, StringComparison.Ordinal);
            Assert.Same(before, f.Current);
            Assert.Equal(0, f.Writes);
        }
    }

    private static DecomposeFixture Stored(string[] children)
    {
        var f = new DecomposeFixture(string.Concat(children), AtomizerRegistry.GenericId);
        foreach (var text in children) f.Add(DecomposeFixture.Entry(text, AtomizerRegistry.GenericId), text);
        f.Replace(f.Parent with { Receipts = f.Parent.Receipts with { ChainAtoms = [.. children.Select(Id)] } });
        f.CaptureContext();
        return f;
    }

    private static string Id(string text) => DecomposeFixture.Entry(text, AtomizerRegistry.GenericId).AtomId;
}
