using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScopedTableAtomizationTests
{
    private const string Body =
        "设参数 α > 0。  \n\n"
        + "| 情形 | 值 |\n| --- | --- |\n| 左 | α |\n| 右 | β |\n\n"
        + "因此两个情形均满足下面的结论。\n\n"
        + "$$\nF(α, β) > 0\n$$\n\n"
        + "### 证明\n\n先使用第一张表，再作如下比较。\n\n"
        + "| 条件 | 结果 |\n| --- | --- |\n| α < β | 严格 |\n\n"
        + "*证明续*。代入得极限为 3，故结论成立。 ∎\n \t\n";

    [Theory]
    [InlineData("## 命题 3.1\n\n", "\n")]
    [InlineData("**命题 3.1**。\n\n", "\n")]
    [InlineData("## 命题 3.1\n\n", "\r\n")]
    [InlineData("**命题 3.1**。\n\n", "\r\n")]
    public void ScopedClaimRetainsTablesAndFollowingProofByteForByte(string lead, string newline)
    {
        var prefix = "# 卷首 😀\n\n## 论证\n\n".Replace("\n", newline, StringComparison.Ordinal);
        var expected = (lead + Body).Replace("\n", newline, StringComparison.Ordinal);
        var next = "## 引理 3.2\n\n独立结论。\n".Replace("\n", newline, StringComparison.Ordinal);
        var bytes = Encoding.UTF8.GetBytes(prefix + expected + next);

        var document = Atomize(bytes);

        Assert.Equal(expected, Text(document.Claims[0]));
        Assert.Equal(next, Text(document.Claims[1]));
        Assert.Equal(2, document.Claims.Length);
        Assert.Equal(Encoding.UTF8.GetByteCount(prefix), document.Claims[0].StartByte);
        AssertPartition(bytes, document);
    }

    [Theory]
    [InlineData("## 命题 3.1\n\n", "### 引理 3.2\n\n")]
    [InlineData("**命题 3.1**。\n\n", "**引理 3.2**。\n\n")]
    [InlineData("## 命题 3.1\n\n", "**引理 3.2**。\n\n")]
    [InlineData("**命题 3.1**。\n\n", "### 引理 3.2\n\n")]
    [InlineData("## 命题 3.1\n\n", "## 无关章节\n\n")]
    [InlineData("**命题 3.1**。\n\n", "## 无关章节\n\n")]
    [InlineData("## 命题 3.1\n\n", "# 下一卷\n\n")]
    [InlineData("**命题 3.1**。\n\n", "# 下一卷\n\n")]
    public void ScopedClaimStopsBeforePeerClaimsAndScopeHeadings(string lead, string boundary)
    {
        const string unrelatedTable = "| 项 | 值 |\n| --- | --- |\n| 独立 | 7 |\n\n尾声。\n";
        var expected = lead + Body;
        var bytes = Encoding.UTF8.GetBytes("## 当前章节\n\n" + expected + boundary + unrelatedTable);

        var document = Atomize(bytes);

        Assert.Equal(expected, Text(document.Claims[0]));
        Assert.DoesNotContain("独立", Text(document.Claims[0]), StringComparison.Ordinal);
        if (boundary.Contains("引理", StringComparison.Ordinal))
        {
            Assert.Equal(boundary + unrelatedTable, Text(document.Claims[1]));
        }
        else
        {
            Assert.Single(document.Claims, atom => Text(atom) == "| 独立 | 7 ");
        }
        AssertPartition(bytes, document);
    }

    [Fact]
    public void AdjacentParagraphClaimsKeepTheirOwnMultilineBodiesAndTables()
    {
        const string first = "**命题 4.1**。首行。\n续行假设。\n\n"
            + "| 项 | 值 |\n| --- | --- |\n| 甲 | 1 |\n\n第一条结论。\n\n";
        const string second = "**引理 4.2**。次行。\n后续条件。\n\n"
            + "| 项 | 值 |\n| --- | --- |\n| 乙 | 2 |\n\n第二条证明。\n";
        var bytes = Encoding.UTF8.GetBytes(first + second);

        var document = Atomize(bytes);

        Assert.Equal(new[] { first, second }, document.Claims.Select(Text));
        AssertPartition(bytes, document);
    }

    [Fact]
    public void ScopedTableClaimStopsAtSinglePeerLeadAfterProofWithoutBlankLine()
    {
        const string first = "**命题 4.1**。设条件成立。\n\n"
            + "| 项 | 值 |\n| --- | --- |\n| 甲 | 1 |\n\n证明完毕。\n";
        const string second = "**引理 4.2**。后继命题。\n后继证明。\n";
        var bytes = Encoding.UTF8.GetBytes(first + second);

        var document = Atomize(bytes);

        Assert.Equal(new[] { first, second }, document.Claims.Select(Text));
        AssertPartition(bytes, document);
    }

    [Fact]
    public void SameParagraphClaimLeadsRemainSeparateBeforeAnEmbeddedTable()
    {
        const string first = "**命题 4.1**。第一条。\n续行。\n";
        const string second = "**引理 4.2**。第二条。\n后续假设。\n\n"
            + "| 项 | 值 |\n| --- | --- |\n| 乙 | 2 |\n\n第二条结论。\n";
        var bytes = Encoding.UTF8.GetBytes(first + second);

        var document = Atomize(bytes);

        Assert.Equal(new[] { first, second }, document.Claims.Select(Text));
        AssertPartition(bytes, document);
    }

    [Fact]
    public void ScopedTableClaimClausePlanRetainsTheCompleteParent()
    {
        var expected = "## 命题 3.1\n\n" + Body + "**证明补充。** 所有情形已经覆盖。\n";
        var bytes = Encoding.UTF8.GetBytes(expected);

        var document = Atomize(bytes);

        var parent = Assert.Single(document.Claims);
        Assert.Equal(expected, Text(parent));
        var plan = Assert.Single(document.ClausePlans);
        Assert.Equal(parent.Fingerprints, plan.Parent.Fingerprints);
        Assert.Equal(2, plan.Children.Length);
        Assert.Equal(bytes, plan.Segments.SelectMany(static segment => segment.Atom.RawBytes).ToArray());
        AssertPartition(bytes, document);
    }

    [Fact]
    public void StandaloneRowsKeepTheirBytesAndIdentitiesAroundScopedClaims()
    {
        const string table = "| 项 | 值 |\n| --- | --- |\n| 独立甲 | 1 |\n| 独立乙 | 2 |\n\n";
        var standalone = Atomize(Encoding.UTF8.GetBytes(table));
        var bytes = Encoding.UTF8.GetBytes(table + "## 命题 3.1\n\n" + Body
            + "## 目录\n\n" + table);

        var document = Atomize(bytes);

        // Markdig row spans exclude the closing pipe; it remains in the nonclaim slice.
        Assert.Equal(new[] { "| 独立甲 | 1 ", "| 独立乙 | 2 " }, standalone.Claims.Select(Text));
        foreach (var row in standalone.Claims)
        {
            var copies = document.Claims.Where(atom => Text(atom) == Text(row)).ToArray();
            Assert.Equal(2, copies.Length);
            Assert.All(copies, atom => Assert.Equal(row.Fingerprints, atom.Fingerprints));
        }
        AssertPartition(bytes, document);
    }

    private static AtomizedTheoryDocument Atomize(byte[] bytes) =>
        AtomizerRegistry.Atomize(AtomizerRegistry.GenericId, bytes, TheoryAtomizerRules.None);

    private static string Text(DigestionAtom atom) => Encoding.UTF8.GetString(atom.RawBytes.AsSpan());

    private static void AssertPartition(byte[] bytes, AtomizedTheoryDocument document)
    {
        Assert.Equal(bytes, document.Reassemble().ToArray());
        var claimSlices = document.Slices.Where(static slice => slice.IsClaim).ToArray();
        Assert.Equal(document.Claims.Length, claimSlices.Length);
        var end = 0;
        for (var index = 0; index < document.Claims.Length; index++)
        {
            var atom = document.Claims[index];
            Assert.True(atom.StartByte >= end);
            Assert.True(atom.EndByte > atom.StartByte);
            Assert.Equal(bytes[atom.StartByte..atom.EndByte], atom.RawBytes.ToArray());
            Assert.Equal(atom.RawBytes.ToArray(), claimSlices[index].RawBytes.ToArray());
            Assert.Equal(DigestionFingerprint.Compute(atom.RawBytes.AsSpan()), atom.Fingerprints);
            end = atom.EndByte;
        }
    }
}
