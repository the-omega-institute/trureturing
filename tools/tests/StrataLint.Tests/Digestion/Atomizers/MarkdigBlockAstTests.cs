using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// The default path parses with Markdig rather than the line scanner the registered
/// dialects use. The scanner stays where it is on purpose: its block boundaries are baked
/// into content-addressed receipts that are already frozen, so replacing it under them
/// would move atom boundaries and invalidate those receipts. It is replaced only under
/// generic-v1, which has no receipts yet, so this is a choice about a new thing rather
/// than a migration of an old one.
///
/// These cases are the two halves of that claim: on everything the scanner already
/// handled, the two agree; on what it could not represent at all, only Markdig does.
/// </summary>
public sealed class MarkdigBlockAstTests
{
    private static string[] Describe(IEnumerable<MarkdownBlock> blocks) => blocks
        .Select(static block => block switch
        {
            MarkdownHeading heading => $"h{heading.Level}:{heading.Text}",
            MarkdownTableRow row => $"row:{row.FirstCellText}",
            MarkdownParagraph paragraph => $"p:{paragraph.Text}",
            _ => "?",
        })
        .ToArray();

    [Theory]
    [InlineData("# 卷首\n\n一段。\n\n## §1 甲\n\n二段。\n")]
    [InlineData("# T\n\n**定理 1.1**。证。\n\n### 深标题\n\n末。\n")]
    [InlineData("# T\n\n| 常数 | 值 |\n|---|---|\n| κ | 1/2 |\n| **C** | 3 |\n")]
    [InlineData("# T\n\n```\n**定理 9.9** 在代码块里\n```\n\n后。\n")]
    [InlineData("# T\n\n~~~lean\ntheorem x : True\n~~~\n\n后。\n")]
    [InlineData("# 只有标题\n")]
    [InlineData("没有标题的一段散文。\n")]
    public void OnEveryShapeTheLineScannerAlreadyHandledTheTwoParsersAgree(string source)
    {
        Assert.Equal(
            Describe(MarkdownBlockAst.Parse(source)),
            Describe(MarkdigBlockAst.Parse(source)));
    }

    [Theory]
    [InlineData("# 卷首\n\n一段。\n\n## §1 甲\n\n二段。\n")]
    [InlineData("# T\n\n| 常数 | 值 |\n|---|---|\n| κ | 1/2 |\n")]
    public void TheTwoParsersAgreeOnBlockOffsetsNotJustOnText(string source)
    {
        Assert.Equal(
            MarkdownBlockAst.Parse(source).Select(static block => block.Start).ToArray(),
            MarkdigBlockAst.Parse(source).Select(static block => block.Start).ToArray());
    }

    /// <summary>
    /// A list is one undivided paragraph to the line scanner, so a volume that states its
    /// claims as list items digests as a single atom. Each item is its own block here.
    /// </summary>
    [Fact]
    public void ListItemsAreSeparateBlocksRatherThanOneParagraph()
    {
        const string source = "# T\n\n- **定理 1.1**。甲。\n- **定理 1.2**。乙。\n";

        Assert.Equal(
            ["h1:T", "p:- **定理 1.1**。甲。\n- **定理 1.2**。乙。"],
            Describe(MarkdownBlockAst.Parse(source)));
        Assert.Equal(
            ["h1:T", "p:**定理 1.1**。甲。", "p:**定理 1.2**。乙。"],
            Describe(MarkdigBlockAst.Parse(source)));
    }

    [Fact]
    public void AQuotedClaimIsItsOwnBlock()
    {
        const string source = "# T\n\n> **定理 2.1**。引。\n\n后。\n";

        Assert.Equal(
            ["h1:T", "p:**定理 2.1**。引。", "p:后。"],
            Describe(MarkdigBlockAst.Parse(source)));
    }

    [Fact]
    public void ASetextHeadingIsAHeadingRatherThanAParagraph()
    {
        const string source = "标题\n===\n\n一段。\n";

        Assert.Equal(["h1:标题", "p:一段。"], Describe(MarkdigBlockAst.Parse(source)));
    }

    [Fact]
    public void AnIndentedCodeBlockDoesNotYieldClaims()
    {
        const string source = "# T\n\n    **定理 9.9** 缩进代码\n\n后。\n";

        Assert.Equal(["h1:T", "p:后。"], Describe(MarkdigBlockAst.Parse(source)));
    }

    /// <summary>
    /// Nested blocks must not both be emitted: overlapping spans would make the atomizer's
    /// slices unorderable, and byte-exact reassembly is what the whole ledger rests on.
    /// </summary>
    [Fact]
    public void EmittedBlocksNeverOverlapAndAreOrdered()
    {
        const string source =
            "# T\n\n> 引用里\n>\n> - 列表项\n>   - 更深一层\n\n| a | b |\n|---|---|\n| 1 | 2 |\n";

        var blocks = MarkdigBlockAst.Parse(source);

        var cursor = -1;
        foreach (var block in blocks)
        {
            Assert.True(block.Start > cursor, $"block at {block.Start} overlaps the previous one");
            Assert.True(block.End >= block.Start, $"block at {block.Start} has a negative extent");
            cursor = block.End;
        }
    }

    [Fact]
    public void TheDefaultAtomizerStillReassemblesByteForByteOnShapesOnlyMarkdigParses()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "标题\n===\n\n- **定理 1.1**。甲。\n- **定理 1.2**。乙。\n\n> 引。\n\n    缩进代码\n");

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            bytes,
            TheoryAtomizerRules.None);

        Assert.Equal(bytes, document.Reassemble().ToArray());
    }
}
