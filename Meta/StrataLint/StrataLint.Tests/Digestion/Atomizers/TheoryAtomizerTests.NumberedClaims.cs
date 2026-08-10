using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    [Theory]
    [InlineData("评注 27.363–27.365", "remark/27.363-27.365")]
    [InlineData("注记 1.1–1.2", "remark/1.1-1.2")]
    public void EveryRemarkGenreOpensASectionNotOnlyTheFirstOneListed(
        string heading,
        string expectedAstPath)
    {
        var bytes = Encoding.UTF8.GetBytes($"# PZG\n\n## {heading}\n\n正文。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(expectedAstPath, Assert.Single(document.Claims).AstPath);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgThreeSegmentClaimNumbersKeepTheirThirdSegmentInTheLocator()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**注记 3.6.1(A)**。一。\n\n**注记 3.6.2(B)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(
            ["remark/3.6.1", "remark/3.6.2"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgTwoSegmentClaimNumbersAreUnchangedByThreeSegmentSupport()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 7.15(A)**。一。\n\n**定理 7.15′(B)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(
            ["theorem/7.15", "theorem/7.15′"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }
}
