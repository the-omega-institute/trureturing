using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    [Fact]
    public void PzgSectionRemarkHeadingTokenIsDeclaredNotDerivedFromGenreOrder()
    {
        var rules = DigestionTestSupport.Rules;
        var firstRemarkGenre = rules.PzgGenres.First(static item => item.Value == "remark").Token;

        Assert.Equal("评注", rules.PzgMarkers["section-remark"]);
        Assert.NotEqual(rules.PzgMarkers["section-remark"], firstRemarkGenre);
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
