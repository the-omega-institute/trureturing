using System.Collections.Immutable;
using System.Reflection;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    public static TheoryData<string> PrefixMatchedTables => new()
    {
        nameof(TheoryAtomizerRules.ObserverClaimPrefixes),
        nameof(TheoryAtomizerRules.GictClaimPrefixes),
        nameof(TheoryAtomizerRules.PzgHeadingPrefixes),
    };

    [Theory]
    [MemberData(nameof(PrefixMatchedTables))]
    public void NoPrefixMatchedEntryIsSwallowedByAShorterOne(string table)
    {
        // These tables are consumed with FirstOrDefault(text.StartsWith(token)) but are
        // ordered ordinally, not longest-first, so an entry that starts with another entry
        // can never be reached: the shorter one always matches first. Nothing in the volume
        // dialects trips this today; the assertion exists because the same shape — taking a
        // representative out of an ordered table — silently dropped PZG_BEDC's
        // remark/27.363-27.365 section atoms when 注记 was registered ahead of 评注.
        var tokens = typeof(TheoryAtomizerRules)
            .GetProperty(table, BindingFlags.NonPublic | BindingFlags.Instance)!
            .GetValue(DigestionTestSupport.Rules) is ImmutableArray<AtomizerMapping> mappings
            ? mappings.Select(static mapping => mapping.Token).ToArray()
            : throw new InvalidOperationException($"{table} is not a mapping table");

        var swallowed = tokens
            .SelectMany(shorter => tokens
                .Where(longer => longer != shorter
                    && longer.StartsWith(shorter, StringComparison.Ordinal))
                .Select(longer => $"{shorter} swallows {longer}"))
            .ToArray();

        Assert.Empty(swallowed);
        Assert.NotEmpty(tokens);
    }

    [Fact]
    public void UnknownClaimLeadsAreReportedAllAtOnceNotOneRunPerLead()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**甲体 1.1(A)**。一。\n\n**乙体 2.2(B)**。二。\n\n**丙体 3.3(C)**。三。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules));

        Assert.Equal(
            "unknown PZG numbered claim kind 甲体 at line 3; "
            + "unknown PZG numbered claim kind 乙体 at line 5; "
            + "unknown PZG numbered claim kind 丙体 at line 7",
            error.Message);
    }

    [Fact]
    public void ARepeatedUnknownLeadIsNamedOnceWithItsFirstLineAndCount()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**甲体 1.1(A)**。一。\n\n**甲体 2.2(B)**。二。\n\n**乙体 3.3(C)**。三。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules));

        Assert.Equal(
            "unknown PZG numbered claim kind 甲体 at line 3 (2 occurrences); "
            + "unknown PZG numbered claim kind 乙体 at line 7",
            error.Message);
    }

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

    [Fact]
    public void ACandidateTheoremLeadCarriesTheSameLocatorAsItsEnrolledForm()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**候签定理 7.1′(A)**。一。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(
            ["theorem/7.1′"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void TheLongerCandidateTheoremLeadDoesNotShadowThePlainTheoremLead()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 7.1(A)**。一。\n\n**候签定理 7.2(B)**。二。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Equal(
            ["theorem/7.1", "theorem/7.2"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }
}
