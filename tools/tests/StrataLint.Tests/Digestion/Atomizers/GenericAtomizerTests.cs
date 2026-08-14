using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// The default digestion path. Its contract is a rule, not a lexicon: the locator of an
/// atom is a function of the source bytes alone, no volume needs a registered vocabulary,
/// and no shape of Markdown makes it throw. These cases are that contract, one per clause.
/// </summary>
public sealed class GenericAtomizerTests
{
    private static AtomizedTheoryDocument Atomize(string markdown) =>
        AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            Encoding.UTF8.GetBytes(markdown),
            TheoryAtomizerRules.None);

    private static string[] Paths(AtomizedTheoryDocument document) =>
        document.Claims.Select(static claim => claim.AstPath).ToArray();

    [Fact]
    public void EveryHeadingBecomesASectionAtom()
    {
        var document = Atomize("# 卷首\n\n引言。\n\n## §1 主账\n\n一。\n\n## §2 位置\n\n二。\n");

        Assert.Equal(["section/卷首", "section/1-主账", "section/2-位置"], Paths(document));
    }

    [Fact]
    public void ANumberedHeadingIsAddressedByItsOwnGenreTokenWithoutAnyRegisteredVocabulary()
    {
        var document = Atomize("# 卷首\n\n## 定理 22.2(甲)\n\n证。\n\n## 未登记体 3.4\n\n证。\n");

        Assert.Equal(["section/卷首", "定理/22.2", "未登记体/3.4"], Paths(document));
    }

    [Fact]
    public void ABoldNumberedParagraphLeadIsAClaimAndABareNumberIsAnItem()
    {
        var document = Atomize("# 卷首\n\n**定理 1.1(甲)**。一。\n\n**1.2**。二。\n");

        Assert.Equal(["section/卷首", "定理/1.1", "item/1.2"], Paths(document));
    }

    /// <summary>The property that makes it a *default*: no input is a format failure.</summary>
    [Theory]
    [InlineData("")]
    [InlineData("没有标题也没有编号的一段散文。\n")]
    [InlineData("# 只有标题\n")]
    [InlineData("| a | b |\n| - | - |\n| 1 | 2 |\n")]
    [InlineData("```\n**定理 1.1** 在代码块里\n```\n")]
    [InlineData("**未登记体 9.9**。任何方言都不认得的抬头。\n")]
    public void NoMarkdownShapeIsAFormatFailure(string markdown)
    {
        var bytes = Encoding.UTF8.GetBytes(markdown);

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            bytes,
            TheoryAtomizerRules.None);

        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void TheDocumentReassemblesByteForByteSoNoSourceByteIsLost()
    {
        var markdown = "# 卷首\n\n引言。\n\n## 定理 1.1\n\n证。\n\n## §2 尾\n\n末。\n";
        var bytes = Encoding.UTF8.GetBytes(markdown);

        var document = Atomize(markdown);

        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    /// <summary>
    /// Locator stability is what keeps re-ingest from rewriting untouched receipts: an
    /// insertion elsewhere must not move an existing atom's address.
    /// </summary>
    [Fact]
    public void InsertingASectionDoesNotMoveTheLocatorsOfTheSectionsAroundIt()
    {
        var before = Atomize("# 卷首\n\n## §1 甲\n\n一。\n\n## §3 丙\n\n三。\n");
        var after = Atomize("# 卷首\n\n## §1 甲\n\n一。\n\n## §2 乙\n\n二。\n\n## §3 丙\n\n三。\n");

        Assert.Equal(["section/卷首", "section/1-甲", "section/3-丙"], Paths(before));
        Assert.Equal(
            ["section/卷首", "section/1-甲", "section/2-乙", "section/3-丙"],
            Paths(after));
    }

    [Fact]
    public void AnAtomKeepsItsFingerprintWhenAnUnrelatedSectionIsInserted()
    {
        var before = Atomize("# 卷首\n\n## §1 甲\n\n一。\n\n## §3 丙\n\n三。\n");
        var after = Atomize("# 卷首\n\n## §1 甲\n\n一。\n\n## §2 乙\n\n二。\n\n## §3 丙\n\n三。\n");

        Assert.Equal(
            before.ResolveClaim("section/3-丙").Fingerprints,
            after.ResolveClaim("section/3-丙").Fingerprints);
    }

    [Fact]
    public void RepeatedHeadingTextIsDisambiguatedByOccurrence()
    {
        var document = Atomize("# 卷首\n\n## 边界\n\n一。\n\n## 边界\n\n二。\n");

        Assert.Equal(
            ["section/卷首", "section/边界/occurrence/1", "section/边界/occurrence/2"],
            Paths(document));
    }

    [Fact]
    public void TheDefaultAtomizerIsRegisteredAndCarriesItsOwnResidualStem()
    {
        Assert.Contains(AtomizerRegistry.GenericId, AtomizerRegistry.RegisteredIds);
        Assert.Equal("generic", AtomizerRegistry.Require(AtomizerRegistry.GenericId).ResidualPrefix);
    }

    /// <summary>
    /// The locator is a function of the source bytes alone: loaded volume vocabularies are
    /// not an input, so editing another volume's dialect cannot churn this volume's ledger.
    /// </summary>
    [Fact]
    public void TheLocatorDoesNotDependOnAnyLoadedVocabulary()
    {
        var markdown = "# 卷首\n\n## 定理 1.1\n\n证。\n";
        var bytes = Encoding.UTF8.GetBytes(markdown);
        Assert.Equal(
            Paths(AtomizerRegistry.Atomize(AtomizerRegistry.GenericId, bytes, TheoryAtomizerRules.None)),
            Paths(AtomizerRegistry.Atomize(
                AtomizerRegistry.GenericId, bytes, DigestionTestSupport.Rules)));
    }
}
