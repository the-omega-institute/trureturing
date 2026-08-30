using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// The default digestion atomizer is a rule, not a lexicon: atom content is independent
/// of any registered vocabulary,
/// and no shape of Markdown makes it throw. These cases are that contract, one per clause.
/// </summary>
public sealed class GenericAtomizerTests
{
    private static AtomizedTheoryDocument Atomize(string markdown) =>
        AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            Encoding.UTF8.GetBytes(markdown),
            TheoryAtomizerRules.None);

    private static string[] Fingerprints(AtomizedTheoryDocument document) =>
        document.Claims.Select(static claim => claim.Fingerprints.RawSha256).ToArray();

    private static DigestionAtom ClaimContaining(AtomizedTheoryDocument document, string text) =>
        Assert.Single(document.Claims, atom =>
            Encoding.UTF8.GetString(atom.RawBytes.AsSpan()).Contains(text, StringComparison.Ordinal));

    [Fact]
    public void EveryHeadingBecomesASectionAtom()
    {
        var document = Atomize("# 卷首\n\n引言。\n\n## §1 主账\n\n一。\n\n## §2 位置\n\n二。\n");

        Assert.Equal(3, document.Claims.Length);
        Assert.All(["# 卷首", "## §1 主账", "## §2 位置"], heading =>
            Assert.Contains(document.Claims, atom =>
                Encoding.UTF8.GetString(atom.RawBytes.AsSpan()).Contains(heading, StringComparison.Ordinal)));
    }

    [Fact]
    public void ANumberedHeadingIsAddressedByItsOwnGenreTokenWithoutAnyRegisteredVocabulary()
    {
        var document = Atomize("# 卷首\n\n## 定理 22.2(甲)\n\n证。\n\n## 未登记体 3.4\n\n证。\n");

        Assert.Equal(2, document.Claims.Length);
    }

    [Fact]
    public void GenericAtomizerHasNoReservedIdentityNamespace()
    {
        var bytes = Encoding.UTF8.GetBytes("# Probe\n\n## unregistered 1.1\n\nclaim。\n");
        var ledger = DigestionTestSupport.EmptyDocument(AtomizerRegistry.GenericId);

        var alignment = DigestionLedgerAligner.Evaluate(
            ledger,
            DigestionTestSupport.Snapshot(("docs/source.md", bytes)),
            ledger,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(alignment.Findings);
        Assert.NotEmpty(alignment.Residual);
        Assert.All(alignment.Residual, static item => Assert.Equal(
            item.Atom.Fingerprints.RawSha256["sha256:".Length..],
            item.SuggestedAtomId));
    }

    [Fact]
    public void ABoldNumberedParagraphLeadIsAClaimAndABareNumberIsAnItem()
    {
        var document = Atomize("# 卷首\n\n**定理 1.1(甲)**。一。\n\n**1.2**。二。\n");

        Assert.Equal(2, document.Claims.Length);
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
    /// Content identity keeps re-ingest from rewriting untouched receipts.
    /// </summary>
    [Fact]
    public void InsertingASectionDoesNotChangeTheSectionsAroundIt()
    {
        var before = Atomize("# 卷首\n\n## §1 甲\n\n一。\n\n## §3 丙\n\n三。\n");
        var after = Atomize("# 卷首\n\n## §1 甲\n\n一。\n\n## §2 乙\n\n二。\n\n## §3 丙\n\n三。\n");

        Assert.Equal(2, before.Claims.Length);
        Assert.Equal(3, after.Claims.Length);
        Assert.Equal(
            ClaimContaining(before, "## §3 丙").Fingerprints,
            ClaimContaining(after, "## §3 丙").Fingerprints);
    }

    [Fact]
    public void AnAtomKeepsItsFingerprintWhenAnUnrelatedSectionIsInserted()
    {
        var before = Atomize("# 卷首\n\n## §1 甲\n\n一。\n\n## §3 丙\n\n三。\n");
        var after = Atomize("# 卷首\n\n## §1 甲\n\n一。\n\n## §2 乙\n\n二。\n\n## §3 丙\n\n三。\n");

        Assert.Equal(
            ClaimContaining(before, "## §3 丙").Fingerprints,
            ClaimContaining(after, "## §3 丙").Fingerprints);
    }

    [Fact]
    public void RepeatedHeadingTextProducesContentDistinctAtoms()
    {
        var document = Atomize("# 卷首\n\n## 边界\n\n一。\n\n## 边界\n\n二。\n");

        Assert.Equal(2, document.Claims.Length);
        Assert.Equal(2, Fingerprints(document).Distinct(StringComparer.Ordinal).Count());
    }

    /// <summary>
    /// Both shapes occur in real volumes: a heading that is a whole sentence, and a heading
    /// made only of punctuation. Neither may put an unbounded or empty field in the ledger.
    /// </summary>
    [Fact]
    public void ALongHeadingIsBoundedAndAPunctuationOnlyHeadingStillAddressesSomething()
    {
        var longHeading = new string('章', 200);
        var document = Atomize($"# {longHeading}\n\n一。\n\n## 《·》\n\n二。\n");

        Assert.Equal(2, document.Claims.Length);
        Assert.All(Fingerprints(document), static fingerprint =>
            Assert.Matches("^sha256:[0-9a-f]{64}$", fingerprint));
    }

    /// <summary>Two long headings that share a prefix must not collapse to one locator.</summary>
    [Fact]
    public void TwoLongHeadingsSharingAPrefixKeepDistinctLocators()
    {
        var prefix = new string('章', 200);
        var document = Atomize($"## {prefix}甲\n\n一。\n\n## {prefix}乙\n\n二。\n");

        var fingerprints = Fingerprints(document);
        Assert.Equal(2, fingerprints.Length);
        Assert.NotEqual(fingerprints[0], fingerprints[1]);
    }

    /// <summary>
    /// A claim table states one proposition per row, each with its own attestation and its
    /// own truth status — 定理级 next to open. Folding them into the section that holds them
    /// produces an atom no single Lean declaration can discharge, so each data row is a
    /// claim of its own. The header row names columns, not propositions, and is not one.
    /// </summary>
    [Fact]
    public void EachDataRowOfATableIsItsOwnClaimAndTheHeaderRowIsNot()
    {
        var document = Atomize(
            "## §3 词典\n\n| 条目 | 内容 | 分型 |\n|---|---|---|\n"
            + "| Euler 积 = 独立性 | v_p 独立几何分布 | 定理级 |\n"
            + "| 极点 = 相变 | Hagedorn 于 β=1 | 定理级 |\n"
            + "| Sarnak 熵分界 | μ ⟂ 零拓扑熵系统 | open |\n");

        // The section keeps an atom of its own because its body is not empty: it holds the
        // title and the column legend, which is what the section itself says. What it no
        // longer holds is the eleven propositions that used to be folded into it.
        Assert.Equal(4, document.Claims.Length);
    }

    /// <summary>
    /// A heading whose whole body is claimed by finer atoms leaves nothing behind but its
    /// own line. Such an atom carries no proposition, can never be discharged, and would
    /// sit residual-open forever; the heading text is not lost, since every atom beneath it
    /// already carries it in its context.
    /// </summary>
    [Fact]
    public void ASectionWhoseBodyIsEntirelyClaimedDoesNotLeaveAnEmptyHeadingAtom()
    {
        var document = Atomize("# 卷\n\n## §2 甲\n\n**定理 1.1**。证。\n\n## §3 乙\n\n散文。\n");

        Assert.Equal(2, document.Claims.Length);
        Assert.DoesNotContain(document.Claims, atom =>
            Encoding.UTF8.GetString(atom.RawBytes.AsSpan()).Trim() == "## §2 甲");
    }

    /// <summary>
    /// The volume's own title, which is a hyphenated identifier ending in a digit. Reading
    /// it as genre ENTROPY-INFO-PRIMES-O numbered 5 is what the repository's real
    /// ENTROPY-INFO-PRIMES-O5.md digested to before a genre token was required to be a word.
    /// </summary>
    [Fact]
    public void AHyphenatedTitleEndingInADigitIsASectionNotAClaim()
    {
        var document = Atomize("# ENTROPY-INFO-PRIMES-O5:热层卷宗(审计版 r1)\n\n前言。\n");

        Assert.Single(document.Claims);
    }

    [Theory]
    [InlineData("## 定理 1.1\n\n证。\n")]
    [InlineData("## 定理1.1\n\n证。\n")]
    [InlineData("## Theorem 2.3\n\n证。\n")]
    public void AGenreTokenIsStillReadWithOrWithoutASeparator(string source)
    {
        Assert.Single(Atomize(source).Claims);
    }

    [Fact]
    public void AClaimIncludesItsDisplayedConclusionUntilTheNextClaimOrPeerHeading()
    {
        const string firstClaim =
            "## 定理 1.1（合成展示结论）\n\n"
            + "设最大纤维大小如下：\n\n"
            + "$$\n"
            + "\\boxed{\n"
            + "m_U\n"
            + "===\n\n"
            + "\\max_{y \\in Y}|U^{-1}(y)|\n"
            + "}\n"
            + "$$\n\n"
            + "### 下界\n\n"
            + "每个纤维中的状态需要不同标签。\n\n";
        var document = Atomize(
            firstClaim
            + "## 引理 1.2（下一条）\n\n"
            + "这是独立的下一条 claim。\n");

        Assert.Equal(2, document.Claims.Length);
        Assert.Equal(
            firstClaim,
            Encoding.UTF8.GetString(ClaimContaining(document, "定理 1.1").RawBytes.AsSpan()));
    }

    [Fact]
    public void ALegacyBracketDisplayIsOpaqueToClaimDiscovery()
    {
        const string firstClaim =
            "## 定理 1.3（旧式展示分隔符）\n\n"
            + "定义如下：\n\n"
            + "[\n"
            + "\\boxed{\n"
            + "m_U\n"
            + "===\n\n"
            + "\\max_{y \\in Y}|U^{-1}(y)|\n"
            + "}\n"
            + "]\n\n";
        var document = Atomize(
            firstClaim
            + "## 推论 1.4（下一条）\n\n"
            + "这是独立的下一条 claim。\n");

        Assert.Equal(2, document.Claims.Length);
        Assert.Equal(
            firstClaim,
            Encoding.UTF8.GetString(ClaimContaining(document, "定理 1.3").RawBytes.AsSpan()));
    }

    [Fact]
    public void AdjacentClaimsRemainSeparateEvenWhenTheSecondClaimUsesADeeperHeading()
    {
        const string firstClaim = "## 定理 2.1（第一条）\n\n第一条正文。\n\n";
        const string secondClaim = "### 引理 2.2（第二条）\n\n第二条正文。\n";

        var document = Atomize(firstClaim + secondClaim);

        Assert.Equal(2, document.Claims.Length);
        Assert.Equal(
            firstClaim,
            Encoding.UTF8.GetString(ClaimContaining(document, "定理 2.1").RawBytes.AsSpan()));
        Assert.Equal(
            secondClaim,
            Encoding.UTF8.GetString(ClaimContaining(document, "引理 2.2").RawBytes.AsSpan()));
    }

    [Fact]
    public void TheDefaultAtomizerIsRegistered()
    {
        Assert.Contains(AtomizerRegistry.GenericId, AtomizerRegistry.RegisteredIds);
    }

    /// <summary>
    /// The content fingerprint is a function of the source bytes alone: loaded volume vocabularies are
    /// not an input, so editing another volume's dialect cannot churn this volume's ledger.
    /// </summary>
    [Fact]
    public void TheFingerprintDoesNotDependOnAnyLoadedVocabulary()
    {
        var markdown = "# 卷首\n\n## 定理 1.1\n\n证。\n";
        var bytes = Encoding.UTF8.GetBytes(markdown);
        Assert.Equal(
            Fingerprints(AtomizerRegistry.Atomize(AtomizerRegistry.GenericId, bytes, TheoryAtomizerRules.None)),
            Fingerprints(AtomizerRegistry.Atomize(
                AtomizerRegistry.GenericId, bytes, DigestionTestSupport.Rules)));
    }

    [Fact]
    public void AMultiClauseSectionClaimCarriesADeterministicClausePlan()
    {
        var bytes = System.Text.Encoding.UTF8.GetBytes(
            "## T1. 包络\n\n定义与记号。\n\n**定理 T1**。主张。\n\n**结案判据**:核验单调性。\n");

        var first = GenericAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var second = GenericAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        var claim = Assert.Single(first.Claims);
        var plan = Assert.Single(first.ClausePlans);
        Assert.Equal(claim.Fingerprints.RawSha256, plan.Parent.Fingerprints.RawSha256);
        Assert.Equal(3, plan.Children.Length);
        Assert.All(plan.Children, child => Assert.Equal(
            DigestionFingerprint.Compute(child.RawBytes.AsSpan()).RawSha256,
            child.Fingerprints.RawSha256));
        Assert.Equal(
            claim.RawBytes.ToArray(),
            plan.Children.SelectMany(static child => child.RawBytes.ToArray()).ToArray());
        Assert.Equal(
            Assert.Single(second.ClausePlans).Children
                .Select(static child => (child.Fingerprints.RawSha256, child.Fingerprints.RawSha256)),
            plan.Children.Select(static child => (child.Fingerprints.RawSha256, child.Fingerprints.RawSha256)));
    }

    [Fact]
    public void ASingleClauseSectionClaimCarriesNoClausePlan()
    {
        var bytes = System.Text.Encoding.UTF8.GetBytes("## T0. 单款\n\n只有一段散文主张。\n");

        var document = GenericAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.Single(document.Claims);
        Assert.Empty(document.ClausePlans);
    }
}
