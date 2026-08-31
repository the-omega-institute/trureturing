using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    private const string FourthProductionSource =
        "docs/develop/theory/INTERFACE_PAPER.md";

    private const string InterfacePhilosophySource =
        "docs/develop/theory/INTERFACE_PHILOSOPHY.md";

    private static void AssertContentIdentity(DigestionAtom atom) => Assert.Equal(
        DigestionFingerprint.Compute(atom.RawBytes.AsSpan()).RawSha256,
        atom.Fingerprints.RawSha256);

    private static void AssertContentIdentities(AtomizedTheoryDocument document, int expectedCount)
    {
        Assert.Equal(expectedCount, document.Claims.Length);
        Assert.All(document.Claims, AssertContentIdentity);
    }

    private static DigestionAtom ClaimContaining(AtomizedTheoryDocument document, string text) =>
        Assert.Single(document.Claims, atom =>
            Encoding.UTF8.GetString(atom.RawBytes.AsSpan()).Contains(text, StringComparison.Ordinal));

    [Fact]
    public void RegistryFailsClosedForAnUnknownAtomizerAndListsRegisteredIds()
    {
        const string unknown = "unregistered-v1";

        var error = Assert.Throws<FormatException>(() =>
            AtomizerRegistry.Atomize(unknown, Array.Empty<byte>(), DigestionTestSupport.Rules));

        Assert.Equal(
            $"Unknown atomizer id '{unknown}'. Registered atomizers: "
            + string.Join(", ", AtomizerRegistry.RegisteredIds)
            + ".",
            error.Message);
    }

    [Fact]
    public void GictAdapterBuildsClaimWithHeadingScaffoldAndReassemblesExactBytes()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n## VII.7 接口\r\n\r\n"
            + "**定理 7.15(G 轴质量)**〔定理·证〕。黄金频率最优。\r\n\r\n"
            + "*证明*。证毕。\r\n\r\n尾注。\r\n");

        var document = GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var atom = Assert.Single(document.Claims);

        AssertContentIdentity(atom);
        Assert.Equal(["GICT", "VII.7 接口"], atom.Context.Select(static item => item.Text));
        Assert.Equal(bytes, document.Reassemble().ToArray());
        Assert.Matches("^sha256:[0-9a-f]{64}$", atom.Fingerprints.RawSha256);
        Assert.Matches("^sha256:[0-9a-f]{64}$", atom.Fingerprints.NormalizedSha256);
    }

    [Fact]
    public void PzgAdapterSeparatesClosedTheoremAndOpenLedgerClaim()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n## 第二十六章 桥通道\n\n"
            + "**定理 26.3(桥通道)**〔closed〕。通道存在。\n\n"
            + "**账目 26.4(RH 的三面孔)**〔open〕。正性未知。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 2);
        Assert.All(document.Claims, atom =>
            Assert.Equal(["PZG", "第二十六章 桥通道"], atom.Context.Select(static item => item.Text)));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    // Byte-faithful canonical status-marker forms used by theory atoms.
    private const string PlainClosedMarker = "〔closed〕";
    private const string QualifiedClosedMarker = "〔closed;数值证书〕";
    private const string UnterminatedPlainClosedMarker = "〔closed";
    private const string UnterminatedClosedMarker = "〔closed;数值证书";
    private const string WhitespaceBeforeSeparatorMarker = "〔closed ;数值证书〕";
    private const string FullwidthSeparatorMarker = "〔closed；数值证书〕";
    private const string WhitespaceStatusMarker = "〔 closed〕";
    private const string ExtraSeparatorMarker = "〔closed;数值证书;附注〕";
    private const string BlankQualifierMarker = "〔closed;  〕";
    private const string SpacedClosedMarker = "  〔closed〕";

    [Theory]
    [InlineData(PlainClosedMarker, "Valid", "closed", null)]
    [InlineData(QualifiedClosedMarker, "Valid", "closed", "数值证书")]
    [InlineData(UnterminatedPlainClosedMarker, "Malformed", "closed", null)]
    [InlineData(UnterminatedClosedMarker, "Malformed", "closed", "数值证书")]
    [InlineData(WhitespaceBeforeSeparatorMarker, "Malformed", "closed ", "数值证书")]
    [InlineData(FullwidthSeparatorMarker, "Malformed", "closed；数值证书", null)]
    [InlineData(WhitespaceStatusMarker, "Malformed", " closed", null)]
    [InlineData(ExtraSeparatorMarker, "Malformed", "closed", "数值证书;附注")]
    [InlineData(BlankQualifierMarker, "Malformed", "closed", "  ")]
    [InlineData(SpacedClosedMarker, "Malformed", "closed", null)]
    public void PzgAdapterOwnsCanonicalStatusMarkerParsing(
        string marker,
        string expectedKind,
        string expectedStatus,
        string? expectedQualifier)
    {
        var bytes = Encoding.UTF8.GetBytes($"# PZG\n\n**定理 26.3**{marker}");

        var atom = Assert.Single(PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);

        Assert.Equal(expectedKind, atom.StatusMarker.Kind.ToString());
        Assert.Equal(expectedStatus, atom.StatusMarker.Status);
        Assert.Equal(expectedQualifier, atom.StatusMarker.Qualifier);
    }

    [Fact]
    public void WmV1RegistryUsesOrdinalIds()
    {
        Assert.Equal(
            [AtomizerRegistry.ConeId, AtomizerRegistry.GenericId,
                AtomizerRegistry.GictId,
                AtomizerRegistry.ObserverId,
                AtomizerRegistry.PeriodicTreeId,
                AtomizerRegistry.PzgId,
                AtomizerRegistry.WmId,
            ],
            AtomizerRegistry.RegisteredIds.ToArray());
        Assert.Equal(
            AtomizerRegistry.RegisteredIds.Order(StringComparer.Ordinal).ToArray(),
            AtomizerRegistry.RegisteredIds.ToArray());
    }

    [Fact]
    public void GictAdapterTreatsEachAppendixConstantRowAsAnAtomicClaim()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n## 附录 A:常数总表\n\n"
            + "| 常数 | 值 |\n|---|---|\n"
            + "| κ | 1/(2φ) |\n"
            + "| C₀ | φ/2 |\n"
            + "| **C_φ** | 0.045 |\n");

        var document = GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 3);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgAdapterTreatsOpenLedgerItemsAsAtomicClaims()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n## 第二十九章 开放账本\n\n"
            + "**O-5**〔open〕发动机未闭。\n"
            + "**O-6**〔open〕正性未闭。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 2);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Theory]
    [InlineData("**§11.1 章程(三定义,ZFC 内,零新公理)**。claim。")]
    [InlineData("**§11.2 四问模板(逐层机械生成)**。claim。")]
    [InlineData("**§11.3 三科目终表(公理之辩四连案终审)**。claim。")]
    [InlineData("**§11.4 首件产品指针**。claim。")]
    public void ObserverV1RecognizesTheV335PeriodicTableClaimLeads(string claim)
    {
        var bytes = Encoding.UTF8.GetBytes($"# Observer\n\n{claim}\n");

        var atom = Assert.Single(AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes, DigestionTestSupport.Rules).Claims);

        AssertContentIdentity(atom);
    }

    [Theory]
    [InlineData("**§12.1 互反-干涉庭(\"真理一半看不见\")**。claim。")]
    [InlineData("**§12.2 投影-干涉庭与署名**。claim。")]
    [InlineData("**§12.3 滤镜与视界庭(Fable/Mythos)**。claim。")]
    public void ObserverV1RecognizesTheV6SemanticCourtClaimLeads(string claim)
    {
        var bytes = Encoding.UTF8.GetBytes($"# Observer\n\n{claim}\n");

        var atom = Assert.Single(AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes, DigestionTestSupport.Rules).Claims);

        AssertContentIdentity(atom);
    }

    [Fact]
    public void GictAdapterIdentifiesNumberedNotesAsClaims()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**注 2.5(Why five)**。claim。\n");

        var atom = Assert.Single(GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);

        AssertContentIdentity(atom);
    }

    [Fact]
    public void GictAdapterRecognizesSurveyAndMapsKind()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**勘察 6.35(量子度量丛与谱三元组路标)**〔勘察〕。claim。\n");

        var atom = Assert.Single(GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);

        AssertContentIdentity(atom);
    }

    [Fact]
    public void GictV330AppendixDialectProducesMetadataAndCoarseAtoms()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n"
            + "> **谱系**:v3.29 → **v3.30:附录 E 增订五**\n\n"
            + "## 附录 E 增订五(v3.30)\n\n"
            + "**E.22 零轨道弧一:36-定理与镜像条款**〔定理·两层证 + 修正条款〕。claim。\n\n"
            + "**E.23 站队塔**〔定理群 + 判负 + 预言制度〕。claim。\n\n"
            + "**E.24 BHK–W3 与三走一体**〔锚 + 恒等 + 条款〕。claim。\n\n"
            + "**E.25 钉-辐角与余割恒等**〔定理 + 册卷〕。claim。\n\n"
            + "**E.26 统计弧终局**〔判负册重案〕。claim。\n\n"
            + "**E.27 城同余定理**〔本卷压轴,自足证明〕。claim。\n\n"
            + "**E.28 开放问题定位与仪器铁款**。claim。\n");

        var document = GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 8);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgV330SupplementHeadingsProduceSectionAtoms()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG_BEDC 增补册:第 330 版记事(轮 471–527;2026-07-18)\n"
            + "本批主题。\n\n"
            + "## 评注 27.363–27.365(36-定理与镜像条款)\n内容。\n\n"
            + "## 评注 27.366–27.371(站队塔)\n内容。\n\n"
            + "## 判负册本批\n内容。\n\n"
            + "## 候查清单变动\n内容。\n\n"
            + "## 本批收束五判\n内容。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 6);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgAdapterIdentifiesEveryProductionNumberedClaimKind()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n"
            + "**后果 7.4**。a。\n\n"
            + "**原则 14.3**。b。\n\n"
            + "**规格 20.2**。c。\n\n"
            + "**契约 23.1**。d。\n\n"
            + "**定理形 6.190**。e。\n\n"
            + "**前沿引注 6.56**。f。\n\n"
            + "**延表 6.38′**。g。\n\n"
            + "**路线 21.1**。h。\n\n"
            + "**〔27.82 追注:receipt〕**。i。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        AssertContentIdentities(document, 9);
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    [InlineData("\r")]
    public void ObserverAdapterRecordsAnUnknownBoldClaimLead(string newLine)
    {
        var bytes = Encoding.UTF8.GetBytes(
            $"# Observer{newLine}{newLine}## 11. New section{newLine}{newLine}"
            + $"**新判词。** claim。{newLine}");

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.ObserverId,
            bytes,
            DigestionTestSupport.Rules);

        Assert.Single(document.Claims);
        Assert.Equal(["**新判词。**"], document.UnregisteredGenres.ToArray());
    }

    [Theory]
    [InlineData(true, "\n")]
    [InlineData(false, "\n")]
    [InlineData(true, "\r\n")]
    [InlineData(false, "\r\n")]
    public void ObserverAdapterRecordsAnUnknownBoldTableClaimLead(
        bool leadingPipe,
        string newLine)
    {
        var header = leadingPipe ? "| Lead | Claim |" : "Lead | Claim";
        var delimiter = leadingPipe ? "| --- | --- |" : "--- | ---";
        var claim = leadingPipe ? "| **新判词。** | claim。 |" : "**新判词。** | claim。";
        var bytes = Encoding.UTF8.GetBytes(
            $"# Observer{newLine}{newLine}{header}{newLine}{delimiter}{newLine}{claim}{newLine}");

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.ObserverId,
            bytes,
            DigestionTestSupport.Rules);

        Assert.Single(document.Claims);
        Assert.Equal(["**新判词。**"], document.UnregisteredGenres.ToArray());
    }

    [Fact]
    public void ObserverAdapterRecordsAnIndentedUnknownBoldClaimLead()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n   **新判词。** claim。\n\n"
            + "**定理(观察者代数的唯一形态)。** known。\n");

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.ObserverId,
            bytes,
            DigestionTestSupport.Rules);

        Assert.Equal(2, document.Claims.Length);
        Assert.Equal(["**新判词。**"], document.UnregisteredGenres.ToArray());
    }

    [Theory]
    [InlineData("**Q1(伪造标签):推出。** claim。")]
    [InlineData("**Q2(伪造标签):条件推出。** claim。")]
    [InlineData("**Q3(伪造标签):搬家。** claim。")]
    [InlineData("**Q4(伪造标签)。** claim。")]
    [InlineData("**已结案(伪造标签):** claim。")]
    [InlineData("**遗留(伪造标签):** claim。")]
    public void ObserverAdapterRecordsMalformedKnownPrefixAsAnUnregisteredLead(string malformedLead)
    {
        var bytes = Encoding.UTF8.GetBytes(
            $"# Observer\n\n{malformedLead}\n\n"
            + "**定理(观察者代数的唯一形态)。** known。\n");

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.ObserverId,
            bytes,
            DigestionTestSupport.Rules);

        Assert.Equal(2, document.Claims.Length);
        Assert.Equal(
            [TheorySourceFormatException.ClaimLead(malformedLead)],
            document.UnregisteredGenres.ToArray());
    }

    [Fact]
    public void ObserverAdapterKeepsContentDistinctRepeatedClaimLeads()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n"
            + "**定理(观察者代数的唯一形态)。** first。\n\n"
            + "**定理(观察者代数的唯一形态)。** second。\n");

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.ObserverId,
            bytes,
            DigestionTestSupport.Rules);

        AssertContentIdentities(document, 2);
    }

    [Fact]
    public void RestrictedNormalizationChangesOnlyBomLineEndingsAndUnicodeNormalization()
    {
        var decomposed = "\uFEFFCafe\u0301  \r\nnext\rline\n";
        var composed = "Caf\u00e9  \nnext\nline\n";
        var first = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(decomposed));
        var second = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(composed));

        Assert.NotEqual(first.RawSha256, second.RawSha256);
        Assert.Equal(first.NormalizedSha256, second.NormalizedSha256);
    }

    [Fact]
    public void UnknownNumberedClaimKindIsClassifiedAsOpenLedgerDebt()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**未知体 1.1(Unknown kind)**。claim。\n");

        var alignment = AlignUnregisteredGenres(bytes);

        Assert.Empty(alignment.Findings);
        AssertContentIdentity(Assert.Single(alignment.Residual).Atom);
        Assert.Equal(
            ["未知体"],
            alignment.GenreRegistryChecks["source"].UnregisteredGenres.ToArray());
        Assert.Empty(alignment.Fallbacks);
    }

    private static void AssertRecognitionComplete(
        AtomizedTheoryDocument document,
        byte[] sourceBytes)
    {
        Assert.NotEmpty(document.Claims);
        Assert.Equal(document.Claims.Length, document.Slices.Count(static slice => slice.IsClaim));
        Assert.Equal(sourceBytes, document.Reassemble().ToArray());
        var atomIds = new HashSet<string>(StringComparer.Ordinal);
        Assert.All(document.Claims, atom =>
        {
            Assert.False(string.IsNullOrWhiteSpace(atom.Fingerprints.RawSha256));
            Assert.True(atomIds.Add(atom.Fingerprints.RawSha256), $"duplicate atom id: {atom.Fingerprints.RawSha256}");
            Assert.InRange(atom.StartByte, 0, sourceBytes.Length - 1);
            Assert.InRange(atom.EndByte, atom.StartByte + 1, sourceBytes.Length);
            Assert.Equal(
                sourceBytes[atom.StartByte..atom.EndByte],
                atom.RawBytes.ToArray());
            Assert.Equal(
                DigestionFingerprint.Compute(atom.RawBytes.AsSpan()),
                atom.Fingerprints);
        });
    }

    private static void AssertSplitIdempotent(
        string atomizerId,
        AtomizedTheoryDocument first,
        TheoryAtomizerRules? rules = null)
    {
        var reassembled = first.Reassemble();
        var second = AtomizerRegistry.Atomize(
            atomizerId,
            reassembled.AsSpan(),
            rules ?? DigestionTestSupport.Rules);

        Assert.Equal(
            first.Claims.Select(static atom =>
                (atom.Fingerprints.RawSha256, atom.StartByte, atom.EndByte, atom.Fingerprints)),
            second.Claims.Select(static atom =>
                (atom.Fingerprints.RawSha256, atom.StartByte, atom.EndByte, atom.Fingerprints)));
        Assert.Equal(first.Claims.Length, second.Claims.Length);
        for (var index = 0; index < first.Claims.Length; index++)
        {
            Assert.Equal(first.Claims[index].RawBytes.ToArray(), second.Claims[index].RawBytes.ToArray());
            Assert.Equal(
                first.Claims[index].Context.Select(static item => (item.Level, item.Text)),
                second.Claims[index].Context.Select(static item => (item.Level, item.Text)));
        }

        Assert.Equal(
            first.Slices.Select(static slice => slice.IsClaim),
            second.Slices.Select(static slice => slice.IsClaim));
        Assert.Equal(first.Slices.Length, second.Slices.Length);
        for (var index = 0; index < first.Slices.Length; index++)
        {
            Assert.Equal(first.Slices[index].RawBytes.ToArray(), second.Slices[index].RawBytes.ToArray());
        }
    }

    private const string WmTitle = "# 世界模型账本卷:公理纲要(BEDC-WM)";

    private const string WmAppendix =
        "### §7-附 尸检账(只增不删)\n\n**尸检 P-1**。判据自身必须受检。\n\n";

    private const string WmDiscipline =
        "> 一句话:数学卷问何以为真。\n"
        + "> 纪律:每条断言携带状态标签。\n";

    private const string WmCurrentTodoClosure =
        "**当前待办**(随版滚动):依判决出 **v0.2**"
        + "(新行追加于版本账,本节追加 v0.2 校核块)。";

    private static string CanonicalWmFixture() =>
        string.Concat(CanonicalWmFixtureSegments());

    private static string CanonicalWmV02Fixture()
    {
        var source = CanonicalWmFixture();
        source = source.Replace(
            "- **v0.1**(2026-07-18)首轮结账。\n",
            "- **v0.1**(2026-07-18)首轮结账。\n- **v0.2**(2026-07-23)勘误轮结账。\n",
            StringComparison.Ordinal);
        return source + "\n**v0.2 校核**(2026-07-23):追加校核,旧块不改。\n";
    }

    private static IReadOnlyList<string> CanonicalWmFixtureSegments()
    {
        var segments = new List<string>
        {
            WmTitle + "\n\n"
                + "**别名**:账本世界模型纲要\n"
                + "**定位**:经验姊妹卷\n\n"
                + "**版本账**(append-only):\n",
            "- **v0**(2026-07-18)立卷。\n",
            "- **v0.1**(2026-07-18)首轮结账。\n",
            "\n" + WmDiscipline + "\n---\n\n",
        };

        for (var section = 0; section <= 11; section++)
        {
            segments.Add($"## {section}. Section {section}\n\nSection {section} claim.\n\n");
            if (section == 7)
            {
                segments.Add(WmAppendix);
            }
        }

        segments.Add(
            "## 校核记录(append-only,按版分块)\n\n"
            + "**v0 校核**(2026-07-18):立卷校核。\n\n"
            + "**v0.1 校核**(2026-07-18):首轮校核。\n\n"
            + WmCurrentTodoClosure + "\n");
        return segments;
    }
    [Fact]
    public void InterfacePaperDialectPreservesDuplicateBlocksAsDistinctOccurrences()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, FourthProductionSource));

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.PzgId,
            bytes,
            DigestionTestSupport.Rules);

        var duplicateContent = document.Claims
            .GroupBy(static atom => atom.Fingerprints.RawSha256, StringComparer.Ordinal)
            .Where(static group => group.Count() > 1)
            .ToArray();
        Assert.Equal(2, duplicateContent.Length);
        Assert.All(duplicateContent, static group => Assert.Equal(2, group.Count()));
    }

    [Fact]
    public void PzgMultiClaimParagraphIncludesIndentedAndUnindentedContinuationLines()
    {
        const string firstClaim =
            "**定理 1.1(First)**。lead。\n"
            + "  indented continuation。\n"
            + "unindented continuation。\n";
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n"
            + firstClaim
            + "**引理 1.2(Second)**。next。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var atom = ClaimContaining(document, "**定理 1.1");

        Assert.Equal(firstClaim, Encoding.UTF8.GetString(atom.RawBytes.AsSpan()));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgLastClaimInMultiClaimParagraphExtendsThroughFollowingProofParagraphs()
    {
        const string lastClaimAndProof =
            "**引理 1.2(Second)**。lead。\n\n"
            + "ordinary proof paragraph。\n\n"
            + "second proof paragraph。\n\n";
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n"
            + "**定理 1.1(First)**。lead。\n"
            + lastClaimAndProof
            + "**命题 1.3(Next)**。next。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var atom = ClaimContaining(document, "**引理 1.2");

        Assert.Equal(lastClaimAndProof, Encoding.UTF8.GetString(atom.RawBytes.AsSpan()));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void PzgSingleClaimParagraphStillExtendsThroughFollowingProofParagraphs()
    {
        const string claimAndProof =
            "**定理 2.1(Single)**。lead。\n\n"
            + "ordinary proof paragraph。\n\n";
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n"
            + claimAndProof
            + "**引理 2.2(Next)**。next。\n");

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var atom = ClaimContaining(document, "**定理 2.1");

        Assert.Equal(claimAndProof, Encoding.UTF8.GetString(atom.RawBytes.AsSpan()));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void InterfacePhilosophyTheorem612IncludesBothContinuationLines()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, InterfacePhilosophySource));

        var document = PzgAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var atom = ClaimContaining(document, "**定理 6.12");
        var rawText = Encoding.UTF8.GetString(atom.RawBytes.AsSpan());

        Assert.Contains(
            "  −k_min − O(log Q) ≤ log(|C_Q(R)| / |F_Q|) ≤ −K(y|x) + O(log Q)。",
            rawText,
            StringComparison.Ordinal);
        Assert.Contains(
            "(iii)[证纲] 对定理 6.6 之构造记录可加强选取",
            rawText,
            StringComparison.Ordinal);
        Assert.DoesNotContain("**案卷 6.12.1", rawText, StringComparison.Ordinal);
    }

    private static DigestionLedgerAlignment AlignUnregisteredGenres(byte[] bytes)
    {
        var ledger = DigestionTestSupport.EmptyDocument(AtomizerRegistry.PzgId);
        return DigestionLedgerAligner.Evaluate(
            ledger,
            DigestionTestSupport.Snapshot(("docs/source.md", bytes)),
            ledger,
            DigestionAlignmentMode.Ingest);
    }
}
internal static class SyntheticNumberedAtomizer { internal static string Id => AtomizerRegistry.GictId; }
