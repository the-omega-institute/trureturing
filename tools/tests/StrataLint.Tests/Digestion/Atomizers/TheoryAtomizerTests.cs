using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    private const string SecondProductionSource =
        "docs/develop/theory/PZG_BEDC.md";
    private const string FourthProductionSource =
        "docs/develop/theory/INTERFACE_PAPER.md";

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

        Assert.Equal("theorem/7.15", atom.AstPath);
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

        Assert.Equal(["theorem/26.3", "ledger/26.4"], document.Claims.Select(static item => item.AstPath));
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
    public void WmV1RegistryUsesOrdinalIdsAndTheWmResidualPrefix()
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
        Assert.Equal("wm", AtomizerRegistry.Require(AtomizerRegistry.WmId).ResidualPrefix);
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

        Assert.Equal(
            ["constant/kappa", "constant/C0", "constant/Cphi"],
            document.Claims.Select(static item => item.AstPath));
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

        Assert.Equal(["open/O-5", "open/O-6"], document.Claims.Select(static item => item.AstPath));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Theory]
    [InlineData("**§11.1 章程(三定义,ZFC 内,零新公理)**。claim。", "periodic-table/charter")]
    [InlineData("**§11.2 四问模板(逐层机械生成)**。claim。", "periodic-table/four-question-template")]
    [InlineData("**§11.3 三科目终表(公理之辩四连案终审)**。claim。", "periodic-table/axiom-hypothesis-definition")]
    [InlineData("**§11.4 首件产品指针**。claim。", "periodic-table/first-product")]
    public void ObserverV1RecognizesTheV335PeriodicTableClaimLeads(
        string claim,
        string expectedAstPath)
    {
        var bytes = Encoding.UTF8.GetBytes($"# Observer\n\n{claim}\n");

        var atom = Assert.Single(AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes, DigestionTestSupport.Rules).Claims);

        Assert.Equal(expectedAstPath, atom.AstPath);
    }

    [Theory]
    [InlineData("**§12.1 互反-干涉庭(\"真理一半看不见\")**。claim。", "semantic-court/reciprocity-interference")]
    [InlineData("**§12.2 投影-干涉庭与署名**。claim。", "semantic-court/projection-interference")]
    [InlineData("**§12.3 滤镜与视界庭(Fable/Mythos)**。claim。", "semantic-court/filters-and-horizons")]
    public void ObserverV1RecognizesTheV6SemanticCourtClaimLeads(
        string claim,
        string expectedAstPath)
    {
        var bytes = Encoding.UTF8.GetBytes($"# Observer\n\n{claim}\n");

        var atom = Assert.Single(AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes, DigestionTestSupport.Rules).Claims);

        Assert.Equal(expectedAstPath, atom.AstPath);
    }

    [Fact]
    public void GictAdapterIdentifiesNumberedNotesAsClaims()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**注 2.5(Why five)**。claim。\n");

        var atom = Assert.Single(GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);

        Assert.Equal("note/2.5", atom.AstPath);
    }

    [Fact]
    public void GictAdapterRecognizesSurveyAndMapsKind()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**勘察 6.35(量子度量丛与谱三元组路标)**〔勘察〕。claim。\n");

        var atom = Assert.Single(GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);

        Assert.Equal("survey/6.35", atom.AstPath);
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

        Assert.Equal(
            [
                "metadata/lineage",
                "appendix/E.22",
                "appendix/E.23",
                "appendix/E.24",
                "appendix/E.25",
                "appendix/E.26",
                "appendix/E.27",
                "appendix/E.28",
            ],
            document.Claims.Select(static item => item.AstPath));
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

        Assert.Equal(
            [
                "metadata/supplement/330",
                "remark/27.363-27.365",
                "remark/27.366-27.371",
                "negative-register/batch",
                "research-queue/batch",
                "verdict/batch",
            ],
            document.Claims.Select(static item => item.AstPath));
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

        Assert.Equal(
            [
                "consequence/7.4",
                "principle/14.3",
                "specification/20.2",
                "contract/23.1",
                "theorem-form/6.190",
                "frontier-note/6.56",
                "extension-table/6.38′",
                "route/21.1",
                "trace-note/27.82",
            ],
            document.Claims.Select(static item => item.AstPath));
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
    public void ObserverAdapterRejectsADuplicateClaimLocator()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n"
            + "**定理(观察者代数的唯一形态)。** first。\n\n"
            + "**定理(观察者代数的唯一形态)。** second。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes, DigestionTestSupport.Rules));

        Assert.Contains("duplicate observer claim locator", error.Message, StringComparison.Ordinal);
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
    public void DuplicateClaimLocatorIsAmbiguousAndFailsClosed()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 7.15(A)**。一。\n\n**定理 7.15(B)**。二。\n");

        var document = GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules);
        var error = Assert.Throws<FormatException>(() => document.ResolveClaim("theorem/7.15"));

        Assert.Contains("ambiguous", error.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void UnknownNumberedClaimKindIsClassifiedAsALedgerFinding()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**未知体 1.1(Unknown kind)**。claim。\n");

        var alignment = AlignUnregisteredGenres(bytes);

        var finding = Assert.Single(alignment.Findings);
        Assert.Contains("source source", finding, StringComparison.Ordinal);
        Assert.Contains("未知体", finding, StringComparison.Ordinal);
        Assert.Empty(alignment.Residual);
        Assert.Empty(alignment.Fallbacks);
    }

    [Fact]
    public void GictIngestionSubtractsNormalizedMatchAndAdmitsSemanticRewriteAsResidual()
    {
        var oldBytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n**定理 1.1(Test)**。claim。\r\n\r\n*证明*。done。\r\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var ledger = new[] { LedgerEntry("gict-old", AtomizerRegistry.GictId, oldAtom) };
        var lineEndingOnly = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。claim。\n\n*证明*。done。\n");

        var seen = TheoryIngestion.AdmitResidual(
            AtomizerRegistry.GictId,
            lineEndingOnly,
            ledger,
            DigestionTestSupport.Rules);

        var match = Assert.Single(seen.Seen);
        Assert.Equal("gict-old", match.LedgerAtomId);
        Assert.Equal(DigestionFingerprintMatch.Normalized, match.Match);
        Assert.Empty(seen.Residual);

        var rewritten = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。semantically rewritten claim。\n");
        var admitted = TheoryIngestion.AdmitResidual(
            AtomizerRegistry.GictId,
            rewritten,
            ledger,
            DigestionTestSupport.Rules);

        Assert.Empty(admitted.Seen);
        var residual = Assert.Single(admitted.Residual);
        Assert.Equal(DigestionMigrationState.Residual, residual.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, residual.ProjectedStatus.Truth);
        Assert.NotEqual(oldAtom.Fingerprints.RawSha256, residual.Atom.Fingerprints.RawSha256);
        Assert.Equal(
            "gict-residual-" + residual.Atom.Fingerprints.RawSha256["sha256:".Length..],
            residual.SuggestedAtomId);
    }

    [Fact]
    public void PzgIngestionSubtractsRawMatchAndAdmitsNewClaim()
    {
        var oldBytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 1.1(Test)**〔closed〕。claim。\n");
        var oldAtom = Assert.Single(PzgAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var ledger = new[] { LedgerEntry("pzg-old", AtomizerRegistry.PzgId, oldAtom) };

        var seen = TheoryIngestion.AdmitResidual(AtomizerRegistry.PzgId, oldBytes, ledger, DigestionTestSupport.Rules);
        var incoming = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 1.2(New)**〔open〕。new claim。\n");
        var admitted = TheoryIngestion.AdmitResidual(AtomizerRegistry.PzgId, incoming, ledger, DigestionTestSupport.Rules);

        Assert.Equal(DigestionFingerprintMatch.Raw, Assert.Single(seen.Seen).Match);
        Assert.Empty(seen.Residual);
        Assert.Equal("theorem/1.2", Assert.Single(admitted.Residual).Atom.AstPath);
    }

    [Fact]
    public void IngestionFailsClosedWhenOneAtomMatchesMultipleLedgerReceipts()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);
        var ledger = new[]
        {
            LedgerEntry("gict-first", AtomizerRegistry.GictId, atom),
            LedgerEntry("gict-second", AtomizerRegistry.GictId, atom),
        };

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(AtomizerRegistry.GictId, bytes, ledger, DigestionTestSupport.Rules));

        Assert.Contains("ambiguous", error.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void IngestionFailsClosedWhenOneLedgerReceiptMatchesMultipleIncomingAtoms()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\n| κ | 1 |\n");
        var first = GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims[0];
        var ledger = new[] { LedgerEntry("gict-kappa", AtomizerRegistry.GictId, first) };

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(AtomizerRegistry.GictId, bytes, ledger, DigestionTestSupport.Rules));

        Assert.Contains("matches multiple incoming atoms", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestionFailsClosedForDuplicateResidualFingerprint()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\n| κ | 1 |\n");

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(
                AtomizerRegistry.GictId,
                bytes,
                Array.Empty<DigestionLedgerEntry>(),
                DigestionTestSupport.Rules));

        Assert.Contains("duplicate raw residual fingerprint", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestionFailsClosedForDuplicateNormalizedResidualFingerprint()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\r\n| κ | 1 |\n");
        var claims = GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims;
        Assert.Equal(2, claims.Length);
        Assert.NotEqual(claims[0].Fingerprints.RawSha256, claims[1].Fingerprints.RawSha256);
        Assert.Equal(claims[0].Fingerprints.NormalizedSha256, claims[1].Fingerprints.NormalizedSha256);

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(
                AtomizerRegistry.GictId,
                bytes,
                Array.Empty<DigestionLedgerEntry>(),
                DigestionTestSupport.Rules));

        Assert.Contains("duplicate normalized residual fingerprint", error.Message, StringComparison.Ordinal);
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
            Assert.False(string.IsNullOrWhiteSpace(atom.AstPath));
            Assert.True(atomIds.Add(atom.AstPath), $"duplicate atom id: {atom.AstPath}");
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
                (atom.AstPath, atom.StartByte, atom.EndByte, atom.Fingerprints)),
            second.Claims.Select(static atom =>
                (atom.AstPath, atom.StartByte, atom.EndByte, atom.Fingerprints)));
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
        string.Concat(CanonicalWmFixtureSegments().Select(static item => item.Text));

    private static string CanonicalWmV02Fixture()
    {
        var source = CanonicalWmFixture();
        source = source.Replace(
            "- **v0.1**(2026-07-18)首轮结账。\n",
            "- **v0.1**(2026-07-18)首轮结账。\n- **v0.2**(2026-07-23)勘误轮结账。\n",
            StringComparison.Ordinal);
        return source + "\n**v0.2 校核**(2026-07-23):追加校核,旧块不改。\n";
    }

    private static IReadOnlyList<(string AstPath, string Text)> CanonicalWmFixtureSegments()
    {
        var segments = new List<(string AstPath, string Text)>
        {
            (
                "metadata/preamble",
                WmTitle + "\n\n"
                + "**别名**:账本世界模型纲要\n"
                + "**定位**:经验姊妹卷\n\n"
                + "**版本账**(append-only):\n"),
            ("version/v0", "- **v0**(2026-07-18)立卷。\n"),
            ("version/v0.1", "- **v0.1**(2026-07-18)首轮结账。\n"),
            (
                "metadata/discipline",
                "\n" + WmDiscipline + "\n---\n\n"),
        };

        for (var section = 0; section <= 11; section++)
        {
            segments.Add(($"section/{section}", $"## {section}. Section {section}\n\nSection {section} claim.\n\n"));
            if (section == 7)
            {
                segments.Add(("section/7-appendix", WmAppendix));
            }
        }

        segments.Add((
            "audit",
            "## 校核记录(append-only,按版分块)\n\n"
            + "**v0 校核**(2026-07-18):立卷校核。\n\n"
            + "**v0.1 校核**(2026-07-18):首轮校核。\n\n"
            + WmCurrentTodoClosure + "\n"));
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

        Assert.Equal(
            ["remark/3.5/occurrence/1", "remark/3.5/occurrence/2"],
            document.Claims
                .Where(static atom => atom.AstPath.StartsWith("remark/3.5/", StringComparison.Ordinal))
                .Select(static atom => atom.AstPath));
        Assert.Equal(
            ["corollary/3.6/occurrence/1", "corollary/3.6/occurrence/2"],
            document.Claims
                .Where(static atom => atom.AstPath.StartsWith("corollary/3.6/", StringComparison.Ordinal))
                .Select(static atom => atom.AstPath));
        Assert.Equal(
            ["theorem/3.7/occurrence/1", "theorem/3.7/occurrence/2"],
            document.Claims
                .Where(static atom => atom.AstPath.StartsWith("theorem/3.7/", StringComparison.Ordinal))
                .Select(static atom => atom.AstPath));

        var repeatedRemarks = document.Claims
            .Where(static atom => atom.AstPath.StartsWith("remark/3.5/", StringComparison.Ordinal))
            .ToArray();
        var repeatedCorollaries = document.Claims
            .Where(static atom => atom.AstPath.StartsWith("corollary/3.6/", StringComparison.Ordinal))
            .ToArray();
        var incompatibleTheorems = document.Claims
            .Where(static atom => atom.AstPath.StartsWith("theorem/3.7/", StringComparison.Ordinal))
            .ToArray();
        Assert.Equal(repeatedRemarks[0].Fingerprints, repeatedRemarks[1].Fingerprints);
        Assert.Equal(repeatedCorollaries[0].Fingerprints, repeatedCorollaries[1].Fingerprints);
        Assert.NotEqual(incompatibleTheorems[0].Fingerprints, incompatibleTheorems[1].Fingerprints);
    }

    private static DigestionLedgerAlignment AlignUnregisteredGenres(byte[] bytes)
    {
        var ledger = BackfillInventoryLoader.Load(
            DigestionTestSupport.EmptyLedger(AtomizerRegistry.PzgId));
        return DigestionLedgerAligner.Evaluate(
            ledger,
            DigestionTestSupport.Snapshot(("docs/source.md", bytes)),
            ledger,
            DigestionAlignmentMode.Ingest);
    }
}
internal static class SyntheticNumberedAtomizer { internal static string Id => AtomizerRegistry.GictId; }
