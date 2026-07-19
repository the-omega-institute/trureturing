using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class TheoryAtomizerTests
{
    private const string FirstProductionSource =
        "docs/develop/theory/GICT.md";
    private const string SecondProductionSource =
        "docs/develop/theory/PZG_BEDC.md";
    private const string ThirdProductionSource =
        "docs/develop/theory/OBSERVER-QUANTUM.md";

    public static TheoryData<string, string> ProductionTheorySources => new()
    {
        { FirstProductionSource, AtomizerRegistry.GictId },
        { SecondProductionSource, AtomizerRegistry.PzgId },
        { ThirdProductionSource, AtomizerRegistry.ObserverId },
    };

    [Fact]
    public void RegistryFailsClosedForAnUnknownAtomizerAndListsRegisteredIds()
    {
        const string unknown = "unregistered-v1";

        var error = Assert.Throws<FormatException>(() =>
            AtomizerRegistry.Atomize(unknown, Array.Empty<byte>()));

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

        var document = GictAtomizer.Atomize(bytes);
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

        var document = PzgAtomizer.Atomize(bytes);

        Assert.Equal(["theorem/26.3", "ledger/26.4"], document.Claims.Select(static item => item.AstPath));
        Assert.All(document.Claims, atom =>
            Assert.Equal(["PZG", "第二十六章 桥通道"], atom.Context.Select(static item => item.Text)));
        Assert.Equal(bytes, document.Reassemble().ToArray());
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

        var document = GictAtomizer.Atomize(bytes);

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

        var document = PzgAtomizer.Atomize(bytes);

        Assert.Equal(["open/O-5", "open/O-6"], document.Claims.Select(static item => item.AstPath));
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void ObserverAdapterRecognizesEveryProductionClaim()
    {
        var root = FindRepositoryRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, ThirdProductionSource));

        var document = AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes);

        AssertRecognitionComplete(document, bytes);
    }

    [Fact]
    public void ObserverV1RecognizesTheObserverQuantumRefreshDialect()
    {
        var bytes = Encoding.UTF8.GetBytes(
            """
            # Observer refresh

            本文主张的是:claim。

            **簿记条款(v2)**:claim。

            因果方向:claim。

            **(i) 相位对象。** claim。

            **(ii) 刚性定律。** claim。

            **(iii) 账本纪律。** claim。

            **语义地基(v2 一层重写)**:claim。

            **定理(观察者代数的典范形态)。** claim。

            **定理(有限窗口 = 素数量子寄存器,绕行限定版)。** claim。

            **定理(无经典答案表,收窄版)。** claim。

            **定理(叠加不违反经典刚性)。** claim。

            **定理(观察者度量与二型无穷远,v2 新增)。** claim。

            **定理(两族窗口二分法与黄金支,v3 新增)。** claim。

            **测量的完整理论只有两个动词。** claim。

            **遗忘是可审计的数学关系。** claim。

            **时间的连续性是统计的产物(热时间假设,诠释级)。** claim。

            **中心层(强制,无选择)。** claim。

            **指针基层(由记账规则选定)。** claim。

            **冗余层(集体记忆)。** claim。

            单配定理锁死 claim。

            **v4 补全:经典性的账本签名与两种命运。** claim。

            **Q1(为何有概率):推出。** claim。

            **Q2(为何恰是 $|\psi|^2$):条件推出(路线 B)。** claim。

            **Q3(为何单一结果):动力学谜化解,索引谜搬家。** claim。

            **Q4(概率何义)。** claim。

            **设置格(选问题)与记账格(选经典):判真。** claim。

            **距离-相位定律三代(v2 全谱)。** claim。

            **自由价目全表**:claim。

            **互补预算定理(v2 新增,自含四行证)。** claim。

            Wigner 之友、claim。

            "连续本不存在,连续是统计" claim。

            未具备者如实列出:claim。

            **已结案(附证书):** claim。

            **遗留(三类):** claim。

            **总判词:** claim。

            **§10.1 分层公共记忆中和原则**。claim。

            **§10.2 对数钟与通道谱(指针)**。claim。

            **§10.3 商余本体语义庭**。claim。

            **边界**。claim。
            """);

        var document = AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes);

        Assert.Equal(
            [
                "scope/kinematics-statistics",
                "scope/bookkeeping",
                "scope/forced-causal-direction",
                "premise/phase-object",
                "premise/rigidity",
                "premise/ledger-discipline",
                "premise/semantic-foundation",
                "theorem/observer-algebra",
                "theorem/finite-window-register",
                "theorem/no-classical-answer-table",
                "theorem/state-not-path",
                "theorem/observer-metric",
                "theorem/window-dichotomy",
                "measurement/conditioning",
                "measurement/forgetting",
                "measurement/statistical-time",
                "classical/center",
                "classical/pointer-basis",
                "classical/redundant-records",
                "classical/unique-record",
                "classical/ledger-signature",
                "probability/Q1",
                "probability/Q2",
                "probability/Q3",
                "probability/Q4",
                "freedom/settings-and-recording",
                "freedom/distance-phase",
                "freedom/price-list",
                "freedom/complementarity-budget",
                "observer/nested-facts",
                "physics/continuum-and-fields",
                "physics/open-geometry",
                "verdict/settled",
                "verdict/open",
                "verdict/final",
                "memory/public-neutralization",
                "memory/log-clock-channel-spectrum",
                "ontology/quotient-remainder",
                "ontology/boundary",
            ],
            document.Claims.Select(static item => item.AstPath));
        AssertRecognitionComplete(document, bytes);
    }

    [Fact]
    public void ObserverV1SplitIsByteExactAndIdempotent()
    {
        var root = FindRepositoryRoot();
        var sourceBytes = File.ReadAllBytes(Path.Combine(root, ThirdProductionSource));
        var document = ObserverAtomizer.Atomize(sourceBytes);

        AssertRecognitionComplete(document, sourceBytes);
        AssertSplitIdempotent(AtomizerRegistry.ObserverId, document);
    }

    [Fact]
    public void GictAdapterIdentifiesNumberedNotesAsClaims()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**注 2.5(Why five)**。claim。\n");

        var atom = Assert.Single(GictAtomizer.Atomize(bytes).Claims);

        Assert.Equal("note/2.5", atom.AstPath);
    }

    [Fact]
    public void GictAdapterRecognizesSurveyAndMapsKind()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**勘察 6.35(量子度量丛与谱三元组路标)**〔勘察〕。claim。\n");

        var atom = Assert.Single(GictAtomizer.Atomize(bytes).Claims);

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

        var document = GictAtomizer.Atomize(bytes);

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

        var document = PzgAtomizer.Atomize(bytes);

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

        var document = PzgAtomizer.Atomize(bytes);

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

        var document = GictAtomizer.Atomize(bytes);
        var error = Assert.Throws<FormatException>(() => document.ResolveClaim("theorem/7.15"));

        Assert.Contains("ambiguous", error.Message, StringComparison.OrdinalIgnoreCase);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void UnknownNumberedClaimKindIsClassifiedAsASourceFormatFailure()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# PZG\n\n**猜想 1.1(Unknown kind)**。claim。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() => PzgAtomizer.Atomize(bytes));

        Assert.Contains("unknown PZG numbered claim kind", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ObserverAdapterRejectsAnUnknownBoldClaimLead()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n## 11. New section\n\n**新判词。** claim。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes));

        Assert.Contains("unknown observer claim lead", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ObserverAdapterRejectsAnIndentedUnknownBoldClaimLead()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n   **新判词。** claim。\n\n"
            + "**定理(观察者代数的唯一形态)。** known。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes));

        Assert.Contains("unknown observer claim lead", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("**Q1(伪造标签):推出。** claim。")]
    [InlineData("**Q2(伪造标签):条件推出。** claim。")]
    [InlineData("**Q3(伪造标签):搬家。** claim。")]
    [InlineData("**Q4(伪造标签)。** claim。")]
    [InlineData("**已结案(伪造标签):** claim。")]
    [InlineData("**遗留(伪造标签):** claim。")]
    public void ObserverAdapterRejectsMalformedKnownPrefixBoldLead(string malformedLead)
    {
        var bytes = Encoding.UTF8.GetBytes(
            $"# Observer\n\n{malformedLead}\n\n"
            + "**定理(观察者代数的唯一形态)。** known。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes));

        Assert.Contains("unknown observer claim lead", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ObserverAdapterRejectsADuplicateClaimLocator()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# Observer\n\n"
            + "**定理(观察者代数的唯一形态)。** first。\n\n"
            + "**定理(观察者代数的唯一形态)。** second。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            AtomizerRegistry.Atomize(AtomizerRegistry.ObserverId, bytes));

        Assert.Contains("duplicate observer claim locator", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void GictIngestionSubtractsNormalizedMatchAndAdmitsSemanticRewriteAsResidual()
    {
        var oldBytes = Encoding.UTF8.GetBytes(
            "# GICT\r\n\r\n**定理 1.1(Test)**。claim。\r\n\r\n*证明*。done。\r\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes).Claims);
        var ledger = new[] { LedgerEntry("gict-old", AtomizerRegistry.GictId, oldAtom) };
        var lineEndingOnly = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。claim。\n\n*证明*。done。\n");

        var seen = TheoryIngestion.AdmitResidual(
            AtomizerRegistry.GictId,
            lineEndingOnly,
            ledger);

        var match = Assert.Single(seen.Seen);
        Assert.Equal("gict-old", match.LedgerAtomId);
        Assert.Equal(DigestionFingerprintMatch.Normalized, match.Match);
        Assert.Empty(seen.Residual);

        var rewritten = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。semantically rewritten claim。\n");
        var admitted = TheoryIngestion.AdmitResidual(
            AtomizerRegistry.GictId,
            rewritten,
            ledger);

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
        var oldAtom = Assert.Single(PzgAtomizer.Atomize(oldBytes).Claims);
        var ledger = new[] { LedgerEntry("pzg-old", AtomizerRegistry.PzgId, oldAtom) };

        var seen = TheoryIngestion.AdmitResidual(AtomizerRegistry.PzgId, oldBytes, ledger);
        var incoming = Encoding.UTF8.GetBytes(
            "# PZG\n\n**定理 1.2(New)**〔open〕。new claim。\n");
        var admitted = TheoryIngestion.AdmitResidual(AtomizerRegistry.PzgId, incoming, ledger);

        Assert.Equal(DigestionFingerprintMatch.Raw, Assert.Single(seen.Seen).Match);
        Assert.Empty(seen.Residual);
        Assert.Equal("theorem/1.2", Assert.Single(admitted.Residual).Atom.AstPath);
    }

    [Fact]
    public void IngestionFailsClosedWhenOneAtomMatchesMultipleLedgerReceipts()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**定理 1.1(Test)**。claim。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(bytes).Claims);
        var ledger = new[]
        {
            LedgerEntry("gict-first", AtomizerRegistry.GictId, atom),
            LedgerEntry("gict-second", AtomizerRegistry.GictId, atom),
        };

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(AtomizerRegistry.GictId, bytes, ledger));

        Assert.Contains("ambiguous", error.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void IngestionFailsClosedWhenOneLedgerReceiptMatchesMultipleIncomingAtoms()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\n| κ | 1 |\n");
        var first = GictAtomizer.Atomize(bytes).Claims[0];
        var ledger = new[] { LedgerEntry("gict-kappa", AtomizerRegistry.GictId, first) };

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(AtomizerRegistry.GictId, bytes, ledger));

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
                Array.Empty<DigestionLedgerEntry>()));

        Assert.Contains("duplicate raw residual fingerprint", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestionFailsClosedForDuplicateNormalizedResidualFingerprint()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n| 常数 | 值 |\n|---|---|\n| κ | 1 |\r\n| κ | 1 |\n");
        var claims = GictAtomizer.Atomize(bytes).Claims;
        Assert.Equal(2, claims.Length);
        Assert.NotEqual(claims[0].Fingerprints.RawSha256, claims[1].Fingerprints.RawSha256);
        Assert.Equal(claims[0].Fingerprints.NormalizedSha256, claims[1].Fingerprints.NormalizedSha256);

        var error = Assert.Throws<FormatException>(() =>
            TheoryIngestion.AdmitResidual(
                AtomizerRegistry.GictId,
                bytes,
                Array.Empty<DigestionLedgerEntry>()));

        Assert.Contains("duplicate normalized residual fingerprint", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [MemberData(nameof(ProductionTheorySources))]
    public void ProductionTheoryDocumentsSatisfyAtomizationProperties(
        string relativePath,
        string atomizerId)
    {
        var root = FindRepositoryRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, relativePath));

        var document = AtomizerRegistry.Atomize(atomizerId, bytes);

        AssertRecognitionComplete(document, bytes);
        AssertSplitIdempotent(atomizerId, document);
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
        AtomizedTheoryDocument first)
    {
        var reassembled = first.Reassemble();
        var second = AtomizerRegistry.Atomize(atomizerId, reassembled.AsSpan());

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

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "Meta", "BACKFILL.yaml")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }

    private static DigestionLedgerEntry LedgerEntry(
        string atomId,
        string atomizer,
        DigestionAtom atom) => new(
        atomizer,
        "docs/source.md",
        atomizer,
        atomId,
        atom.AstPath,
        new DigestionBoundary(atom.AstPath, atom.StartByte, atom.EndByte),
        atom.Fingerprints,
        [],
        new DigestionReceipts([], [], [], [], null),
        new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
        ReceiptSyntax: null,
        CasRef: atom.Fingerprints.RawSha256);
}
