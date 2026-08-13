using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    private static string ConeProductionSource => Path.Combine(
        "docs", "develop", "theory", "CONE_PROGRAM_FORMAL.md");
    private static readonly TheoryAtomizerRules ConeRules = TheoryAtomizerDataLoader.Load(
        DigestionTestSupport.Snapshot((
            TheoryAtomizerDataLoader.DataPath,
            Encoding.UTF8.GetBytes("""
                schema_version = 1

                [[observer.claim_prefixes]]
                prefix = "**Known**"
                locator = "theorem/known"

                [[cone.claim_prefixes]]
                prefix = "定理"
                locator = "theorem/{number}|theorem-form/{number}"
                [[cone.claim_prefixes]]
                prefix = "引理"
                locator = "lemma/{number}|theorem-form/{number}"
                [[cone.claim_prefixes]]
                prefix = "系"
                locator = "corollary/{number}|theorem-form/{number}"
                [[cone.claim_prefixes]]
                prefix = "定义"
                locator = "definition/{number}"
                [[cone.claim_prefixes]]
                prefix = "注"
                locator = "note/{number}"
                [[cone.claim_prefixes]]
                prefix = "约定"
                locator = "specification/{number}"
                [[cone.claim_prefixes]]
                prefix = "命题|数值定理"
                locator = "theorem-form/{number}"
                [[cone.claim_prefixes]]
                prefix = "结构|发现"
                locator = "observation/{number}"
                [[cone.claim_prefixes]]
                prefix = "目"
                locator = "frontier-note/{number}"
                [[cone.claim_prefixes]]
                prefix = "版图"
                locator = "extension-table/{number}"
                [[cone.claim_prefixes]]
                prefix = "定律"
                locator = "principle/{number}"

                [[gict.genres]]
                token = "定理"
                kind = "theorem"

                [[gict.claim_prefixes]]
                prefix = "**Heart**"
                locator = "open/heart"

                [[gict.constants]]
                name = "κ"
                locator = "constant/kappa"

                [[pzg.genres]]
                token = "定理"
                kind = "theorem"

                [[pzg.markers]]
                role = "trace-note"
                text = "追注"

                [[pzg.heading_prefixes]]
                prefix = "判负册"
                locator = "negative-register/batch"

                [[wm.headings]]
                role = "title"
                text = "Synthetic WM"
                [[wm.headings]]
                role = "appendix"
                text = "Synthetic appendix"
                [[wm.headings]]
                role = "audit"
                text = "Synthetic audit"
                """))));

    [Fact]
    public void ConeV1ProductionFixtureReassemblesAll353LinesByteExactly()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, ConeProductionSource));

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.ConeId,
            bytes,
            ConeRules);

        Assert.Equal(47_929, bytes.Length);
        Assert.Equal(353, bytes.Count(static value => value == (byte)'\n'));
        Assert.Equal(67, document.Claims.Length);
        AssertRecognitionComplete(document, bytes);
        AssertSplitIdempotent(AtomizerRegistry.ConeId, document, ConeRules);
    }

    [Fact]
    public void ConeV1UsesStableSemanticLocatorFingerprintAndChapterContext()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, ConeProductionSource));

        var atom = AtomizerRegistry.Atomize(
                AtomizerRegistry.ConeId,
                bytes,
                ConeRules)
            .ResolveClaim("lemma/3.6");

        Assert.Equal(
            "sha256:d6d0ea477f01d992336c74fbcb8984a5fb9386f4a4547c6327713131a3e4dbd1",
            atom.Fingerprints.RawSha256);
        Assert.Equal(atom.Fingerprints.RawSha256, atom.Fingerprints.NormalizedSha256);
        Assert.Equal(
            ["正锥纲领:形式化定理与证明", "第三章 路径散度理论"],
            atom.Context.Select(static item => item.Text));
        Assert.Equal([1, 2], atom.Context.Select(static item => item.Level));
    }

    [Fact]
    public void ConeV1RejectsAnUnknownNumberedClaimTitle()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**猜想 3.6(未登记标题)[证]。**claim。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            AtomizerRegistry.Atomize(AtomizerRegistry.ConeId, bytes, ConeRules));

        Assert.Contains("unknown cone numbered claim title", error.Message, StringComparison.Ordinal);
        Assert.Contains("line 5", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ConeV1RejectsAMalformedNumberedClaimTitle()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第四章 收缩谱\n\n"
            + "**定理4.6(KM 渐近律)[证]。**claim。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            AtomizerRegistry.Atomize(AtomizerRegistry.ConeId, bytes, ConeRules));

        Assert.Contains("unknown cone numbered claim title", error.Message, StringComparison.Ordinal);
        Assert.Contains("line 5", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ConeV1RejectsAClaimOutsideItsNumberedChapter()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第四章 收缩谱\n\n"
            + "**引理 3.6(反演恒等式)[证]。**claim。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            AtomizerRegistry.Atomize(AtomizerRegistry.ConeId, bytes, ConeRules));

        Assert.Contains("cone claim chapter mismatch", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ConeV1RejectsADuplicateClaimLocator()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**引理 3.6(反演恒等式)[证]。**first。\n\n"
            + "**引理 3.6(反演恒等式)[证]。**second。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            AtomizerRegistry.Atomize(AtomizerRegistry.ConeId, bytes, ConeRules));

        Assert.Contains("duplicate cone claim locator", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ConeV1DoesNotFormalizeACompositeGradeContainingProofToken()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第四章 收缩谱\n\n"
            + "**定理 4.6(KM 渐近律)[数][证]。**claim。\n");

        var atom = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.ConeId,
            bytes,
            ConeRules).Claims);

        Assert.Equal("theorem-form/4.6", atom.AstPath);
    }

    [Fact]
    public void ConeV1ProjectsOnlyExactProofGradesToFormalizableKinds()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, ConeProductionSource));
        var claims = AtomizerRegistry.Atomize(
            AtomizerRegistry.ConeId,
            bytes,
            ConeRules).Claims;

        Assert.Contains(claims, static atom => atom.AstPath == "theorem/3.7");
        Assert.Contains(claims, static atom => atom.AstPath == "lemma/3.6");
        Assert.Contains(claims, static atom => atom.AstPath == "corollary/3.4");
        Assert.Contains(claims, static atom => atom.AstPath == "theorem-form/4.6");
        Assert.Contains(claims, static atom => atom.AstPath == "theorem-form/6.2");
        Assert.Contains(claims, static atom => atom.AstPath == "theorem-form/8.2");
        Assert.Contains(claims, static atom => atom.AstPath == "theorem-form/10.2");
        Assert.Contains(claims, static atom => atom.AstPath == "theorem-form/11.3");
        Assert.Contains(claims, static atom => atom.AstPath == "extension-table/11.6");
        Assert.Contains(claims, static atom => atom.AstPath == "frontier-note/8.7");

        Assert.All(claims, atom =>
        {
            var text = Encoding.UTF8.GetString(atom.RawBytes.AsSpan());
            var titleEnd = text.IndexOf("**", 2, StringComparison.Ordinal);
            Assert.True(titleEnd > 2, $"claim has no closed bold title: {atom.AstPath}");
            var title = text[..(titleEnd + 2)];
            var exactProofGrade = title.EndsWith("[证]。**", StringComparison.Ordinal);
            var formalizableKind = atom.AstPath[..atom.AstPath.IndexOf('/', StringComparison.Ordinal)]
                is "theorem" or "lemma" or "corollary";

            Assert.Equal(exactProofGrade, formalizableKind);
        });

        Assert.DoesNotContain(
            claims,
            static atom => atom.AstPath.StartsWith("method/", StringComparison.Ordinal));
    }
}
