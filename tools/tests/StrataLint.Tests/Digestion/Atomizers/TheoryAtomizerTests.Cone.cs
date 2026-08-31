using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
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
    public void ConeV1RecordsAnUnregisteredNumberedClaimGenre()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**猜想 3.6(未登记标题)[证]。**claim。\n");

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.ConeId,
            bytes,
            ConeRules);

        AssertContentIdentity(Assert.Single(document.Claims));
        Assert.Equal(["猜想"], document.UnregisteredGenres.ToArray());
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

        Assert.Contains("has chapter mismatch", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ConeV1KeepsContentDistinctRepeatedClaimLeads()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "# 正锥纲领:形式化定理与证明\n\n"
            + "## 第三章 路径散度理论\n\n"
            + "**引理 3.6(反演恒等式)[证]。**first。\n\n"
            + "**引理 3.6(反演恒等式)[证]。**second。\n");

        var document = AtomizerRegistry.Atomize(AtomizerRegistry.ConeId, bytes, ConeRules);

        AssertContentIdentities(document, 2);
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

        AssertContentIdentity(atom);
    }

}
