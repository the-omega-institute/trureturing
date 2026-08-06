using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    private const string ConeAtomizerId = "cone-v1";
    private static string ConeProductionSource => Path.Combine(
        "docs", "develop", "theory", "CONE_PROGRAM_FORMAL.md");

    [Fact]
    public void ConeV1ProductionFixtureReassemblesAll353LinesByteExactly()
    {
        var root = FindRepositoryRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, ConeProductionSource));

        var document = AtomizerRegistry.Atomize(
            ConeAtomizerId,
            bytes,
            DigestionTestSupport.Rules);

        Assert.Equal(47_929, bytes.Length);
        Assert.Equal(353, bytes.Count(static value => value == (byte)'\n'));
        Assert.Equal(67, document.Claims.Length);
        AssertRecognitionComplete(document, bytes);
        AssertSplitIdempotent(ConeAtomizerId, document);
    }

    [Fact]
    public void ConeV1UsesStableSemanticLocatorFingerprintAndChapterContext()
    {
        var root = FindRepositoryRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, ConeProductionSource));

        var atom = AtomizerRegistry.Atomize(
                ConeAtomizerId,
                bytes,
                DigestionTestSupport.Rules)
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
            AtomizerRegistry.Atomize(ConeAtomizerId, bytes, DigestionTestSupport.Rules));

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
            AtomizerRegistry.Atomize(ConeAtomizerId, bytes, DigestionTestSupport.Rules));

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
            AtomizerRegistry.Atomize(ConeAtomizerId, bytes, DigestionTestSupport.Rules));

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
            AtomizerRegistry.Atomize(ConeAtomizerId, bytes, DigestionTestSupport.Rules));

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
            ConeAtomizerId,
            bytes,
            DigestionTestSupport.Rules).Claims);

        Assert.Equal("theorem-form/4.6", atom.AstPath);
    }

    [Fact]
    public void ConeV1ProjectsOnlyExactProofGradesToFormalizableKinds()
    {
        var root = FindRepositoryRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, ConeProductionSource));
        var claims = AtomizerRegistry.Atomize(
            ConeAtomizerId,
            bytes,
            DigestionTestSupport.Rules).Claims;

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
