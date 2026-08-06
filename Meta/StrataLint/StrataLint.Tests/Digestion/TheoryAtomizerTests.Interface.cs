using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    [Fact]
    public void InterfacePaperDialectExhaustsNumberedClaimsWithStableKindsAndFingerprints()
    {
        var root = FindRepositoryRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, FourthProductionSource));

        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.PzgId,
            bytes,
            DigestionTestSupport.Rules);

        Assert.Equal(37, document.Claims.Length);
        Assert.Equal(
            [
                ("corollary", 2),
                ("definition", 5),
                ("example", 1),
                ("lemma", 2),
                ("observation", 3),
                ("proposition", 3),
                ("remark", 8),
                ("theorem", 13),
            ],
            document.Claims
                .GroupBy(static atom => atom.AstPath.Split('/')[0], StringComparer.Ordinal)
                .Select(static group => (Kind: group.Key, Count: group.Count()))
                .OrderBy(static item => item.Kind, StringComparer.Ordinal));

        var landing = document.ResolveClaim("lemma/3.1");
        var escape = document.ResolveClaim("theorem/3.4");
        Assert.Equal(
            "sha256:9d52e41b062f81b1ce93cf241bf4ef9806f6e6de3fe9d6d10b5dc2de6d1f929a",
            landing.Fingerprints.RawSha256);
        Assert.Equal(
            "sha256:c0a63f4cbbe848e456ae1f847150de6bf63e59a5295bf711230af4bbb4860cab",
            escape.Fingerprints.RawSha256);
        Assert.Contains("*证明。*", Encoding.UTF8.GetString(landing.RawBytes.AsSpan()), StringComparison.Ordinal);
        Assert.Contains("*证明。*", Encoding.UTF8.GetString(escape.RawBytes.AsSpan()), StringComparison.Ordinal);
        Assert.DoesNotContain("隐藏独立性", Encoding.UTF8.GetString(escape.RawBytes.AsSpan()), StringComparison.Ordinal);
    }

    [Fact]
    public void InterfacePaperDialectPreservesDuplicateBlocksAsDistinctOccurrences()
    {
        var root = FindRepositoryRoot();
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
}
