using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    public static TheoryData<string, string, bool> SyntheticVolumeFixtures => new()
    {
        {
            AtomizerRegistry.GictId,
            "# GICT\n\n## VII.7 Interface\n\n**定理 7.15(G axis)**〔定理·证〕。Claim.\n\n*证明*。Done.\n",
            false
        },
        {
            AtomizerRegistry.ConeId,
            "# 正锥纲领:形式化定理与证明\n\n## 第三章 路径散度理论\n\n**引理 3.6(反演恒等式)[证]。**Claim.\n",
            true
        },
        {
            AtomizerRegistry.ObserverId,
            "# Observer\n\n## Synthetic\n\n**定理(叠加不违反经典刚性)。** Claim.\n\n---\n",
            false
        },
    };

    [Theory]
    [MemberData(nameof(SyntheticVolumeFixtures))]
    public void SyntheticVolumeSplitIsByteExactAndIdempotent(
        string atomizerId,
        string source,
        bool useConeRules)
    {
        var bytes = Encoding.UTF8.GetBytes(source);
        var rules = useConeRules ? ConeRules : DigestionTestSupport.Rules;
        var document = AtomizerRegistry.Atomize(atomizerId, bytes, rules);

        AssertRecognitionComplete(document, bytes);
        AssertSplitIdempotent(atomizerId, document, rules);
        foreach (var claim in document.Claims)
        {
            var captured = DigestionCasStore.Capture(claim.RawBytes.AsSpan());
            var frozen = DigestionAtom.FromFrozenCas(captured.Bytes);

            Assert.Equal(claim.Fingerprints.RawSha256, captured.Reference);
            Assert.Equal(claim.RawBytes.ToArray(), frozen.RawBytes.ToArray());
            Assert.Equal(claim.Fingerprints, frozen.Fingerprints);
        }
    }

    [Fact]
    public void FrozenCasAtomUsesSyntheticBytesAndContentAddress()
    {
        var bytes = Encoding.UTF8.GetBytes("synthetic frozen CAS bytes\n");
        var captured = DigestionCasStore.Capture(bytes);

        var atom = DigestionAtom.FromFrozenCas(captured.Bytes);

        Assert.Equal(
            "sha256:b323429784e6d290c89805f54a458bec3f2aa0d7185c7009e447287e013eb495",
            captured.Reference);
        Assert.Equal(bytes, atom.RawBytes.ToArray());
        Assert.Equal(bytes.Length, atom.EndByte);
        Assert.Equal(DigestionFingerprint.Compute(bytes), atom.Fingerprints);
    }
}
