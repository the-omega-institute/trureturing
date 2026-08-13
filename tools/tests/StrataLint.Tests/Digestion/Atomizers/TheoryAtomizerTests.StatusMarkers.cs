using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    [Theory]
    [InlineData("〔定理·证 + 证书〕")]
    [InlineData("〔closed·数值(五仪终审)+ 解析证明待办;v3.7 改版〕")]
    public void GictAnnotationsDoNotClaimTheCanonicalClosedStatusNamespace(string annotation)
    {
        var bytes = Encoding.UTF8.GetBytes($"# GICT\n\n**定理 7.12**{annotation}。陈述。\n");

        var atom = Assert.Single(GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);

        Assert.Equal(DigestionAtomStatusMarkerKind.Absent, atom.StatusMarker.Kind);
        Assert.Null(atom.StatusMarker.Status);
        Assert.Null(atom.StatusMarker.Qualifier);
    }

    [Fact]
    public void ProductionGictAnnotationsDoNotContainMalformedClosedStatusMarkers()
    {
        var root = TestRepositoryLayout.FindRoot();
        var bytes = File.ReadAllBytes(Path.Combine(root, FirstProductionSource));

        var document = GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules);

        Assert.DoesNotContain(
            document.Claims,
            static atom => atom.StatusMarker.Kind == DigestionAtomStatusMarkerKind.Malformed);
    }
}
