using System.Text;
using StrataLint.Engine;

namespace StrataLint.Digestion.Tests;

public sealed class DigestionContentKindTests
{
    [Theory]
    [InlineData("## 定理 364.1（内容地址）\n\n陈述。\n", "定理")]
    [InlineData("**proposition 6.30**. Claim.\n", "proposition")]
    public void GenericAtomizerDerivesClaimKindFromContent(string markdown, string expectedKind)
    {
        var bytes = Encoding.UTF8.GetBytes(markdown);
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            bytes).Claims);

        var kinds = AtomizerRegistry.ResolveContentKinds(
            AtomizerRegistry.GenericId,
            bytes);

        Assert.Equal(expectedKind, kinds[atom.Fingerprints.RawSha256]);
    }

    [Fact]
    public void GenericAtomizerDerivesTableSectionKindFromContent()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "## Dictionary\n\n| key | value |\n| --- | --- |\n| M(S) | residual escape mass |\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            bytes).Claims);

        var kinds = AtomizerRegistry.ResolveContentKinds(
            AtomizerRegistry.GenericId,
            bytes);

        Assert.Equal("section", kinds[atom.Fingerprints.RawSha256]);
    }

    [Fact]
    public void ClauseAtomsInheritTheirParentsContentDerivedKind()
    {
        var bytes = Encoding.UTF8.GetBytes(
            "**定理 6.62**。主张。\n\n**独立补充**。第二子句。\n");
        var document = AtomizerRegistry.Atomize(
            AtomizerRegistry.GenericId,
            bytes);
        var plan = Assert.Single(document.ClausePlans);

        var kinds = AtomizerRegistry.ResolveContentKinds(
            AtomizerRegistry.GenericId,
            bytes);

        Assert.Equal("定理", kinds[plan.Parent.Fingerprints.RawSha256]);
        Assert.All(
            plan.Children,
            child => Assert.Equal("定理", kinds[child.Fingerprints.RawSha256]));
    }
}
