namespace StrataLint.ArchitectureTests;

public sealed class NamespaceLayoutTests
{
    [Fact]
    public void MetaAndBlueprintSourcesFollowTheV2NamespaceConvention()
    {
        Assert.Empty(NamespacePolicy.InspectRepository(RepositoryLayout.FindRoot()));
    }

    [Fact]
    public void BucketNamespaceIsRejectedByTheFlatNamespaceRedFixture()
    {
        var finding = Assert.Single(NamespacePolicy.Check(
            "Meta/StrataLint/StrataLint.Engine/Coordinates/Leak.cs",
            "StrataLint.Engine",
            "namespace StrataLint.Engine.Coordinates;\n"));

        Assert.Contains("does not match", finding.Message, StringComparison.Ordinal);
    }
}
