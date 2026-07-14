namespace StrataLint.ArchitectureTests;

public sealed class TargetFrameworkSingleSourceTests
{
    private const string EngineLockPath =
        "Meta/StrataLint/StrataLint.Engine/packages.lock.json";
    private const string BannedApiConfigurationFixturePath =
        "Meta/StrataLint/StrataLint.ArchitectureTests/Determinism/BannedApiConfigurationTests.cs";

    [Fact]
    public void RepositoryReadsTargetFrameworkFromMsbuild()
    {
        var findings = TargetFrameworkSingleSourcePolicy.InspectRepository(
            RepositoryLayout.FindRoot());

        Assert.True(
            findings.Count == 0,
            string.Join(
                Environment.NewLine,
                findings.Select(static finding => $"{finding.Path}: {finding.Message}")));
    }

    [Fact]
    public void CopiedTargetFrameworkIsRejectedByTheRedFixture()
    {
        var source = "DLL_REL=bin/Release/net" + "99.0/StrataLint.dll";

        var finding = Assert.Single(TargetFrameworkSingleSourcePolicy.InspectText(
            ".github/scripts/synthetic.sh",
            source));

        Assert.Contains("MSBuild", finding.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("Directory.Build.props")]
    [InlineData(EngineLockPath)]
    [InlineData(BannedApiConfigurationFixturePath)]
    public void CanonicalOwnerAndGeneratedOrSyntheticFixturesAreAllowed(string path)
    {
        Assert.Empty(TargetFrameworkSingleSourcePolicy.InspectText(path, "net" + "99.0"));
    }
}
