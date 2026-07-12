namespace StrataLint.ArchitectureTests;

public sealed class BannedApiConfigurationTests
{
    private const string AnalyzerVersion = "5.6.0";

    [Theory]
    [InlineData("StrataLint.Engine")]
    [InlineData("StrataLint.Scribe")]
    public void EngineAndScribeAttachThePinnedBannedApiAnalyzer(string projectName)
    {
        var root = RepositoryLayout.FindRoot();
        var projectDirectory = Path.Combine(root, "Meta", "StrataLint", projectName);

        Assert.Empty(BannedApiConfigurationPolicy.InspectProject(
            File.ReadAllText(Path.Combine(projectDirectory, projectName + ".csproj"))));
        Assert.Empty(BannedApiConfigurationPolicy.InspectLockFile(
            File.ReadAllText(Path.Combine(projectDirectory, "packages.lock.json")),
            AnalyzerVersion));
    }

    [Fact]
    public void AnalyzerVersionIsPinnedCentrally()
    {
        var path = Path.Combine(RepositoryLayout.FindRoot(), "Directory.Packages.props");

        Assert.Empty(BannedApiConfigurationPolicy.InspectCentralVersion(
            File.ReadAllText(path),
            AnalyzerVersion));
    }

    [Fact]
    public void MissingAnalyzerReferenceIsRejectedByTheRedFixture()
    {
        const string project = """
            <Project Sdk="Microsoft.NET.Sdk">
              <ItemGroup>
                <AdditionalFiles Include="../Architecture/BannedSymbols.txt" />
              </ItemGroup>
            </Project>
            """;

        Assert.Contains(
            BannedApiConfigurationPolicy.InspectProject(project),
            static finding => finding.Contains("PackageReference", StringComparison.Ordinal));
    }
}
