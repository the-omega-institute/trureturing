namespace StrataLint.ArchitectureTests;

public sealed class BannedApiConfigurationTests
{
    [Theory]
    [InlineData("StrataLint.Engine")]
    [InlineData("StrataLint.Scribe")]
    [InlineData("StrataLint.Cli")]
    public void ProductionProjectsAttachThePinnedBannedApiAnalyzer(string projectName)
    {
        var root = RepositoryLayout.FindRoot();
        var projectDirectory = Path.Combine(root, "Meta", "StrataLint", projectName);
        var analyzerVersion = BannedApiConfigurationPolicy.ReadCentralVersion(
            File.ReadAllText(Path.Combine(root, "Directory.Packages.props")));

        Assert.Empty(BannedApiConfigurationPolicy.InspectProject(
            File.ReadAllText(Path.Combine(projectDirectory, projectName + ".csproj"))));
        Assert.Empty(BannedApiConfigurationPolicy.InspectLockFile(
            File.ReadAllText(Path.Combine(projectDirectory, "packages.lock.json")),
            analyzerVersion));
    }

    [Theory]
    [InlineData("StrataLint.Engine")]
    [InlineData("StrataLint.Scribe")]
    [InlineData("StrataLint.Cli")]
    public void ProductionProjectsAttachTheAmbientRuntimeApiDenylist(string projectName)
    {
        var root = RepositoryLayout.FindRoot();
        var projectDirectory = Path.Combine(root, "Meta", "StrataLint", projectName);

        Assert.Empty(BannedApiConfigurationPolicy.InspectDeterminismProject(
            File.ReadAllText(Path.Combine(projectDirectory, projectName + ".csproj"))));
    }

    [Theory]
    [InlineData("StrataLint.Engine")]
    [InlineData("StrataLint.Scribe")]
    public void DeterministicProjectsAttachTheGuidCreationDenylist(string projectName)
    {
        var root = RepositoryLayout.FindRoot();
        var projectDirectory = Path.Combine(root, "Meta", "StrataLint", projectName);

        Assert.Empty(BannedApiConfigurationPolicy.InspectGuidProject(
            File.ReadAllText(Path.Combine(projectDirectory, projectName + ".csproj"))));
    }

    [Fact]
    public void AnalyzerVersionHasOneCentralDefinition()
    {
        var path = Path.Combine(RepositoryLayout.FindRoot(), "Directory.Packages.props");

        Assert.NotEmpty(BannedApiConfigurationPolicy.ReadCentralVersion(File.ReadAllText(path)));
    }

    [Fact]
    public void DuplicateAnalyzerVersionDefinitionIsRejectedByTheRedFixture()
    {
        const string props = """
            <Project><ItemGroup>
              <PackageVersion Include="Microsoft.CodeAnalysis.BannedApiAnalyzers" Version="1.2.3" />
              <PackageVersion Include="Microsoft.CodeAnalysis.BannedApiAnalyzers" Version="1.2.4" />
            </ItemGroup></Project>
            """;

        Assert.Throws<FormatException>(() =>
            BannedApiConfigurationPolicy.ReadCentralVersion(props));
    }

    [Fact]
    public void LockFileFrameworkKeyIsNotHardCoded()
    {
        const string lockFile = """
            {
              "dependencies": {
                "net99.0": {
                  "Microsoft.CodeAnalysis.BannedApiAnalyzers": {
                    "type": "Direct",
                    "requested": "[1.2.3, )",
                    "resolved": "1.2.3"
                  }
                }
              }
            }
            """;

        Assert.Empty(BannedApiConfigurationPolicy.InspectLockFile(lockFile, "1.2.3"));
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
