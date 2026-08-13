using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class ProjectSideBoundaryTests
{
    [Fact]
    public void RepositorySourceIncludesDoNotIncreaseTheSingleKnownCrossSideViolation()
    {
        var root = FindRepositoryRoot();
        var projects = GitIndexRepositoryFiles.Enumerate(root)
            .Where(static file => file.RelativePath.EndsWith(".csproj", StringComparison.Ordinal))
            .Select(file => new ProjectManifest(
                file.RelativePath,
                File.ReadAllText(file.FullPath)))
            .ToArray();

        var findings = ProjectSideBoundaryPolicy.Inspect(projects);
        var sourceViolations = findings
            .Where(static finding => finding.Kind == ProjectBoundaryViolation.SourceCrossesSide)
            .ToArray();
        var referenceViolations = findings
            .Where(static finding => finding.Kind == ProjectBoundaryViolation.ToolReferencesContent)
            .ToArray();

        Assert.True(
            sourceViolations.Length <= 1,
            "Source-item cross-side violations must decrease monotonically from the single known baseline.\n"
            + string.Join('\n', sourceViolations.Select(static finding => finding.Message)));
        Assert.Empty(referenceViolations);
    }

    [Fact]
    public void SourcePolicyRejectsAToolProjectCompilingContentAsARedFixture()
    {
        var findings = ProjectSideBoundaryPolicy.Inspect(
        [
            Manifest(
                "Meta/StrataLint/Tool/Tool.csproj",
                "<Compile Include=\"../../../Blueprint/**/*.scribe.cs\" />"),
        ]);

        var finding = Assert.Single(findings);
        Assert.Equal(ProjectBoundaryViolation.SourceCrossesSide, finding.Kind);
        Assert.Contains("Tool.csproj:3", finding.Message, StringComparison.Ordinal);
        Assert.Contains("../../../Blueprint/**/*.scribe.cs", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SourcePolicyNormalizesParentSegmentsBeforeJudgingSameSideIncludes()
    {
        var findings = ProjectSideBoundaryPolicy.Inspect(
        [
            Manifest(
                "Meta/StrataLint/Tool/Tool.csproj",
                "<AdditionalFiles Include=\"../Architecture/BannedSymbols*.txt\" />"),
        ]);

        Assert.Empty(findings);
    }

    [Fact]
    public void MonotoneSourceBaselineAcceptsZeroViolations()
    {
        var findings = ProjectSideBoundaryPolicy.Inspect(
        [
            Manifest(
                "Meta/StrataLint/Tool/Tool.csproj",
                "<Compile Include=\"Sources/**/*.cs\" />"),
        ]);

        Assert.Empty(findings);
        Assert.True(findings.Count(static finding =>
            finding.Kind == ProjectBoundaryViolation.SourceCrossesSide) <= 1);
    }

    [Fact]
    public void ProjectReferencePolicyAllowsOnlyContentToToolAcrossSides()
    {
        var allowed = ProjectSideBoundaryPolicy.Inspect(
        [
            Manifest(
                "Consumer/Consumer.csproj",
                "<ProjectReference Include=\"../Meta/StrataLint/Tool/Tool.csproj\" />"),
        ]);
        var rejected = ProjectSideBoundaryPolicy.Inspect(
        [
            Manifest(
                "Meta/StrataLint/Tool/Tool.csproj",
                "<ProjectReference Include=\"../../../Consumer/Consumer.csproj\" />"),
        ]);

        Assert.Empty(allowed);
        var finding = Assert.Single(rejected);
        Assert.Equal(ProjectBoundaryViolation.ToolReferencesContent, finding.Kind);
        Assert.Contains("../../../Consumer/Consumer.csproj", finding.Message, StringComparison.Ordinal);
    }

    private static ProjectManifest Manifest(string path, string item) => new(
        path,
        $"""
        <Project Sdk="Microsoft.NET.Sdk">
          <ItemGroup>
            {item}
          </ItemGroup>
        </Project>
        """);

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
