using System.Xml.Linq;

namespace StrataLint.ArchitectureTests;

public sealed class DefinitionsLayerTests
{
    private const string DefinitionsRoot =
        "Meta/StrataLint/StrataLint.Definitions";

    public static TheoryData<string, string> CanonicalDataSources => new()
    {
        { "Catalog/AnchorCatalogDefinitions.cs", "StrataLint.Scribe/Catalog/AnchorCatalogDefinitions.cs" },
        { "Catalog/ExternalAnchorManifest.cs", "StrataLint.Scribe/Catalog/ExternalAnchorManifest.cs" },
        { "Values/ValuesDefinitions.cs", "StrataLint.Scribe/Values/ValuesDefinitions.cs" },
        { "Golden/GoldenCorpus.cs", "StrataLint.Tests/Golden/GoldenCorpus.cs" },
        { "Golden/TomlGoldenLoader.cs", "StrataLint.Tests/Golden/TomlGoldenLoader.cs" },
        { "Golden/TomlGoldenWriter.cs", "StrataLint.Tests/Golden/TomlGoldenWriter.cs" },
    };

    [Fact]
    public void DefinitionsProjectDependsOnlyOnThePlatformAndTomlyn()
    {
        var projectPath = Path.Combine(
            RepositoryLayout.FindRoot(),
            DefinitionsRoot,
            "StrataLint.Definitions.csproj");
        Assert.True(File.Exists(projectPath), $"Definitions project is missing: {projectPath}");
        var project = XDocument.Load(projectPath);

        var references = project.Descendants()
            .Where(static element => element.Name.LocalName is
                "ProjectReference" or "PackageReference" or "Reference")
            .Select(static element => element.Attribute("Include")?.Value ?? element.Value)
            .ToArray();

        Assert.Equal(["Tomlyn"], references);
    }

    [Theory]
    [MemberData(nameof(CanonicalDataSources))]
    public void CanonicalDataSourceIsOwnedOnlyByDefinitions(
        string definitionsPath,
        string legacyPath)
    {
        var root = RepositoryLayout.FindRoot();

        Assert.True(File.Exists(Path.Combine(root, DefinitionsRoot, definitionsPath)));
        Assert.False(File.Exists(Path.Combine(root, "Meta/StrataLint", legacyPath)));
    }

    [Theory]
    [InlineData("CphiKernel")]
    [InlineData("FullPeriodWindowAverager")]
    [InlineData("NeumaierSum")]
    [InlineData("ValuesEvaluator")]
    public void DefinitionsDoesNotOwnScribeProgramTypes(string typeName)
    {
        var root = Path.Combine(RepositoryLayout.FindRoot(), DefinitionsRoot);
        Assert.True(Directory.Exists(root), $"Definitions directory is missing: {root}");
        var sources = Directory.EnumerateFiles(root, "*.cs", SearchOption.AllDirectories)
            .Select(File.ReadAllText);

        Assert.DoesNotContain(sources, source =>
            source.Contains($"class {typeName}", StringComparison.Ordinal));
    }
}
