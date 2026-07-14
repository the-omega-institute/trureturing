namespace StrataLint.ArchitectureTests;

public sealed class DefinitionsLayerTests
{
    private const string DefinitionsRoot = "Meta/StrataLint/StrataLint.Definitions";

    [Fact]
    public void CanonicalValuesAndAnchorInstancesLiveOutsideProgramDirectories()
    {
        var root = RepositoryLayout.FindRoot();

        Assert.True(File.Exists(Path.Combine(
            root,
            "Meta",
            "StrataLint",
            "Golden",
            "values-kernels.toml")));
        Assert.True(File.Exists(Path.Combine(
            root,
            "Meta",
            "StrataLint",
            "Golden",
            "external-anchors.toml")));
    }

    [Fact]
    public void DefinitionsAssemblyIsRetiredAfterCanonicalDataMovesOutsideProgramDirectories()
    {
        var root = RepositoryLayout.FindRoot();
        var definitionsProject = Path.Combine(root, DefinitionsRoot, "StrataLint.Definitions.csproj");
        var solution = File.ReadAllText(Path.Combine(root, "Meta", "StrataLint", "StrataLint.sln"));

        Assert.False(File.Exists(definitionsProject), $"Retired assembly remains: {definitionsProject}");
        Assert.DoesNotContain("StrataLint.Definitions", solution, StringComparison.Ordinal);
    }
}
