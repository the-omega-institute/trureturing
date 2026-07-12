using StrataLint.Engine;

namespace StrataLint.ArchitectureTests;

public sealed class CSharpArchitectureTowerTests
{
    [Fact]
    public void TowerRegistersTheCSharpArchitectureEnforcementChain()
    {
        var path = Path.Combine(
            RepositoryLayout.FindRoot(),
            "Meta",
            "StrataLint",
            "TOWER.yaml");
        var loaded = Assert.IsType<TowerManifestParseOutcome.Loaded>(
            TowerManifestParser.Parse(File.ReadAllBytes(path)));
        var component = Assert.Single(
            loaded.Syntax.Components,
            static item => item.Id == "csharp-architecture");

        Assert.Equal(
            ["architecture-tests", "banned-api-analyzers", "engineering-ci"],
            component.JudgedBy.ToArray());
        Assert.Equal("verified", component.Verification);
    }
}
