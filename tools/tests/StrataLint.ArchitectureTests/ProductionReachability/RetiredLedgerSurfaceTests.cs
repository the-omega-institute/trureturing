namespace StrataLint.ArchitectureTests;

public sealed class RetiredLedgerSurfaceTests(
    RetiredLedgerSurfaceTests.ProductionGraphFixture fixture)
    : IClassFixture<RetiredLedgerSurfaceTests.ProductionGraphFixture>
{
    private readonly ProductionSourceGraph graph = fixture.Graph;

    public sealed class ProductionGraphFixture
    {
        internal ProductionSourceGraph Graph { get; } =
            ProductionSourceGraph.Create(RepositoryLayout.FindRoot());
    }

    [Fact]
    public void TrackedDotnetExecutableEntryPointsAreEnumerated()
    {
        Assert.Equal(
            [
                "tools/StrataLint.Cli/StrataLint.Cli.csproj::StrataLint.Cli.Program.Main(string[])",
                "tools/StrataLint.FileMap/StrataLint.FileMap.csproj::StrataLint.FileMap.FileMapProgram.Main(string[])",
                "tools/StrataLint.Lean/StrataLint.Lean.csproj::StrataLint.EngineeringScope.LeanProgram.Main(string[])",
                "tools/StrataLint.Scribe/StrataLint.Scribe.csproj::StrataLint.Scribe.ScribeProgram.Main(string[])",
                "tools/StrataLint.TestEvidence/StrataLint.TestEvidence.csproj::StrataLint.TestEvidence.Program.Main(string[])",
            ],
            graph.ExecutableEntryPointDescriptions);
    }

}
