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
                "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj::StrataLint.EngineeringScope.Program.Main(string[])",
                "tools/StrataLint.Scribe/StrataLint.Scribe.csproj::top-level:tools/StrataLint.Scribe/Program.cs",
            ],
            graph.ExecutableEntryPointDescriptions);
    }

    [Fact]
    public void HistoricalFreezeMatcherHasOneProductionOwnerAndAllSemanticConsumersUseIt()
    {
        var definitions = graph.MethodDefinitionsNamed("HistoricalActiveFreezeMatches");

        var definition = Assert.Single(definitions);
        Assert.StartsWith(
            "StrataLint.Engine.FrozenLedgerHistoricalFreezeMatcher.HistoricalActiveFreezeMatches(",
            definition,
            StringComparison.Ordinal);
        Assert.Equal(
            [
                "tools/StrataLint.Engine/Ledger/Admission/FrozenLedgerAdmission.cs",
                "tools/StrataLint.Engine/Ledger/FrozenLedgerCanonicalWriter.cs",
                "tools/StrataLint.Engine/Ledger/Validation/FrozenLedgerCandidateValidation.cs",
                "tools/StrataLint.Engine/Ledger/Validation/FrozenLedgerHistoryValidation.cs",
            ],
            graph.ProductionReferencePaths(definition));
    }
}
