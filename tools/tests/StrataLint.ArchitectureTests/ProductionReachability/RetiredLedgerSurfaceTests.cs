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
    public void CliCommandTableContainsNoRetiredLedgerWriteVerb()
    {
        Assert.DoesNotContain("ledger-reattest", StrataLint.Cli.CliApplication.ImplementedCommands);
        Assert.DoesNotContain("ledger-sync", StrataLint.Cli.CliApplication.ImplementedCommands);
        Assert.DoesNotContain("ledger-supersede", StrataLint.Cli.CliApplication.ImplementedCommands);
    }

    [Fact]
    public void TrackedDotnetExecutableRootsHaveNoStaticallyBoundPathToRetiredLedgerWriteProtocols()
    {
        Assert.Equal(
            [
                "tools/StrataLint.Cli/StrataLint.Cli.csproj::StrataLint.Cli.Program.Main(string[])",
                "tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj::StrataLint.EngineeringScope.Program.Main(string[])",
                "tools/StrataLint.Scribe/StrataLint.Scribe.csproj::top-level:tools/StrataLint.Scribe/Program.cs",
            ],
            graph.ExecutableEntryPointDescriptions);

        // This is a conservative static C# graph: calls, construction, delegates, initializers,
        // and interface/virtual dispatch are covered. Reflection, dynamic/native invocation and
        // arbitrary shell behavior are outside the claim made by this test.
        var reachable = graph.ReachableFromExecutableEntryPoints();
        var forbidden = reachable
            .Where(static symbol => symbol is
                "StrataLint.Cli.DagLedgerLoader.ToLinearSyntax(System.Collections.Immutable.ImmutableArray<StrataLint.Engine.DagLedgerFileEvent>)"
                or "StrataLint.Engine.FrozenLedgerCanonicalWriter.WriteEvent(string, System.Text.Json.JsonElement, string, int)"
                or "StrataLint.Engine.FrozenLedgerCanonicalWriter.WriteReplayEnvelope(string, System.Text.Json.JsonElement, string, int)"
                or "StrataLint.Engine.FrozenLedgerCanonicalWriter.ReplayEnvelope(string, System.Text.Json.JsonElement, string, int, string?)"
                or "StrataLint.Cli.DagLedgerReattestWriter"
                or "StrataLint.Cli.DagLedgerSyncWriter"
                or "StrataLint.Cli.DagLedgerSupersedeWriter"
                or "StrataLint.Engine.FrozenLedgerLineSyntax"
                or "StrataLint.Engine.FrozenLedgerSyntax")
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Empty(forbidden);
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
