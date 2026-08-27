namespace StrataLint.ArchitectureTests;

public sealed class RetiredLedgerSurfaceTests
{
    [Fact]
    public void CliCommandTableContainsNoRetiredLedgerWriteVerb()
    {
        Assert.DoesNotContain("ledger-reattest", StrataLint.Cli.CliApplication.ImplementedCommands);
        Assert.DoesNotContain("ledger-sync", StrataLint.Cli.CliApplication.ImplementedCommands);
        Assert.DoesNotContain("ledger-supersede", StrataLint.Cli.CliApplication.ImplementedCommands);
    }

    [Fact]
    public void CliEntryPointCannotReachV1ReplayOrRetiredLedgerWriteProtocol()
    {
        var graph = ProductionSourceGraph.Create(RepositoryLayout.FindRoot());
        var reachable = graph.ReachableFrom("StrataLint.Cli.Program.Main(string[])");
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
        var graph = ProductionSourceGraph.Create(RepositoryLayout.FindRoot());
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
