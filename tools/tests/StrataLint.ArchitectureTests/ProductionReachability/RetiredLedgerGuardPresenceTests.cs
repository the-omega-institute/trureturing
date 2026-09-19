namespace StrataLint.ArchitectureTests;

public sealed class RetiredLedgerGuardPresenceTests
{
    [Fact]
    public void HistoricalFreezeMatcherOwnerGuardIsRegisteredAsFact()
    {
        const string guardMethodName =
            "HistoricalFreezeMatcherHasOneProductionOwnerAndAllSemanticConsumersUseIt";

        var guard = typeof(RetiredLedgerSurfaceTests).GetMethod(guardMethodName);

        Assert.NotNull(guard);
        Assert.True(guard!.IsDefined(typeof(FactAttribute), inherit: false));
    }
}
