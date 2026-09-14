namespace StrataLint.Tests;

public sealed class LeanCachePublishTests
{
    [Fact]
    public void ReleaseSeedsUsePartitionAndAtomicPublication() =>
        // This process runs the whole transport suite, including retention and concurrency.
        LeanSeedProcessContract.Run("TransportTests", TestBudgets.LongWorkflowProcessHangGuard);
}
