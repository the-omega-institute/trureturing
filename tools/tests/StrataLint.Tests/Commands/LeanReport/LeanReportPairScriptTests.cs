namespace StrataLint.Tests;

public sealed class LeanReportPairScriptTests
{
    [Fact]
    public void TransportedBundleIsOnlyAnIncrementalSeed() =>
        LeanSeedProcessContract.Run("PairTests.test_transport_adapter_preserves_seed_identity_and_omits_logs");
}
