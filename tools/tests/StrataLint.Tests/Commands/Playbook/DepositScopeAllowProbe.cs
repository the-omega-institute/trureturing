namespace StrataLint.Tests;

public sealed class DepositScopeAllowProbe
{
    [Theory]
    [InlineData("none")]
    [InlineData("atom")]
    [InlineData("task")]
    public void InstalledDepositHeaderUsesOnlyProtectedTargetPolicyAndRequestedUtility(string kind)
    {
        new DepositHeaderUtilityTests().DepositReadsOnlyRelevantLeanPolicyBaselineAndUtilityTarget(kind);
    }

    [Theory]
    [InlineData("Meta/Digestion/backfill/fixture-source/partial-open/0000000000000000000000000000000000000000000000000000000000000000.yaml")]
    [InlineData("Meta/Digestion/backfill/unrelated-source/partial-open/0000000000000000000000000000000000000000000000000000000000000000.yaml")]
    [InlineData("Meta/Digestion/backfill/unrelated-source/source.toml")]
    public void InstalledAtomUtilityIgnoresMalformedUnrelatedLedgerInput(string unrelatedPath)
    {
        new UtilityAdmissionObservationTests().AtomUtilityIgnoresMalformedUnrelatedLedgerInput(unrelatedPath);
    }
}
