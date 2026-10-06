namespace StrataLint.Tests;

public sealed class DepositScopeRejectProbe
{
    [Fact]
    public void InstalledDepositHeaderRejectsMissingSelectedAtomWithoutDigestionLedger()
    {
        new DepositHeaderUtilityTests().MissingUtilityAtomIsDanglingWhenThereIsNoDigestionLedger();
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InstalledAtomUtilityRejectsMissingOrMalformedTargetSourceMetadata(bool malformed)
    {
        new UtilityAdmissionObservationTests().AtomUtilityRequiresValidTargetSourceMetadata(malformed);
    }
}
