using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MakeCoverRejectsMissingArgumentsBeforeProducingLeanReport(bool includeAtomId)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();

        var result = fixture.RunMakeCover(includeAtomId);

        Assert.NotEqual(0, result.ExitCode);
        Assert.DoesNotContain("make:lean-report", fixture.CallKinds());
        Assert.False(fixture.LeanReportExists());
    }

}
