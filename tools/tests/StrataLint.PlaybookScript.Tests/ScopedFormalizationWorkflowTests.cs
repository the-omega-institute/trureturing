using static StrataLint.TestSupport.TransactionFixture;

namespace StrataLint.PlaybookScript.Tests;

public sealed class ScopedFormalizationWorkflowTests
{
    [Theory]
    [InlineData("deposit")]
    [InlineData("deposit-uncovered")]
    public void CrossClosureScribeEmissionPreservesTheFreezeReport(string command)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run(command, atomId: null,
            crossScribeScope: true);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(1, fixture.FreezeCount());
    }

    [Theory]
    [InlineData("deposit")]
    [InlineData("deposit-uncovered")]
    public void LocalFormalizationBuildsOnlyTheRequestedModule(string command)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run(command, atomId: null);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains(fixture.Calls(), call => call.StartsWith(
            "make:lean-report-scoped LEAN_TARGETS=D5.S0.Carrier.Probe LEAN_REPORT=", StringComparison.Ordinal));
        Assert.DoesNotContain("make:lean-report", fixture.Calls());
        if (command != "cover")
            Assert.Contains(fixture.Calls(), call => call.StartsWith("make:emit PATHS=", StringComparison.Ordinal));
    }

}
