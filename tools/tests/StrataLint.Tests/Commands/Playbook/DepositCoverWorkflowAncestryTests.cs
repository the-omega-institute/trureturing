using System.Text;
using System.Text.Json;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Fact]
    public void DeliverCheckRejectsAddedLegacyFreeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var deliveryBase = fixture.HeadRevision();
        fixture.ChangeFormalization();
        var eventPath = fixture.WriteLegacyFreeze();
        fixture.CommitAll("record freeze");

        var result = fixture.Run("deliver-check", baseRevision: deliveryBase);

        Assert.Equal(1, result.ExitCode);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("PLAYBOOK_INVALID", error, StringComparison.Ordinal);
        Assert.Contains(eventPath, error, StringComparison.Ordinal);
        Assert.Contains("is not a v5 Freeze", error, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet:ledger-align", fixture.Calls());
        Assert.DoesNotContain("make:preflight", fixture.Calls());
    }

    [Fact]
    public void DeliverCheckAcceptsAddedCanonicalV5Freeze()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var deliveryBase = fixture.HeadRevision();
        fixture.ChangeFormalization();
        fixture.WriteAcceptedFreezeV5();
        fixture.CommitAll("record freeze");

        var result = fixture.Run("deliver-check", baseRevision: deliveryBase);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("make:preflight BASE=" + deliveryBase, fixture.Calls());
    }

}
