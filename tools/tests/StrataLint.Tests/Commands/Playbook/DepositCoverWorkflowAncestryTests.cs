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
        Assert.DoesNotContain("dotnet:ledger-append", fixture.Calls());
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

    internal sealed partial class TransactionFixture
    {
        internal string HeadRevision() => Git("rev-parse", "HEAD").Trim();

        internal string CommitAll(string message)
        {
            Git("add", "-A");
            Git("commit", "-qm", message);
            return HeadRevision();
        }

        internal string WriteAcceptedFreezeV5()
        {
            var identity = new string('4', 64);
            var relativePath = $"{LedgerPath}/{identity}.json";
            WriteFile(relativePath, JsonSerializer.Serialize(new
            {
                event_hash = "sha256:" + identity,
                event_type = "Freeze",
                payload = new
                {
                    declaration_statement_ids = Array.Empty<object>(),
                    descriptor_selector = LeanPath,
                    prerequisite_frozen_node_ids = Array.Empty<string>(),
                    statement_id = "sha256:" + identity,
                },
                schema_version = 5,
            }) + "\n");
            return relativePath;
        }

        internal string WriteLegacyFreeze()
        {
            var identity = new string('5', 64);
            var relativePath = $"{LedgerPath}/{identity}.json";
            WriteFile(relativePath, JsonSerializer.Serialize(new
            {
                event_type = "Freeze",
                payload = new { descriptor_selector = LeanPath },
                schema_version = 4,
            }) + "\n");
            return relativePath;
        }
    }
}
