using static StrataLint.TestSupport.TransactionFixture;

namespace StrataLint.PlaybookScript.Tests;

public sealed class TransactionFixtureEntryTests
{
    [Fact]
    public void ExplicitCliEntryRejectsMissingApphostBeforeWorkflow()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var path = Path.Combine(fixture.Root, "missing-apphost");

        var error = Assert.Throws<InvalidOperationException>(() => fixture.Run("deposit", realCliPath: path));

        Assert.Equal($"PLAYBOOK_REAL_CLI 需要 StrataLint apphost 与测试程序集同目录,但 {path} 不存在;"
            + "消费该夹具的测试项目必须引用 StrataLint.Cli。", error.Message);
        Assert.Empty(fixture.CallKinds());
        Assert.Equal(0, fixture.FreezeCount());
    }

    [Fact]
    public void ExplicitCliEntryExecutesProvidedApphostForFrozenQuery()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var path = Path.Combine(fixture.Root, "explicit-apphost");
        TestExecutable.WriteExecutable(path, """
            #!/bin/bash
            set -euo pipefail
            [[ "$*" == 'ledger-frozen --target D5/S0/Carrier/Probe.lean' ]]
            echo 'LEDGER_FROZEN_INVALID explicit apphost query' >&2
            exit 2
            """);

        var result = fixture.Run("deposit", realCliPath: path);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("LEDGER_FROZEN_INVALID explicit apphost query", Diagnostics(result), StringComparison.Ordinal);
        Assert.Equal(new[] { "make:lean-report", "dotnet:deposit-header-check", "make:emit", "dotnet:ledger-frozen" },
            fixture.CallKinds());
        Assert.Equal(0, fixture.FreezeCount());
    }
}
