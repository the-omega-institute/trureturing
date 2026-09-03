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

    internal sealed partial class TransactionFixture
    {
        internal bool LeanReportExists() => File.Exists(
            Path.Combine(Root, ".lake/build/stratalint/raw-lean-report.json"));

        internal ProcessOutput RunMakeCover(bool includeAtomId) =>
            TestProcessRunner.Run(
                "/usr/bin/env",
                includeAtomId
                    ?
                    [
                        $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                        $"PLAYBOOK_TEST_CALLS={callsPath}",
                        "/usr/bin/make",
                        "cover",
                        $"ATOM_ID={AtomId}",
                    ]
                    :
                    [
                        $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                        $"PLAYBOOK_TEST_CALLS={callsPath}",
                        "/usr/bin/make",
                        "cover",
                    ],
                Root,
                TestBudgets.ShortProcessHangGuard,
                128 * 1024);
    }
}
