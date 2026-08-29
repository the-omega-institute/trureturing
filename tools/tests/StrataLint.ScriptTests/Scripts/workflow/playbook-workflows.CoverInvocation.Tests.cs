using StrataLint.Engine;

namespace StrataLint.ScriptTests;

public sealed partial class PlaybookWorkflowsTests
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

    [Fact]
    public void CoverRemovesInterruptedTemporaryFilesBeforeProducingLeanReport()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.LeaveInterruptedTemporaryFiles();

        var result = fixture.Run("cover");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.False(fixture.InterruptedTemporaryFilesExist());
    }

    internal sealed partial class TransactionFixture
    {
        internal bool LeanReportExists() => File.Exists(
            Path.Combine(Root, ".lake/build/stratalint/raw-lean-report.json"));

        internal bool InterruptedTemporaryFilesExist() => Directory
            .EnumerateFiles(
                Path.GetDirectoryName(ReceiptPath)!,
                Path.GetFileName(ReceiptPath) + ".tmp.*")
            .Any();

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
