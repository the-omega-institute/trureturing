using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Fact]
    public void CoverBatchWritesEachEdgeAndReemitsOnceWithoutCommitting()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();
        var primaryDeposit = fixture.Run("deposit");
        Assert.True(primaryDeposit.ExitCode == 0, Diagnostics(primaryDeposit));
        fixture.AddSecondaryFormalization();
        var secondaryDeposit = fixture.Run(
            "deposit",
            TransactionFixture.SecondaryGid,
            TransactionFixture.SecondaryAtomId);
        Assert.True(secondaryDeposit.ExitCode == 0, Diagnostics(secondaryDeposit));
        fixture.ClearCalls();
        var atoms = fixture.WriteBatchFile(
            $"{TransactionFixture.AtomId}\t{TransactionFixture.Gid}\n"
            + $"{TransactionFixture.SecondaryAtomId}\t{TransactionFixture.SecondaryGid}\n");
        var before = fixture.CommitCount();

        var result = fixture.RunBatch(atoms);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(before, fixture.CommitCount());
        Assert.Equal(
            [
                "make:lean-report",
                "dotnet:cover-atom",
                "dotnet:cover-atom",
                "make:emit",
            ],
            fixture.CallKinds());
        Assert.Equal("emission: covered\n", fixture.EmissionContents());
        Assert.Contains(
            "dotnet:cover-atom"
                + $" --cover-atom {TransactionFixture.AtomId}"
                + $" --gid {TransactionFixture.Gid}"
                + " --base synthetic-base",
            fixture.Calls());
        Assert.Contains(
            "dotnet:cover-atom"
                + $" --cover-atom {TransactionFixture.SecondaryAtomId}"
                + $" --gid {TransactionFixture.SecondaryGid}"
                + " --base synthetic-base",
            fixture.Calls());
        Assert.NotEmpty(fixture.Status());

        using var failedFixture = new TransactionFixture();
        var failedAtoms = failedFixture.WriteBatchFile(
            $"{TransactionFixture.AtomId}\t{TransactionFixture.Gid}\n");
        var failedBefore = failedFixture.CommitCount();
        var failed = failedFixture.RunBatch(failedAtoms, coverDispositionFailure: true);
        Assert.NotEqual(0, failed.ExitCode);
        Assert.Equal(failedBefore, failedFixture.CommitCount());
        Assert.Contains("cover_disposition:", failedFixture.BackfillContents(), StringComparison.Ordinal);
        Assert.Equal(
            ["make:lean-report", "dotnet:cover-atom"],
            failedFixture.CallKinds());
        Assert.NotEmpty(failedFixture.Status());
    }
    [Theory]
    [InlineData("")]
    [InlineData("atom-1 D5/S0/Carrier/Probe.probe\n")]
    [InlineData("atom-1\tD5/S0/Carrier/Probe.probe\textra\n")]
    [InlineData("INVALID\tD5/S0/Carrier/Probe.probe\n")]
    public void CoverBatchRejectsInvalidTsvBeforeBuildingOrWriting(string contents)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var atoms = fixture.WriteBatchFile(contents);
        var before = fixture.CommitCount();

        var result = fixture.RunBatch(atoms);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Equal(before, fixture.CommitCount());
        Assert.Empty(fixture.CallKinds());
        Assert.Empty(fixture.Status());
    }

    internal sealed partial class TransactionFixture
    {
        internal string WriteBatchFile(string contents)
        {
            const string path = ".lake/cover-batch.tsv";
            WriteFile(path, contents);
            return path;
        }

        internal ProcessOutput RunBatch(string atomsFile, bool coverDispositionFailure = false) =>
            TestProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                    $"PLAYBOOK_TEST_CALLS={callsPath}",
                    "PLAYBOOK_STALE_REPORT=0",
                    $"PLAYBOOK_COVER_DISPOSITION_FAILURE={(coverDispositionFailure ? "1" : "0")}",
                    "/bin/bash",
                    Path.Combine(Root, ScriptPath),
                    "cover-batch",
                    "synthetic-base",
                    atomsFile,
                ],
                Root,
                BoundedProcessRunner.HangDetectionBudget,
                128 * 1024);
    }

}
