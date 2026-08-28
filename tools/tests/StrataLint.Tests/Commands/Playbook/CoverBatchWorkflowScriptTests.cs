using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Fact]
    public void CoverBatchRederivesEachDistinctAtomsEnvelopeAndReemitsOnceAtEnd()
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
        Assert.Equal(before + 3, fixture.CommitCount());
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
                + " --base synthetic-base"
                + $" --envelope {TransactionFixture.ReceiptRelativePath}"
                + " --align-scribe-receipt",
            fixture.Calls());
        Assert.Contains(
            "dotnet:cover-atom"
                + $" --cover-atom {TransactionFixture.SecondaryAtomId}"
                + $" --gid {TransactionFixture.SecondaryGid}"
                + " --base synthetic-base"
                + $" --envelope {TransactionFixture.SecondaryReceiptRelativePath}"
                + " --align-scribe-receipt",
            fixture.Calls());
        Assert.Empty(fixture.Status());

        using var failedFixture = new TransactionFixture();
        var failedAtoms = failedFixture.WriteBatchFile(
            $"{TransactionFixture.AtomId}\t{TransactionFixture.Gid}\n");
        var failedBefore = failedFixture.CommitCount();
        var failed = failedFixture.RunBatch(failedAtoms, coverDispositionFailure: true);
        Assert.NotEqual(0, failed.ExitCode);
        Assert.Equal(failedBefore + 1, failedFixture.CommitCount());
        Assert.Contains("cover_disposition:", failedFixture.BackfillContents(), StringComparison.Ordinal);
        Assert.Equal(
            ["make:lean-report", "dotnet:cover-atom"],
            failedFixture.CallKinds());
        Assert.Empty(failedFixture.Status());
    }

    [Fact]
    public void CoverBatchCleansEachDistinctAtomsInterruptedReceiptBeforeSharedLeanReport()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.AddSecondaryFormalization();
        fixture.LeaveInterruptedTemporaryFiles(TransactionFixture.ReceiptRelativePath);
        fixture.LeaveInterruptedTemporaryFiles(TransactionFixture.SecondaryReceiptRelativePath);
        var atoms = fixture.WriteBatchFile(
            $"{TransactionFixture.AtomId}\t{TransactionFixture.Gid}\n"
            + $"{TransactionFixture.SecondaryAtomId}\t{TransactionFixture.SecondaryGid}\n");

        var result = fixture.RunBatch(atoms);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal("make:lean-report", fixture.CallKinds()[0]);
        Assert.False(File.Exists(Path.Combine(
            fixture.Root,
            TransactionFixture.ReceiptRelativePath + ".tmp.abandoned")));
        Assert.False(File.Exists(Path.Combine(
            fixture.Root,
            TransactionFixture.SecondaryReceiptRelativePath + ".tmp.abandoned")));
        Assert.Empty(fixture.Status());
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
                    "PLAYBOOK_INVALID_RECEIPT=0",
                    $"PLAYBOOK_COVER_DISPOSITION_FAILURE={(coverDispositionFailure ? "1" : "0")}",
                    "PLAYBOOK_MUTATE_RECEIPT_AFTER_PREPARE=",
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
