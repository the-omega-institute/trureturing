using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CoverBatchInvokesOneCanonicalCommandAndForwardsItsExit(bool failure)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        var atoms = fixture.WriteBatchFile(
            $"{TransactionFixture.AtomId}\t{TransactionFixture.Gid}\n"
            + $"{TransactionFixture.SecondaryAtomId}\t{TransactionFixture.SecondaryGid}\n");
        var before = fixture.CommitCount();

        var result = fixture.RunBatch(atoms, coverDispositionFailure: failure);

        Assert.Equal(failure ? 1 : 0, result.ExitCode);
        Assert.Equal(before, fixture.CommitCount());
        Assert.Equal([$"make:lean-report BASE={fixture.HeadRevision()}", "dotnet:cover-batch"], fixture.CallKinds());
        Assert.Contains($"dotnet:cover-batch --atoms {atoms} --base {fixture.HeadRevision()}", fixture.Calls());
    }

    [Fact]
    public void CoverBatchRejectsMissingFileBeforeBuilding()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();

        var result = fixture.RunBatch("missing.tsv");

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(fixture.CallKinds());
        Assert.Empty(fixture.Status());
    }
}
