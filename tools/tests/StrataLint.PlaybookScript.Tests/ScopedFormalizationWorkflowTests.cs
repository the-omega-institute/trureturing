using static StrataLint.TestSupport.TransactionFixture;

namespace StrataLint.PlaybookScript.Tests;

public sealed class ScopedFormalizationWorkflowTests
{
    [Theory]
    [InlineData("deposit")]
    [InlineData("deposit-uncovered")]
    [InlineData("cover")]
    public void LocalFormalizationBuildsOnlyTheRequestedModule(string command)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalization();

        var result = fixture.Run(command, atomId: command == "deposit-uncovered" ? null : AtomId);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("make:lean-report-scoped LEAN_TARGETS=D5.S0.Carrier.Probe", fixture.Calls());
        Assert.DoesNotContain("make:lean-report", fixture.Calls());
        if (command != "cover")
            Assert.Contains(fixture.Calls(), call => call.StartsWith("make:emit PATHS=", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("")]
    [InlineData("atom-1\tD5/S2/Missing.missing\n")]
    [InlineData("atom-1\tinvalid\n")]
    public void BatchRejectsUnresolvedOrEmptyScopeBeforeBuilding(string contents)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();

        var result = fixture.RunBatch(fixture.WriteBatchFile(contents));

        Assert.NotEqual(0, result.ExitCode);
        Assert.Empty(fixture.CallKinds());
        Assert.Equal(0, fixture.FreezeCount());
    }

    [Fact]
    public void BatchBuildsTheDeduplicatedUnionOfAllTargets()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.AddSecondaryFormalization();
        var batch = fixture.WriteBatchFile($"{AtomId}\t{Gid}\n{SecondaryAtomId}\t{SecondaryGid}\n");

        var result = fixture.RunBatch(batch);

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Contains("make:lean-report-scoped LEAN_TARGETS=D5.S0.Carrier.Probe D5.S3.Observer.WindowRegisterCRT", fixture.Calls());
        Assert.DoesNotContain("make:lean-report", fixture.Calls());
    }
}
