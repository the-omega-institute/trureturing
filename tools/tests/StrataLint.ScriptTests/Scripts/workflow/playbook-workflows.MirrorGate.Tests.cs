using System.Text;

namespace StrataLint.ScriptTests;

public sealed partial class PlaybookWorkflowsTests
{
    [Fact]
    public void DepositRejectsNewModuleWhenBlueprintMirrorIsMissing()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.AddNewFormalization(withMirror: false);

        var result = fixture.Run("deposit", TransactionFixture.NewGid, baseRevision: "HEAD");

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            "missing Blueprint mirror: Blueprint/D5/S2/NewModule.md; run make emit",
            Encoding.UTF8.GetString(result.StandardError),
            StringComparison.Ordinal);
        Assert.DoesNotContain("make:lean-report", fixture.CallKinds());
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
        Assert.Equal(1, fixture.CommitCount());
        Assert.Equal(0, fixture.FreezeCount(TransactionFixture.NewLeanPath));
    }

    [Fact]
    public void DepositAcceptsNewModuleWhenBlueprintMirrorIsPresent()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.AddNewFormalization(withMirror: true);
        var before = fixture.CommitCount();

        var result = fixture.Run("deposit", TransactionFixture.NewGid, baseRevision: "HEAD");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Equal(before + 2, fixture.CommitCount());
        Assert.Equal(1, fixture.FreezeCount(TransactionFixture.NewLeanPath));
        Assert.True(File.Exists(Path.Combine(fixture.Root, TransactionFixture.NewEmissionPath)));
        Assert.Empty(fixture.Status());
    }
}
