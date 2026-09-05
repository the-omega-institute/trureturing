using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    private const string CanonicalHeaderFinding =
        "expected the exact six-line header at byte zero";

    [Fact]
    public void DepositHeaderCommandEvaluatesRegisteredSl012WithoutLoadingLeanReport()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = TransactionFixture.ExactSixLineLean(
            RuleFixture.RingPath,
            "def goldenRing : Nat := 0\n");
        var current = RawRepositorySnapshot.Create(
            fixture.Files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create([RuleFixture.RingPath]),
            current,
            baseline: null);
        var environment = new ProductionCliEnvironment(
            "/repo",
            repository,
            new FakeLeanReportSource(null));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["deposit-header-check", "--target", RuleFixture.RingPath],
            environment,
            console);

        Assert.Equal(0, exitCode);
        Assert.Equal(
            $"DEPOSIT_HEADER_CHECKED SL-012 {RuleFixture.RingPath}\n",
            console.Output);
        Assert.Empty(console.Error);
    }

    [Fact]
    public void DepositRejectsSevenLineWrappedDigestBeforeFreezeAndWritesNothing()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalizationToSevenLineWrappedDigest();
        var commitsBefore = fixture.CommitCount();
        var blueprintBefore = fixture.BlueprintState();

        var result = fixture.Run("deposit", rejectDepositHeader: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            $"SL-012 {TransactionFixture.LeanPath}: {CanonicalHeaderFinding}",
            Diagnostics(result),
            StringComparison.Ordinal);
        Assert.Equal(commitsBefore, fixture.CommitCount());
        Assert.Equal(0, fixture.FreezeCount());
        Assert.Equal(blueprintBefore, fixture.BlueprintState());
        Assert.DoesNotContain("make:emit", fixture.CallKinds());
        Assert.DoesNotContain("dotnet:ledger-align", fixture.CallKinds());
    }

    [Fact]
    public void DepositRejectsSevenLineWrappedDigestWithExistingFreezeBeforeEmission()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalizationToSevenLineWrappedDigest();
        fixture.WriteActiveFreeze();
        var commitsBefore = fixture.CommitCount();
        var blueprintBefore = fixture.BlueprintState();
        var ledgerBefore = fixture.LedgerState();

        var result = fixture.Run("deposit", rejectDepositHeader: true);

        Assert.NotEqual(0, result.ExitCode);
        Assert.Contains(
            $"SL-012 {TransactionFixture.LeanPath}: {CanonicalHeaderFinding}",
            Diagnostics(result),
            StringComparison.Ordinal);
        Assert.Equal(commitsBefore, fixture.CommitCount());
        Assert.Equal(blueprintBefore, fixture.BlueprintState());
        Assert.Equal(ledgerBefore, fixture.LedgerState());
        Assert.Equal(
            ["make:lean-report", "dotnet:deposit-header-check"],
            fixture.CallKinds());
        Assert.DoesNotContain("make:emit", fixture.CallKinds());
        Assert.DoesNotContain("dotnet:ledger-align", fixture.CallKinds());
    }

    [Fact]
    public void DepositHeaderCommandUsesRegisteredSl012ForSevenLineWrappedDigest()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = SevenLineWrappedDigest(
            "D5/S0/Carrier/Ring",
            "def goldenRing : Nat := 0\n");
        var current = RawRepositorySnapshot.Create(
            fixture.Files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create([RuleFixture.RingPath]),
            current,
            baseline: null);
        var environment = new ProductionCliEnvironment(
            "/repo",
            repository,
            new FakeLeanReportSource(null));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["deposit-header-check", "--target", RuleFixture.RingPath],
            environment,
            console);

        Assert.Equal(1, exitCode);
        Assert.Equal(
            $"SL-012 {RuleFixture.RingPath}: {CanonicalHeaderFinding}\n",
            console.Output);
        Assert.Empty(console.Error);
    }

    // TransactionFixture 提升为顶层类后不再能访问本类的 private 成员;
    // 该辅助被夹具与本类共同使用,故改 internal(同程序集可见,行为与签名不变)。
    internal static string SevenLineWrappedDigest(string documentGid, string declaration) =>
        $"/- GID: {documentGid}\n"
        + "   generality: G\n"
        + $"   mirror-B: D5/B/{documentGid[3..]}\n"
        + "   mirror-E: none(waiver:pure-definition)\n"
        + "   anchors: []\n"
        + "   digest: Synthetic deposit workflow digest\n"
        + "   wraps onto physical line seven. -/\n"
        + declaration;
}
