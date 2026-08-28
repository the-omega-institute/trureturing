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
        Assert.Empty(fixture.ReceiptArtifacts());
        Assert.Equal(blueprintBefore, fixture.BlueprintState());
        Assert.DoesNotContain("make:emit", fixture.CallKinds());
        Assert.DoesNotContain("dotnet:emit-formalization-receipt", fixture.CallKinds());
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
    }

    [Fact]
    public void DepositRejectsSevenLineWrappedDigestWithExistingFreezeBeforeReceiptWrite()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TransactionFixture();
        fixture.ChangeFormalizationToSevenLineWrappedDigest();
        fixture.WriteActiveFreezeForCurrentModule();
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
        Assert.Empty(fixture.ReceiptArtifacts());
        Assert.Equal(
            ["dotnet:freeze-status", "dotnet:deposit-header-check"],
            fixture.CallKinds());
        Assert.DoesNotContain("make:emit", fixture.CallKinds());
        Assert.DoesNotContain("dotnet:emit-formalization-receipt", fixture.CallKinds());
        Assert.DoesNotContain("dotnet:ledger-append", fixture.CallKinds());
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

    internal sealed partial class TransactionFixture
    {
        internal void ChangeFormalizationToSevenLineWrappedDigest()
        {
            WriteFile(LeanPath, SevenLineWrappedDigest(
                Gid[..Gid.LastIndexOf('.')],
                "theorem probe : True := by trivial\n"));
            WriteFile(DefinitionPath, "definition deposited\n");
        }

        internal string[] ReceiptArtifacts()
        {
            var directory = Path.Combine(Root, "Meta", "Digestion", "formalizations");
            return Directory.Exists(directory)
                ? Directory.EnumerateFiles(directory)
                    .Select(path => Path.GetRelativePath(Root, path))
                    .Order(StringComparer.Ordinal)
                    .ToArray()
                : [];
        }

        internal string[] BlueprintState()
        {
            var directory = Path.Combine(Root, "Blueprint");
            return Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories)
                .Order(StringComparer.Ordinal)
                .Select(path => Path.GetRelativePath(Root, path) + "\n" + File.ReadAllText(path))
                .ToArray();
        }

        internal static string ExactSixLineLean(string gid, string declaration)
        {
            var documentGid = gid[..gid.LastIndexOf('.')];
            return $"/- GID: {documentGid}\n"
                + "   generality: G\n"
                + $"   mirror-B: D5/B/{documentGid[3..]}\n"
                + "   mirror-E: none(waiver:pure-definition)\n"
                + "   anchors: []\n"
                + "   digest: Synthetic deposit workflow fixture. -/\n"
                + declaration;
        }
    }

    private static string SevenLineWrappedDigest(string documentGid, string declaration) =>
        $"/- GID: {documentGid}\n"
        + "   generality: G\n"
        + $"   mirror-B: D5/B/{documentGid[3..]}\n"
        + "   mirror-E: none(waiver:pure-definition)\n"
        + "   anchors: []\n"
        + "   digest: Synthetic deposit workflow digest\n"
        + "   wraps onto physical line seven. -/\n"
        + declaration;
}
