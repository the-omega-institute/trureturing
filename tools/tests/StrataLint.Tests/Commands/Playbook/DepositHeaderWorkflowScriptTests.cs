using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DepositCoverWorkflowScriptTests
{
    private const string CanonicalHeaderFinding =
        "expected the canonical Lean header at byte zero "
        + "(six-line legacy header or seven-line header with utility)";

    [Fact]
    public void DepositHeaderCommandEvaluatesRegisteredSl012ForFrozenTargetWithoutLoadingLeanReport()
    {
        var fixture = new RuleFixture();
        fixture.Files[RuleFixture.RingPath] = TransactionFixture.ExactSixLineLean(
            RuleFixture.RingPath,
            "def goldenRing : Nat := 0\n");
        var statePath = FrozenStatePath.FromModulePath(
            RepoPath.CreateKnown(RuleFixture.RingPath)).Value;
        fixture.Files[statePath] = "{}\n";
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
        fixture.Files[RuleFixture.RingPath] = TransactionFixture.SevenLineWrappedDigest(
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

    [Fact]
    public void HeaderCheckScriptRejectsUtilityWithoutSpaceAfterColon()
    {
        if (OperatingSystem.IsWindows()) return;
        using var repository = new TemporaryDirectory();
        var initialize = TestProcessRunner.Run(
            "git",
            ["init", "--quiet", repository.Path],
            repository.Path,
            BoundedProcessRunner.HangDetectionBudget,
            4096);
        Assert.Equal(0, initialize.ExitCode);
        var moduleDirectory = Path.Combine(repository.Path, "D5", "S0", "Carrier");
        Directory.CreateDirectory(moduleDirectory);
        var modulePath = Path.Combine(moduleDirectory, "Probe.lean");
        File.WriteAllText(
            modulePath,
            """
            /- GID: D5/S0/Carrier/Probe
               generality: G
               mirror-B: D5/B/S0/Carrier/Probe
               mirror-E: none(waiver:pure-definition)
               anchors: []
               utility:none
               digest: Synthetic fixture. -/
            def probe : Nat := 0
            """ + "\n",
            new UTF8Encoding(false));
        var script = Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "scripts", "agent", "header-check.sh");

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [script, modulePath],
            repository.Path,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains(
            "第 6 行必须是 '   utility: '",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }
}

public sealed class DepositHeaderUtilityTests
{
    [Fact]
    public void DepositHeaderCheckRequiresUtilityForUnfrozenTarget()
    {
        var fixture = new RuleFixture();
        var source = new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports));
        var result = Run(fixture, source);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(
            $"DEPOSIT_HEADER_UTILITY_MISSING module={RuleFixture.RingPath}\n",
            result.Output);
        Assert.Equal(string.Empty, result.Error);
        Assert.Equal(0, source.CallCount);
    }

    [Fact]
    public void DepositHeaderCheckRejectsDanglingDeclarationTarget()
    {
        var fixture = new RuleFixture();
        AddUtility(
            fixture,
            "kind=bounded-enumeration; basis=terminal=gid:D5/S0/Carrier/Ring.missing");
        var source = new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports));

        var result = Run(fixture, source);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(
            $"DEPOSIT_HEADER_UTILITY_TARGET_DANGLING module={RuleFixture.RingPath} "
            + "target=D5/S0/Carrier/Ring.missing\n",
            result.Output);
        Assert.Equal(1, source.CallCount);
    }

    [Fact]
    public void DepositHeaderCheckResolvesAtomAndTaskWithoutCoverageChecks()
    {
        var atomFixture = new RuleFixture();
        AddUtility(
            atomFixture,
            $"kind=bounded-enumeration; basis=refutes=atom:{RuleFixture.FixtureAtomId}");
        var atomSource = new FakeLeanReportSource(LeanAxiomReport.Create(atomFixture.Reports));

        var atomResult = Run(atomFixture, atomSource);

        Assert.Equal(0, atomResult.ExitCode);
        Assert.Equal(1, atomSource.CallCount);

        var taskFixture = new RuleFixture();
        taskFixture.AddSyntheticUnregisteredFrontierTask("D5-T0098");
        AddUtility(
            taskFixture,
            "kind=certified-instance; basis=terminal=task:D5-T0098");
        var taskSource = new FakeLeanReportSource(LeanAxiomReport.Create(taskFixture.Reports));

        var taskResult = Run(taskFixture, taskSource);

        Assert.Equal(0, taskResult.ExitCode);
        Assert.Equal(1, taskSource.CallCount);
    }

    [Fact]
    public void AmbiguousAtomTargetClassifiedConsistentlyAcrossPhases()
    {
        var fixture = new RuleFixture();
        AddUtility(
            fixture,
            $"kind=bounded-enumeration; basis=refutes=atom:{RuleFixture.FixtureAtomId}");
        fixture.Files[RuleFixture.FixtureBackfillAtomPath.Replace(
            "/partial-open/",
            "/residual-open/",
            StringComparison.Ordinal)] = fixture.Files[RuleFixture.FixtureBackfillAtomPath];
        var source = new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports));

        var preDeposit = Run(fixture, source);
        var statePath = FrozenStatePath.FromModulePath(
            RepoPath.CreateKnown(RuleFixture.RingPath)).Value;
        fixture.Files[statePath] =
            "{\"statement_id\":\"sha256:0000000000000000000000000000000000000000000000000000000000000000\"}\n";
        var firstFreeze = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(31),
            fixture.Build(RawChangeSet.CreateWithKinds(
                [(statePath, RawChangeKind.Added)]))).Diagnostics;

        Assert.Equal(1, preDeposit.ExitCode);
        Assert.Equal(
            $"DEPOSIT_HEADER_UTILITY_INPUT_UNKNOWN module={RuleFixture.RingPath} "
            + $"reason=ambiguous-atom-target:{RuleFixture.FixtureAtomId}\n",
            preDeposit.Output);
        var firstFreezeBlock = Assert.Single(
            firstFreeze,
            diagnostic => diagnostic.AdmissionEffect is AdmissionEffect.Block);
        Assert.Equal(
            $"UTILITY-INPUT-UNKNOWN module={RuleFixture.RingPath} "
            + $"reason=ambiguous-atom-target:{RuleFixture.FixtureAtomId}",
            firstFreezeBlock.Message);
    }

    [Fact]
    public void DepositHeaderCheckDoesNotRequireConsumerImportPath()
    {
        var fixture = new RuleFixture();
        AddUtility(
            fixture,
            "kind=certified-instance; "
            + "basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue");
        var source = new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports));

        var result = Run(fixture, source);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(1, source.CallCount);
    }

    [Fact]
    public void DepositHeaderReportLoadFailureIsUtilityInputUnknown()
    {
        var fixture = new RuleFixture();
        AddUtility(
            fixture,
            "kind=certified-instance; basis=terminal=gid:D5/S0/Carrier/Ring.goldenRing");
        var source = new FakeLeanReportSource(null);

        var result = Run(fixture, source);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(
            $"DEPOSIT_HEADER_UTILITY_INPUT_UNKNOWN module={RuleFixture.RingPath} "
            + "reason=current-lean-report-load-failed\n",
            result.Output);
        Assert.Equal(string.Empty, result.Error);
        Assert.Equal(1, source.CallCount);
    }

    [Fact]
    public void DepositHeaderCheckAllowsLegacyHeaderForFrozenTarget()
    {
        var fixture = new RuleFixture();
        var statePath = FrozenStatePath.FromModulePath(
            RepoPath.CreateKnown(RuleFixture.RingPath)).Value;
        fixture.Files[statePath] = "{}\n";
        var source = new FakeLeanReportSource(null);

        var result = Run(fixture, source);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(0, source.CallCount);
    }

    private static ExplicitCommandResult Run(
        RuleFixture fixture,
        ILeanReportSource source)
    {
        var current = RawRepositorySnapshot.Create(
            fixture.Files.Select(static pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var repository = new FakeRepositoryGateway(
            RawChangeSet.Create([RuleFixture.RingPath]),
            current,
            baseline: null);
        var environment = new ProductionCliEnvironment("/repo", repository, source);
        return environment.DepositHeaderCheck(["--target", RuleFixture.RingPath]);
    }

    private static void AddUtility(RuleFixture fixture, string utility) =>
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath].Replace(
            "   anchors: []\n",
            $"   anchors: []\n   utility: {utility}\n",
            StringComparison.Ordinal);
}
