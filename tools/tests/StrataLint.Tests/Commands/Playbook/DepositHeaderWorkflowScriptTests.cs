using static StrataLint.TestSupport.TransactionFixture;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DepositHeaderCommandTests
{

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
            baseline: current);
        var environment = new ProductionCliEnvironment(
            "/repo",
            repository,
            new FakeLeanReportSource(null));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["deposit-header-check", "--target", RuleFixture.RingPath, "--protected-base", new string('b', 40)],
            environment,
            console);

        Assert.Equal(0, exitCode);
        Assert.Equal(
            $"DEPOSIT_HEADER_CHECKED SL-012 {RuleFixture.RingPath}\n",
            console.Output);
        Assert.Empty(console.Error);
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
            baseline: current);
        var environment = new ProductionCliEnvironment(
            "/repo",
            repository,
            new FakeLeanReportSource(null));
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            ["deposit-header-check", "--target", RuleFixture.RingPath, "--protected-base", new string('b', 40)],
            environment,
            console);

        Assert.Equal(1, exitCode);
        Assert.Equal(
            $"SL-012 {RuleFixture.RingPath}: {CanonicalHeaderFinding}\n",
            console.Output);
        Assert.Empty(console.Error);
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
            "kind=checker; basis=terminal=gid:D5/S0/Carrier/Ring.missing; instance=D5/S0/Carrier/Ring.goldenRing");
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
            UtilityAdmissionTestSupport.AddRefutationEvidence(atomFixture,
                $"kind=bounded-enumeration; basis=refutes=atom:{RuleFixture.FixtureAtomId}"));
        var atomSource = new FakeLeanReportSource(LeanAxiomReport.Create(atomFixture.Reports));

        var atomResult = Run(atomFixture, atomSource);

        Assert.Equal(0, atomResult.ExitCode);
        Assert.Equal(1, atomSource.CallCount);

        var taskFixture = new RuleFixture();
        taskFixture.AddSyntheticUnregisteredFrontierTask("D5-T0098");
        AddUtility(
            taskFixture,
            "kind=checker; basis=terminal=task:D5-T0098; instance=D5/S0/Carrier/Ring.goldenRing");
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
            UtilityAdmissionTestSupport.AddRefutationEvidence(fixture,
                $"kind=bounded-enumeration; basis=refutes=atom:{RuleFixture.FixtureAtomId}"));
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
            "kind=numeric-reduction; "
            + "basis=consumer=D5/S0/Carrier/ValuesBinding.fixtureValue; premises=D5/S0/Carrier/Ring.goldenRing");
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
        fixture.Baseline[statePath] = "{}\n";
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
            baseline: UtilityAdmissionTestSupport.Raw(fixture.Baseline));
        var environment = new ProductionCliEnvironment("/repo", repository, source);
        return environment.DepositHeaderCheck(["--target", RuleFixture.RingPath, "--protected-base", new string('b', 40)]);
    }

    private static void AddUtility(RuleFixture fixture, string utility) =>
        fixture.Files[RuleFixture.RingPath] = fixture.Files[RuleFixture.RingPath].Replace(
            "   anchors: []\n",
            $"   anchors: []\n   utility: {utility}\n",
            StringComparison.Ordinal);
}
