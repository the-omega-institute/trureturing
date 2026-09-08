using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.OrdinaryInstanceAdmissionTests;

namespace StrataLint.Tests;

public sealed class OrdinaryInstanceCliTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ProductionCheckReportsOrdinaryBanWithOrWithoutFirstState(bool freeze)
    {
        using var temporary = new TemporaryDirectory();
        var fixture = InstanceFixture("kind=certified-instance; basis=terminal=gid:D5/S0/Carrier/Ring.fixed_sum");
        fixture.AddBackfillTargets();
        ProductionEnvironmentTests.InstallDefaultAdmissionPlaneFileMap(fixture);
        var paths = new List<string> { RuleFixture.RingPath };
        if (freeze) paths.Add(AddCandidateState(fixture));
        var raw = Raw(fixture.Files);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
        var reportPath = Path.Combine(temporary.Path, "candidate.json");
        RawLeanReportArtifact.WriteFile(reportPath, snapshot, LeanAxiomReport.Create(fixture.Reports));
        var repository = new FakeRepositoryGateway(RawChangeSet.Create(paths), raw, Raw(fixture.Baseline));
        var console = new BufferedConsole();

        var exit = CliApplication.Run(["check", "--candidate-lean-report", reportPath],
            new ProductionCliEnvironment("/repo", repository, new FakeLeanReportSource(null)), console);

        Assert.True(exit == 1, console.Output + console.Error);
        Assert.Contains("UTILITY-ORDINARY-INSTANCE-BANNED", console.Output, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("branch")]
    [InlineData("unreadable")]
    public void DepositRequiresAnAvailableImmutableProtectedBaseline(string defect)
    {
        var fixture = InstanceFixture("none");
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]), Raw(fixture.Files),
            defect == "unreadable" ? null : Raw(fixture.Baseline));
        var arguments = new List<string> { "deposit-header-check", "--target", RuleFixture.RingPath };
        if (defect != "missing") arguments.AddRange(["--protected-base", defect == "branch" ? "origin/dev" : new string('b', 40)]);
        var console = new BufferedConsole();

        var exit = CliApplication.Run(arguments,
            new ProductionCliEnvironment("/repo", repository, new FakeLeanReportSource(null)), console);

        Assert.Equal(2, exit);
        Assert.Contains(defect == "unreadable" ? "DEPOSIT_HEADER_CHECK_INVALID" : "USAGE:", console.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DepositAcceptsConsumerFreeRefutationBeforeCoverageOrFirstPin(bool pin)
    {
        var fixture = UtilityRefutationTests.RefutationFixture();
        if (pin) AddCandidateState(fixture);
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]), Raw(fixture.Files), Raw(fixture.Baseline));
        var console = new BufferedConsole();

        var exit = CliApplication.Run(["deposit-header-check", "--target", RuleFixture.RingPath,
                "--protected-base", new string('b', 40)],
            new ProductionCliEnvironment("/repo", repository, new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports))), console);

        Assert.Equal(0, exit);
        Assert.Contains("DEPOSIT_HEADER_CHECKED", console.Output, StringComparison.Ordinal);
    }
}
