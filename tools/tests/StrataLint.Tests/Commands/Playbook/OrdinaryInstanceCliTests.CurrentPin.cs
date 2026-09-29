using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.UtilityAdmissionTestSupport;

namespace StrataLint.Tests;

public sealed partial class OrdinaryInstanceCliTests
{

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CurrentOnlyStateDoesNotBypassProductionDepositPrecheck(bool currentPin)
    {
        var fixture = InstanceFixture(Ordinary);
        if (currentPin) AddCandidateState(fixture);
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([RuleFixture.RingPath]),
            Raw(fixture.Files), Raw(fixture.Baseline));
        var console = new BufferedConsole();

        var exit = CliApplication.Run(["deposit-header-check", "--target", RuleFixture.RingPath,
                "--protected-base", new string('b', 40)],
            new ProductionCliEnvironment("/repo", repository, new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports))), console);

        Assert.Equal(1, exit);
        Assert.Contains("DEPOSIT_HEADER_UTILITY_ORDINARY_INSTANCE_BANNED", console.Output, StringComparison.Ordinal);
        Assert.Equal(["baseline"], repository.ReadRevisionCalls);
    }
}
