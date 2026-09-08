using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanUtilityInputTests
{
    [Fact]
    public void ProducerUsesCanonicalUtilityParserToCreateStructuredObligations()
    {
        var fixture = UtilityRefutationTests.RefutationFixture();
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]),
            OrdinaryInstanceAdmissionTests.Raw(fixture.Files), null);
        var console = new BufferedConsole();
        var exit = CliApplication.Run(["lean-utility-input"],
            new ProductionCliEnvironment("/repo", repository, new FakeLeanReportSource(null)), console);

        Assert.Equal(0, exit);
        using var json = JsonDocument.Parse(console.Output);
        var obligation = Assert.Single(json.RootElement.EnumerateArray());
        Assert.Equal(RuleFixture.RingPath, obligation.GetProperty("modulePath").GetString());
        Assert.Equal(UtilityRefutationTests.Claim, obligation.GetProperty("claimGid").GetString());
        Assert.Equal("D5.S0.Carrier.Ring", obligation.GetProperty("claimModule").GetString());
        Assert.Equal("proposed_law", obligation.GetProperty("claimSelector").GetString());
        Assert.Equal("refuted_law", obligation.GetProperty("resultSelector").GetString());
        Assert.Equal(RuleFixture.RingPath, obligation.GetProperty("claimSourcePath").GetString());
        Assert.Equal("sha256:" + Convert.ToHexStringLower(System.Security.Cryptography.SHA256.HashData(
            System.Text.Encoding.UTF8.GetBytes(fixture.Files[RuleFixture.RingPath]))),
            obligation.GetProperty("claimSourceSha256").GetString());
    }

    [Theory]
    [InlineData("none")]
    [InlineData("kind=certified-instance; basis=terminal=gid:D5/S0/Carrier/Ring.fixed_sum")]
    [InlineData("kind=certified-instance; basis=refutes=gid:D5/S0/Carrier/Ring.proposed_law")]
    [InlineData("kind=certified-instance; basis=refutes=gid:D5/S0/Carrier/Ring.proposed_law; claim=D5/S0/Carrier/Ring.proposed_law; result=D5/S0/Carrier/Ring.refuted_law")]
    public void NonObligationsDoNotProduceInventedEvidence(string utility)
    {
        var fixture = OrdinaryInstanceAdmissionTests.InstanceFixture(utility);
        var repository = new FakeRepositoryGateway(RawChangeSet.Create([]),
            OrdinaryInstanceAdmissionTests.Raw(fixture.Files), null);
        var console = new BufferedConsole();
        Assert.Equal(0, CliApplication.Run(["lean-utility-input"],
            new ProductionCliEnvironment("/repo", repository, new FakeLeanReportSource(null)), console));
        Assert.Equal("[]", console.Output.Trim());
    }
}
