using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void EchoVerifyEmitsTheResidualProjection()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.RingPath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var emitted = environment.EchoVerify(["--emit", "--base", "baseline"]);

        Assert.Equal(0, emitted.ExitCode);
        Assert.StartsWith(
            "<!-- echo-residual-summary:v3 residual=sha256:",
            emitted.Output,
            StringComparison.Ordinal);
    }
}
