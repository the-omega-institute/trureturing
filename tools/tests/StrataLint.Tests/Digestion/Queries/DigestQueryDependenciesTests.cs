using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void BulkCandidatesDoNotRequireLeanOrScribe(bool missingVerifier)
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var report = new FakeLeanReportSource(null);
        var verifier = new FakeScribeEmissionVerifier(null);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), null),
            report,
            missingVerifier ? null : verifier);

        var result = environment.DigestStatus(["--formalize-candidates"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("stratalint-formalize-candidates-v5", result.Output, StringComparison.Ordinal);
        Assert.Equal(0, report.CallCount);
        Assert.Equal(0, verifier.CallCount);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ReadinessRequiresLeanButDoesNotRequireScribe(bool missingVerifier)
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var report = new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports));
        var verifier = new FakeScribeEmissionVerifier(null);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), null),
            report,
            missingVerifier ? null : verifier);

        var result = environment.DigestStatus(["--readiness"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("stratalint-digestion-readiness-v1", result.Output, StringComparison.Ordinal);
        Assert.Equal(1, report.CallCount);
        Assert.Equal(0, verifier.CallCount);
    }

    [Fact]
    public void ReadinessStillRejectsUnavailableLeanReport()
    {
        var fixture = new RuleFixture();
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), null),
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.DigestStatus(["--readiness"]);

        Assert.False(result.Success);
        Assert.Contains("Lean report source should not be called", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void DetailedCandidateDoesNotRequireScribe()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var verifier = new FakeScribeEmissionVerifier(null);
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), null),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            verifier);

        var result = environment.DigestStatus(
            ["--formalize-candidates", "--atom-id", RuleFixture.FixtureAtomId]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, verifier.CallCount);
    }

    [Fact]
    public void ReadinessStillRejectsInvalidCoverageBinding()
    {
        var environment = DigestStatusHistoricalCoverageEnvironment();

        var result = environment.DigestStatus(["--readiness"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-target-mismatch", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ReadinessStillRejectsCorruptCas()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files[RuleFixture.FixtureCasPath] = "corrupt CAS";
        var environment = DigestStatusEnvironment(fixture);

        var result = environment.DigestStatus(["--readiness"]);

        Assert.False(result.Success);
        Assert.Contains("CAS blob hash mismatch", result.Error, StringComparison.Ordinal);
    }
}
