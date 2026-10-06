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

    [Fact]
    public void BulkCandidatesUseReportFreeInputsWithoutWholeEvaluationScope()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([]),
            Snapshot(fixture.Files),
            baseline: null);

        var result = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(null))
            .DigestStatus(["--formalize-candidates"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.NotEmpty(gateway.ScopedCurrentReads);
        Assert.All(
            gateway.ScopedCurrentReads,
            scope => Assert.DoesNotContain("Meta", scope, StringComparer.Ordinal));
        Assert.All(
            gateway.ScopedCurrentReads.SelectMany(static scope => scope),
            path => Assert.DoesNotContain("D5/", path, StringComparison.Ordinal));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void UncoveredDetailedCandidateDoesNotLoadTheLeanArtifact(bool hasArtifact)
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        fixture.Files[RuleFixture.FixtureBackfillAtomPath.Replace(
            "/partial-open/", "/residual-open/", StringComparison.Ordinal)] =
            RuleFixture.FixtureBackfillAtom.Replace(
                "coverage_gids:\n  - gid: D5/S0/Carrier/BackfillTarget\n    target_statement_id: null",
                "coverage_gids: []",
                StringComparison.Ordinal);
        using var temporary = new TemporaryDirectory();
        if (hasArtifact)
        {
            RawLeanReportArtifact.WriteFile(
                RawLeanReportArtifact.DefaultPath(temporary.Path),
                Decode(Snapshot(fixture.Files)),
                LeanAxiomReport.Create(fixture.Reports));
        }
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([]), Snapshot(fixture.Files), baseline: null);
        var environment = new ProductionCliEnvironment(
            temporary.Path, gateway, new PrecomputedLeanReportSource(temporary.Path));

        var result = environment.DigestStatus(
            ["--formalize-candidates", "--atom-id", RuleFixture.FixtureAtomId]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("stratalint-formalize-candidates-v5", result.Output, StringComparison.Ordinal);
        Assert.All(gateway.ScopedCurrentReads.SelectMany(static scope => scope),
            path => Assert.False(path.StartsWith("D5", StringComparison.Ordinal)
                || path.StartsWith("Reg", StringComparison.Ordinal)
                || path.StartsWith("Golden/Frozen", StringComparison.Ordinal)));
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
    public void CoverageBackedDetailedCandidateKeepsTheEvaluationScope()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var gateway = new FakeRepositoryGateway(
            RawChangeSet.Create([]),
            Snapshot(fixture.Files),
            baseline: null);

        var result = new ProductionCliEnvironment(
            "/repo",
            gateway,
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)))
            .DigestStatus(["--formalize-candidates", "--atom-id", RuleFixture.FixtureAtomId]);

        Assert.True(result.Success, result.Error);
        var paths = gateway.ScopedCurrentReads.SelectMany(static scope => scope).ToArray();
        Assert.Contains(TheoryAtomizerDataLoader.DataPath, paths);
        Assert.Contains("D5", paths);
        Assert.DoesNotContain(DigestionCasStore.RootPath.TrimEnd('/'), paths);
        Assert.DoesNotContain(EngineeringProjectRegistry.ManifestPath, paths);
    }

    [Fact]
    public void ReadinessStillRejectsInvalidCoverageBinding()
    {
        var environment = DigestStatusHistoricalCoverageEnvironment();

        var result = environment.DigestStatus(["--readiness"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-target-mismatch", result.Error, StringComparison.Ordinal);
    }

}
