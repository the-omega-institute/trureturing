using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void EchoVerifyMachineRejectsHandEditedStaleAndMissingBlocks()
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
        using var temporary = new TemporaryDirectory();
        var candidatePath = Path.Combine(temporary.Path, "echo-review.md");
        var emitted = environment.EchoVerify(["--emit", "--base", "baseline"]);
        Assert.Equal(0, emitted.ExitCode);

        File.WriteAllText(candidatePath, emitted.Output, new UTF8Encoding(false));
        var exact = environment.EchoVerify(["--file", candidatePath, "--base", "baseline"]);
        File.WriteAllText(
            candidatePath,
            emitted.Output.Replace("unresolved_subitems", "hand_modified", StringComparison.Ordinal),
            new UTF8Encoding(false));
        var modified = environment.EchoVerify(["--file", candidatePath, "--base", "baseline"]);
        File.WriteAllText(
            candidatePath,
            emitted.Output.Replace("git-sha256:baseline", "git-sha256:cccccccc", StringComparison.Ordinal),
            new UTF8Encoding(false));
        var stale = environment.EchoVerify(["--file", candidatePath, "--base", "baseline"]);
        File.Delete(candidatePath);
        var missing = environment.EchoVerify(["--file", candidatePath, "--base", "baseline"]);

        Assert.Equal(0, exact.ExitCode);
        Assert.All([modified, stale, missing], result => Assert.Equal(1, result.ExitCode));
        Assert.Contains("byte-match", modified.Error, StringComparison.Ordinal);
        Assert.Contains("byte-match", stale.Error, StringComparison.Ordinal);
        Assert.Contains("candidate file is missing", missing.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void SourceOnlyTheoryChangeRequiresTheCommittedProjection()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create(["docs/develop/theory/SYNTHETIC.md"]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.EchoVerify(["--base", "baseline", "--if-affected"]);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains(EchoResidualBlock.RelativePath, result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void EchoVerifyDefaultsToTheCommittedProjection()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var environment = new ProductionCliEnvironment(
            temporary.Path,
            new FakeRepositoryGateway(
                RawChangeSet.Create([EchoResidualBlock.RelativePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
        var emitted = environment.EchoVerify(["--emit", "--base", "baseline"]);
        var projection = Path.Combine(temporary.Path, EchoResidualBlock.RelativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(projection)!);
        File.WriteAllText(projection, emitted.Output, new UTF8Encoding(false));

        var result = environment.EchoVerify(["--base", "baseline", "--if-affected"]);

        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void EchoVerifySkipsMissingEvidenceOnlyWhenNoResidualInputChanged()
    {
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create(["README.md"]),
                null,
                null),
            new FakeLeanReportSource(null),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));

        var result = environment.EchoVerify(
            ["--file", "/absent/echo-review.md", "--base", "baseline", "--if-affected"]);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("ECHO_VERIFY_NOT_APPLICABLE\n", result.Output);
    }
}
