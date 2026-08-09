using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void EchoVerifyAcceptsProjectionFromBaseCommitWhenDerivedResidualIsUnchanged()
    {
        var result = RunRealGitEchoRoundTrip(changeResidualSummary: false);
        var objectFormat = result.BaseOid.Length == 40 ? "git-sha1:" : "git-sha256:";

        Assert.NotEqual(result.BaseOid, result.CandidateOid);
        Assert.Equal(0, result.Verification.ExitCode);
        Assert.Contains($"candidate={objectFormat}{result.CandidateOid}", result.Verification.Output, StringComparison.Ordinal);
        Assert.Contains($"base={objectFormat}{result.BaseOid}", result.Verification.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void EchoVerifyRejectsProjectionFromBaseCommitWhenDerivedResidualChanges()
    {
        var result = RunRealGitEchoRoundTrip(changeResidualSummary: true);

        Assert.NotEqual(result.BaseOid, result.CandidateOid);
        Assert.Equal(1, result.Verification.ExitCode);
        Assert.Contains("byte-match", result.Verification.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void EchoVerifyMachineRejectsChangedResidualTamperedDigestAndMissingBlocks()
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
        var digestIndex = emitted.Output.IndexOf("sha256:", StringComparison.Ordinal) + "sha256:".Length;
        var replacement = emitted.Output[digestIndex] == '0' ? '1' : '0';
        File.WriteAllText(
            candidatePath,
            emitted.Output[..digestIndex] + replacement + emitted.Output[(digestIndex + 1)..],
            new UTF8Encoding(false));
        var tamperedDigest = environment.EchoVerify(["--file", candidatePath, "--base", "baseline"]);
        File.Delete(candidatePath);
        var missing = environment.EchoVerify(["--file", candidatePath, "--base", "baseline"]);

        Assert.Equal(0, exact.ExitCode);
        Assert.All([modified, tamperedDigest, missing], result => Assert.Equal(1, result.ExitCode));
        Assert.Contains("byte-match", modified.Error, StringComparison.Ordinal);
        Assert.Contains("byte-match", tamperedDigest.Error, StringComparison.Ordinal);
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
                RawChangeSet.Create([string.Concat("docs/develop/", "theory/SYNTHETIC.md")]),
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

    private static RealGitEchoRoundTrip RunRealGitEchoRoundTrip(bool changeResidualSummary)
    {
        using var repository = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        WriteFixture(repository.Path, fixture.Files);
        ReviewRegressionTests.RunGit(repository.Path, "init");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.name", "StrataLint Tests");
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "echo base A");
        var baseOid = ReviewRegressionTests.RunGit(repository.Path, "rev-parse", "HEAD").Trim();

        var environment = new ProductionCliEnvironment(
            repository.Path,
            new GitRepositoryGateway(repository.Path),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty));
        var dirtyPath = Path.Combine(repository.Path, "echo-emit-sentinel.tmp");
        File.WriteAllText(dirtyPath, "emit against A\n", new UTF8Encoding(false));
        var emitted = environment.EchoVerify(["--emit", "--base", baseOid]);
        File.Delete(dirtyPath);
        Assert.Equal(0, emitted.ExitCode);

        if (changeResidualSummary)
        {
            var relativeBackfillPath = SyntheticBackfillFixture.AtomPath(
                fixture.Files["Meta/BACKFILL.yaml"]);
            var backfillPath = Path.Combine(repository.Path,
                relativeBackfillPath.Replace('/', Path.DirectorySeparatorChar));
            var backfill = File.ReadAllText(backfillPath, Encoding.UTF8).Replace(
                "  unresolved_subitems: []\n",
                "  unresolved_subitems:\n    - newly-open\n",
                StringComparison.Ordinal);
            Assert.NotEqual(
                SyntheticBackfillFixture.AtomText(
                    fixture.Files["Meta/BACKFILL.yaml"], "fixture-atom"),
                backfill);
            File.WriteAllText(backfillPath, backfill, new UTF8Encoding(false));
        }
        else
        {
            File.WriteAllText(Path.Combine(repository.Path, "README.md"), "base-only advance\n", new UTF8Encoding(false));
        }

        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "echo candidate B");
        var candidateOid = ReviewRegressionTests.RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        var candidatePath = Path.Combine(repository.Path, "echo-review.md");
        File.WriteAllText(candidatePath, emitted.Output, new UTF8Encoding(false));

        var verification = environment.EchoVerify(["--file", candidatePath, "--base", baseOid]);
        return new RealGitEchoRoundTrip(baseOid, candidateOid, verification);
    }

    private static void WriteFixture(string root, IReadOnlyDictionary<string, string> files)
    {
        foreach (var (relativePath, content) in SyntheticBackfillFixture.Expand(files))
        {
            var path = Path.Combine(root, relativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, content, new UTF8Encoding(false));
        }
    }

    private sealed record RealGitEchoRoundTrip(
        string BaseOid,
        string CandidateOid,
        ExplicitCommandResult Verification);
}
