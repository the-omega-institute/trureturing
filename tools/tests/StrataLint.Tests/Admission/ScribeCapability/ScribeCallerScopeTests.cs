using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CoverAtomDoesNotRequestScribeVerificationForChangedInputs()
    {
        var inputs = CoverWorld.Materialize(new CoverSpec());
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, inputs.Files);
        var verifier = new FakeScribeEmissionVerifier(null);
        var environment = new ProductionCliEnvironment(temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), CoverWorld.Raw(inputs.Files), CoverWorld.Raw(inputs.Baseline)),
            new FakeLeanReportSource(inputs.Report), verifier);

        var result = environment.CoverAtom(CoverArgs(inputs));

        Assert.True(result.Success, result.Error);
        Assert.Equal(0, verifier.CallCount);
        Assert.Empty(verifier.Scopes);
        var entry = Assert.Single(BackfillInventoryLoader.LoadRoot(temporary.Path).RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Equal([inputs.Gid], entry.CoverageGids.ToArray());
    }

    [Fact]
    public void DigestStatusScopeUsesTheExplicitRepositoryDelta()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var verifier = new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty);
        var changes = RawChangeSet.Create([RuleFixture.RingPath]);
        var environment = new ProductionCliEnvironment("/repo",
            new FakeRepositoryGateway(changes, Snapshot(fixture.Files), Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)), verifier, CoverWorld.TimeProvider);

        var result = environment.DigestStatus(["--json", "--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal([RuleFixture.RingPath], Assert.Single(verifier.Scopes).Paths.Select(path => path.Value).ToArray());
    }
    [Fact]
    public void CheckCurrentScopeReadsTheProvidedNulSeparatedManifest()
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.Files["Meta/ci-checks.json"] = CommonCheckRegistrationFixture.Manifest(
            "tools/StrataLint.Scribe/StrataLint.Scribe.csproj");
        var snapshot = Snapshot(fixture.Files);
        var report = Path.Combine(temporary.Path, "report.json");
        RawLeanReportArtifact.WriteFile(report, Decode(snapshot), LeanAxiomReport.Create(fixture.Reports));
        var paths = Path.Combine(temporary.Path, "paths");
        File.WriteAllText(paths, "Blueprint/D5/S0/Carrier/Probe.scribe.cs\0notes/selected.txt\0");
        var verifier = new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty);
        var environment = new ProductionCliEnvironment(temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), snapshot, Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null), verifier);

        var result = environment.CheckCurrent(["--candidate-lean-report", report, "--scribe-paths-from", paths]);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(["Blueprint/D5/S0/Carrier/Probe.scribe.cs", "notes/selected.txt"],
            Assert.Single(verifier.Scopes).Paths.Select(path => path.Value).ToArray());
    }

    [Theory]
    [InlineData(1, "describe red code=probe", false)]
    [InlineData(2, "HostConfiguration: probe", true)]
    public void CheckCurrentReportsScribeVerificationFailuresWithTheirOwnExitCode(
        int exitCode, string message, bool infrastructure)
    {
        using var temporary = new TemporaryDirectory();
        var fixture = new RuleFixture();
        fixture.Files["Meta/ci-checks.json"] = CommonCheckRegistrationFixture.Manifest(
            "tools/StrataLint.Scribe/StrataLint.Scribe.csproj");
        var snapshot = Snapshot(fixture.Files);
        var report = Path.Combine(temporary.Path, "report.json");
        RawLeanReportArtifact.WriteFile(report, Decode(snapshot), LeanAxiomReport.Create(fixture.Reports));
        var paths = Path.Combine(temporary.Path, "paths");
        File.WriteAllText(paths, "Blueprint/D5/S0/Carrier/Probe.scribe.cs\0");
        var environment = new ProductionCliEnvironment(temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), snapshot, Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null), new RejectingScribeEmissionVerifier(exitCode, message));

        var result = environment.CheckCurrent(["--candidate-lean-report", report, "--scribe-paths-from", paths]);

        Assert.Equal(exitCode, result.ExitCode);
        Assert.Contains(message, result.Error, StringComparison.Ordinal);
        Assert.Equal(infrastructure, result.Error.StartsWith("INFRASTRUCTURE_FAILURE ", StringComparison.Ordinal));
    }

    private sealed class RejectingScribeEmissionVerifier(int exitCode, string message) : IScribeEmissionVerifier
    {
        public VerifiedScribeEmissions Verify(RepositorySnapshot snapshot, LeanAxiomReport report, RawChangeSet? changes,
            FrozenStateCatalog? frozenState = null, FrozenStatementIndex? frozenStatements = null) =>
            throw new ScribeVerificationException(exitCode, message);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IngestAndRegistryRefreshSupplyTheirReceiptVerificationScope(bool refresh)
    {
        var fixture = RegistryRefreshFixture();
        fixture.Files[RuleFixture.RingPath] += "\n-- scoped change\n";
        using var temporary = new TemporaryDirectory();
        WriteDirectoryLedger(temporary.Path, fixture.Files);
        var verifier = new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty);
        var environment = new ProductionCliEnvironment(temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), Snapshot(fixture.Files), Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(LeanAxiomReport.Create(fixture.Reports)), verifier, CoverWorld.TimeProvider);

        var result = environment.AlignDigestionStatus(refresh
            ? ["--base", "baseline", "--refresh-source", "fixture-source", "--plan"]
            : ["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        var scope = Assert.Single(verifier.Scopes);
        Assert.Contains(RuleFixture.RingPath, scope.Paths.Select(path => path.Value));
        Assert.DoesNotContain("Blueprint/D5/S0/Test/Unrelated.scribe.cs",
            scope.Paths.Select(path => path.Value));
    }
}
