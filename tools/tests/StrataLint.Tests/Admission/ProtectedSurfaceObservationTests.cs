using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ProtectedSurfaceObservationTests
{
    [Fact]
    public void AdmissionEngineReleasesProtectedSurfaceChangeWhenContentChecksPass()
    {
        var outcome = DecideProtectedSurfaceChange();

        Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(outcome);
    }

    [Fact]
    public void AdmissionEngineCarriesSl028ObservationIntoProtectedSurfaceChange()
    {
        var protectedChange = Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(
            DecideProtectedSurfaceChange());

        var observation = Assert.Single(protectedChange.Observations);
        Assert.Equal(RuleId.CreateKnown(28), observation.RuleId);
        Assert.Equal(AdmissionEffect.Observe, observation.AdmissionEffect);
        Assert.Equal(RuleFixture.DuplicateRightGid + ".lean", observation.Path);
    }

    [Fact]
    public void ProtectedSurfaceChangeRendersDeferredThenObservedLikeAdmitted()
    {
        var protectedChange = Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(
            DecideProtectedSurfaceChange());
        Assert.NotEmpty(protectedChange.ContentCertificate.DeferredRules);
        Assert.NotEmpty(protectedChange.Observations);

        var protectedRendering = Render(protectedChange);
        var admittedRendering = Render(new AdmissionOutcome.Admitted(
            protectedChange.ContentCertificate,
            protectedChange.Observations));
        var protectedDispositions = DispositionLines(protectedRendering.Output);
        var admittedDispositions = DispositionLines(admittedRendering.Output);

        Assert.Equal(0, admittedRendering.ExitCode);
        Assert.Equal(admittedDispositions, protectedDispositions);
        Assert.StartsWith("DEFERRED ", protectedDispositions[0], StringComparison.Ordinal);
        Assert.StartsWith("OBSERVED ", protectedDispositions[^1], StringComparison.Ordinal);
    }

    [Fact]
    public void ProtectedSurfaceChangeKeepsExitCodeThree()
    {
        var protectedChange = Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(
            DecideProtectedSurfaceChange());

        var rendering = Render(protectedChange);

        Assert.Equal(3, rendering.ExitCode);
    }

    private static AdmissionOutcome DecideProtectedSurfaceChange()
    {
        const string protectedPath = ".github/CODEOWNERS";
        var duplicatePath = RuleFixture.DuplicateRightGid + ".lean";
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.channel_monotone",
            RuleFixture.DuplicateStatementType);
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.dpi_defect",
            RuleFixture.DuplicateStatementType);
        fixture.AddDigestionCoverageTarget();
        fixture.Baseline[protectedPath] = "old owners\n";
        fixture.ForkPoint[protectedPath] = "old owners\n";
        fixture.Files[protectedPath] = "new owners\n";
        fixture.Files[duplicatePath] += "-- candidate delta\n";
        var changes = RawChangeSet.Create([protectedPath, duplicatePath]);
        var context = fixture.Build(changes);
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context)).Capability;
        var canonical = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(context.Current, context.Policy, changes));

        return AdmissionEngine.Decide(
            context.Policy,
            canonical.Capability,
            context.Lean,
            completed,
            context.MetaEvaluation);
    }

    private static (int ExitCode, string Output) Render(AdmissionOutcome outcome)
    {
        var console = new BufferedConsole();
        var exitCode = CliApplication.Run(
            ["check"],
            new StubCliEnvironment(outcome),
            console);
        return (exitCode, console.Output);
    }

    private static string[] DispositionLines(string output) => output
        .Split('\n', StringSplitOptions.RemoveEmptyEntries)
        .Where(static line => line.StartsWith("DEFERRED ", StringComparison.Ordinal)
            || line.StartsWith("OBSERVED ", StringComparison.Ordinal))
        .ToArray();
}
