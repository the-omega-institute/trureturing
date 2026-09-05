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
    public void ProtectedSurfaceChangeRendersSl022ThenDeferredThenObservedLikeAdmitted()
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
        var sl022Offset = protectedRendering.Output.IndexOf("SL-022", StringComparison.Ordinal);
        var deferredOffset = protectedRendering.Output.IndexOf("DEFERRED ", StringComparison.Ordinal);
        var observedOffset = protectedRendering.Output.IndexOf("OBSERVED SL-028", StringComparison.Ordinal);
        Assert.True(
            sl022Offset >= 0
            && sl022Offset < deferredOffset
            && deferredOffset < observedOffset,
            $"Expected SL-022 -> DEFERRED -> OBSERVED, got:{Environment.NewLine}{protectedRendering.Output}");
    }

    [Fact]
    public void ProtectedSurfaceChangeKeepsExitCodeThree()
    {
        var protectedChange = Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(
            DecideProtectedSurfaceChange());

        var rendering = Render(protectedChange);

        Assert.Equal(3, rendering.ExitCode);
    }

    [Fact]
    public void ProtectedSurfaceChangeRendersObservationsByRuleIdPathThenMessage()
    {
        var seed = Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(
            DecideProtectedSurfaceChange());
        var protectedChange = new AdmissionOutcome.ProtectedSurfaceChange(
            seed.ContentCertificate,
            seed.ChangeSet,
            seed.Sl022Diagnostics,
            [
                new Diagnostic(
                    RuleId.CreateKnown(28),
                    "rule pair",
                    DisplaySeverity.Warning,
                    AdmissionEffect.Observe,
                    "same/rule.md",
                    "same rule message"),
                new Diagnostic(
                    RuleId.CreateKnown(3),
                    "path pair",
                    DisplaySeverity.Warning,
                    AdmissionEffect.Observe,
                    "zeta/path.md",
                    "path pair message"),
                new Diagnostic(
                    RuleId.CreateKnown(3),
                    "message pair",
                    DisplaySeverity.Warning,
                    AdmissionEffect.Observe,
                    "message/path.md",
                    "z message"),
                new Diagnostic(
                    RuleId.CreateKnown(3),
                    "rule pair",
                    DisplaySeverity.Warning,
                    AdmissionEffect.Observe,
                    "same/rule.md",
                    "same rule message"),
                new Diagnostic(
                    RuleId.CreateKnown(3),
                    "message pair",
                    DisplaySeverity.Warning,
                    AdmissionEffect.Observe,
                    "message/path.md",
                    "a message"),
                new Diagnostic(
                    RuleId.CreateKnown(3),
                    "path pair",
                    DisplaySeverity.Warning,
                    AdmissionEffect.Observe,
                    "alpha/path.md",
                    "path pair message"),
                new Diagnostic(
                    RuleId.CreateKnown(3),
                    "path pair",
                    DisplaySeverity.Warning,
                    AdmissionEffect.Observe,
                    "Alpha/path.md",
                    "path pair message"),
                new Diagnostic(
                    RuleId.CreateKnown(3),
                    "message pair",
                    DisplaySeverity.Warning,
                    AdmissionEffect.Observe,
                    "message/path.md",
                    "A message"),
            ]);

        var observationLines = Render(protectedChange).Output
            .Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Where(static line => line.StartsWith("OBSERVED ", StringComparison.Ordinal))
            .ToArray();

        Assert.Equal(
            [
                "OBSERVED SL-003 Alpha/path.md: path pair message",
                "OBSERVED SL-003 alpha/path.md: path pair message",
                "OBSERVED SL-003 message/path.md: A message",
                "OBSERVED SL-003 message/path.md: a message",
                "OBSERVED SL-003 message/path.md: z message",
                "OBSERVED SL-003 same/rule.md: same rule message",
                "OBSERVED SL-003 zeta/path.md: path pair message",
                "OBSERVED SL-028 same/rule.md: same rule message",
            ],
            observationLines);
    }

    [Fact]
    public void AdmissionEngineCarriesAllObservationsIntoProtectedSurfaceChange()
    {
        var protectedChange = Assert.IsType<AdmissionOutcome.ProtectedSurfaceChange>(
            DecideProtectedSurfaceChange(includeCapacityObservation: true));
        var duplicatePath = RuleFixture.DuplicateRightGid + ".lean";

        Assert.Contains(
            protectedChange.Observations,
            observation => observation.RuleId == RuleId.CreateKnown(3)
                && observation.AdmissionEffect is AdmissionEffect.Observe
                && observation.Path == duplicatePath);
        Assert.Contains(
            protectedChange.Observations,
            observation => observation.RuleId == RuleId.CreateKnown(28)
                && observation.AdmissionEffect is AdmissionEffect.Observe
                && observation.Path == duplicatePath);
    }

    private static AdmissionOutcome DecideProtectedSurfaceChange(
        bool includeCapacityObservation = false)
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
        fixture.Files[protectedPath] = "new owners\n";
        fixture.Files[duplicatePath] += includeCapacityObservation
            ? string.Concat(Enumerable.Repeat(
                "-- capacity pad\n",
                RepositoryRules.ArtifactSoftLineLimit))
            : "-- candidate delta\n";
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
