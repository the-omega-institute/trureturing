using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CliOutcomeTests
{
    public static TheoryData<string, int, string, bool> Outcomes => new()
    {
        { "admitted", 0, "ADMITTED", false },
        { "rejected", 1, "RULE_REJECTED", false },
        { "infrastructure", 2, "INFRASTRUCTURE_FAILURE", true },
        { "human", 3, "HUMAN_REVIEW_REQUIRED", false },
        { "protected", 3, "PROTECTED_SURFACE_CHANGE", false },
    };

    [Theory]
    [MemberData(nameof(Outcomes))]
    public void CheckCommandMapsAllFourOutcomesToStableStreamsAndExitCodes(
        string fixture,
        int expectedExit,
        string marker,
        bool markerOnError)
    {
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(Outcome(fixture));

        var exitCode = CliApplication.Run(new[] { "check" }, environment, console);

        Assert.Equal(expectedExit, exitCode);
        Assert.Contains(marker, markerOnError ? console.Error : console.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(marker, markerOnError ? console.Output : console.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(0, "certificate\n", "")]
    [InlineData(1, "violation\n", "")]
    [InlineData(2, "", "infrastructure\n")]
    public void VerifyConservativePreservesItsThreeWayExitContract(
        int expectedExit,
        string output,
        string error)
    {
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(
            Admitted(),
            new ExplicitCommandResult(expectedExit, output, error));

        var exitCode = CliApplication.Run(
            new[] { "verify-conservative" },
            environment,
            console);

        Assert.Equal(expectedExit, exitCode);
        Assert.Equal(output, console.Output);
        Assert.Equal(error, console.Error);
    }

    [Fact]
    public void GoldenRecordDelegatesToTheAuthoringEnvironment()
    {
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(
            Admitted(),
            recordGolden: new CommandResult(true, "GOLDEN_RECORDED cases=110 changed_files=0\n", string.Empty));

        var exitCode = CliApplication.Run(["golden-record"], environment, console);

        Assert.Equal(0, exitCode);
        Assert.Equal("GOLDEN_RECORDED cases=110 changed_files=0\n", console.Output);
        Assert.Equal(string.Empty, console.Error);
    }

    [Fact]
    public void C0RenewDelegatesToTheCanonicalAuthoringEnvironment()
    {
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(
            Admitted(),
            renewC0: new CommandResult(
                true,
                "C0_RENEWED changed_files=2 admission=not-evaluated\n",
                string.Empty));

        var exitCode = CliApplication.Run(
            ["c0-renew", "--base", new string('a', 40)],
            environment,
            console);

        Assert.Equal(0, exitCode);
        Assert.Equal(
            "C0_RENEWED changed_files=2 admission=not-evaluated\n",
            console.Output);
        Assert.Equal(string.Empty, console.Error);
    }

    private static AdmissionOutcome Outcome(string fixture) => fixture switch
    {
        "admitted" => Admitted(),
        "rejected" => new AdmissionOutcome.RuleRejected(ImmutableArray.Create(
            new Diagnostic(
                RuleId.CreateKnown(6),
                "Generated status",
                DisplaySeverity.Error,
                AdmissionEffect.Block,
                RuleFixture.BlueprintPath,
                "hand-written status badge is forbidden"))),
        "infrastructure" => new AdmissionOutcome.InfrastructureFailure("fixture tool failure"),
        "human" => new AdmissionOutcome.HumanReviewRequired(ImmutableArray.Create(
            new Diagnostic(
                RuleId.CreateKnown(7),
                "Conflict-of-interest gate",
                DisplaySeverity.Warning,
                AdmissionEffect.HumanGate,
                RuleFixture.BlueprintPath,
                "legacy structured human-review outcome"))),
        "protected" => ProtectedSurfaceChange(),
        _ => throw new ArgumentOutOfRangeException(nameof(fixture)),
    };

    private static AdmissionOutcome ProtectedSurfaceChange()
    {
        const string path = RuleFixture.SyntheticProtectedPath;
        var admitted = Assert.IsType<AdmissionOutcome.Admitted>(Admitted());
        var bootstrap = Assert.IsType<BootstrapOutcome.HumanReviewRequired>(
            BootstrapGate.Evaluate(RawChangeSet.Create(new[] { path })));
        var descriptor = RuleCatalog.Default.Descriptors[21];
        return new AdmissionOutcome.ProtectedSurfaceChange(
            admitted.Certificate,
            bootstrap.ChangeSet,
            ImmutableArray.Create(new Diagnostic(
                descriptor.Id,
                descriptor.Title,
                descriptor.DisplaySeverity,
                descriptor.AdmissionEffect,
                path,
                "meta change requires external human review")));
    }

    private static AdmissionOutcome Admitted()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var context = fixture.Build();
        var registry = Assert.IsType<RegistryLoadOutcome.Accepted>(
            RegistryLoader.Load(
                Encoding.UTF8.GetBytes(TestRegistry.Canonical),
                Encoding.UTF8.GetBytes(TestRegistry.Domains)));
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context));
        var canonical = Assert.IsType<CanonicalizationOutcome.Accepted>(
            RepositoryCanonicalizer.Validate(context.Current, registry.Policy));
        return AdmissionEngine.Decide(
            registry.Policy,
            canonical.Capability,
            context.Lean,
            completed.Capability,
            context.MetaEvaluation);
    }
}

internal sealed class StubCliEnvironment(
    AdmissionOutcome outcome,
    ExplicitCommandResult? conservative = null,
    CommandResult? recordGolden = null,
    CommandResult? renewC0 = null) : ICliEnvironment
{
    public AdmissionOutcome Check(IReadOnlyList<string> arguments) => outcome;

    public AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments) =>
        new AdmissionTopologyOutcome.InfrastructureFailure("topology is not configured in this fixture");

    public CommandResult Coverage(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "coverage is not configured in this fixture");

    public CommandResult DigestStatus(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "digest status is not configured in this fixture");

    public CommandResult Ingest(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ingest is not configured in this fixture");

    public CommandResult Route(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "route is not configured in this fixture");

    public CommandResult RecordGolden(IReadOnlyList<string> arguments) =>
        recordGolden ?? new(false, string.Empty, "golden record is not configured in this fixture");

    public CommandResult RenewC0(IReadOnlyList<string> arguments) =>
        renewC0 ?? new(false, string.Empty, "C0 renewal is not configured in this fixture");

    public CommandResult SelfTest(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "selftest is not configured in this fixture");

    public CommandResult GenerateLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger generation is not configured in this fixture");

    public CommandResult AppendLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger append is not configured in this fixture");

    public CommandResult ReattestLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger reattest is not configured in this fixture");

    public CommandResult CleanLanes(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "clean lanes is not configured in this fixture");

    public CommandResult Worktree(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "worktree is not configured in this fixture");

    public ExplicitCommandResult VerifyConservative(IReadOnlyList<string> arguments) =>
        conservative ?? new ExplicitCommandResult(
            2,
            string.Empty,
            "verify-conservative is not configured in this fixture");

    public ExplicitCommandResult EvaluateConservativeCorpus(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "evaluate-conservative-corpus is not configured in this fixture");
}

internal sealed class BufferedConsole : ICliConsole
{
    private readonly StringBuilder output = new();
    private readonly StringBuilder error = new();

    internal string Output => output.ToString();

    internal string Error => error.ToString();

    public void WriteOutput(string value) => output.Append(value);

    public void WriteError(string value) => error.Append(value);
}
