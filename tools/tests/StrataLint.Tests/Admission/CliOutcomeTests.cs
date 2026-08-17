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
        { "verification", 3, "HUMAN_REVIEW_REQUIRED", false },
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
    [InlineData(0, "ECHO_VERIFY_OK\n", "")]
    [InlineData(2, "", "ECHO_VERIFY_INFRASTRUCTURE report unavailable\n")]
    public void EchoVerifyPreservesProducerAndInfrastructureExitCodes(
        int expectedExit,
        string output,
        string error)
    {
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(
            Admitted(),
            echoVerify: new ExplicitCommandResult(expectedExit, output, error));

        var exitCode = CliApplication.Run(["echo-verify", "--emit", "--base", "baseline"], environment, console);

        Assert.Equal(expectedExit, exitCode);
        Assert.Equal(output, console.Output);
        Assert.Equal(error, console.Error);
    }

    [Fact]
    public void ValidateBlueprintPinsDelegatesToTheAuthoringEnvironment()
    {
        var unsupportedAnchor = string.Concat("pz", "g/proposition/9.2");
        var rejection = $"BLUEPRINT_PINS_REJECTED anchor '{unsupportedAnchor}' is not accepted\n";
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(
            Admitted(),
            blueprintPins: new ExplicitCommandResult(
                1,
                rejection,
                string.Empty));

        var exitCode = CliApplication.Run(
            ["validate-blueprint-pins", "pins.json"],
            environment,
            console);

        Assert.Equal(1, exitCode);
        Assert.Equal(rejection, console.Output);
        Assert.Equal(string.Empty, console.Error);
    }

    [Fact]
    public void TheoryCandidatesDelegatesToTheReadOnlyEnvironment()
    {
        var projected = new CommandResult(true, "{\"schema\":\"stratalint-theory-candidates-v1\"}\n", string.Empty);
        var console = new BufferedConsole();
        var environment = new StubCliEnvironment(Admitted(), theoryCandidates: projected);

        var exitCode = CliApplication.Run(
            ["theory-candidates", "--owner-override-file", "problem.txt"],
            environment,
            console);

        Assert.Equal(0, exitCode);
        Assert.Equal(projected.Output, console.Output);
        Assert.Empty(console.Error);
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
        "verification" => new AdmissionOutcome.ProtectedSurfaceVerificationRequired(ImmutableArray.Create(
            new Diagnostic(
                RuleId.CreateKnown(7),
                "Conflict-of-interest gate",
                DisplaySeverity.Warning,
                AdmissionEffect.HumanGate,
                RuleFixture.BlueprintPath,
                "protected-surface verification fixture outcome"))),
        "protected" => ProtectedSurfaceChange(),
        _ => throw new ArgumentOutOfRangeException(nameof(fixture)),
    };

    private static AdmissionOutcome ProtectedSurfaceChange()
    {
        const string path = RuleFixture.SyntheticProtectedPath;
        var admitted = Assert.IsType<AdmissionOutcome.Admitted>(Admitted());
        var bootstrap = Assert.IsType<BootstrapOutcome.ProtectedSurfaceVerificationRequired>(
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
                "protected-surface change detected (SL-022)")));
    }

    private static AdmissionOutcome Admitted()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var context = fixture.Build();
        var registry = RegistryLoadAssert.Accepted(
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
    ExplicitCommandResult? echoVerify = null,
    ExplicitCommandResult? blueprintPins = null,
    ExplicitCommandResult? fileMapConform = null,
    CommandResult? theoryCandidates = null) : ICliEnvironment
{
    public AdmissionOutcome Check(IReadOnlyList<string> arguments) => outcome;

    public AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments) =>
        new AdmissionTopologyOutcome.InfrastructureFailure("topology is not configured in this fixture");

    public CommandResult Coverage(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "coverage is not configured in this fixture");

    public CommandResult DigestStatus(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "digest status is not configured in this fixture");

    public CommandResult TheoryCandidates(IReadOnlyList<string> arguments) =>
        theoryCandidates ?? new(false, string.Empty, "theory candidates are not configured in this fixture");

    public CommandResult ShowAtom(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "show atom is not configured in this fixture");

    public ExplicitCommandResult EchoVerify(IReadOnlyList<string> arguments) =>
        echoVerify ?? new(2, string.Empty, "echo verify is not configured in this fixture");

    public ExplicitCommandResult GateAuthority(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "gate authority is not configured in this fixture");

    public ExplicitCommandResult FileMapConform(IReadOnlyList<string> arguments) =>
        fileMapConform ?? new(2, string.Empty, "filemap conformance is not configured in this fixture");

    public CommandResult Ingest(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ingest is not configured in this fixture");

    public CommandResult CoverAtom(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "cover-atom is not configured in this fixture");

    public CommandResult AlignScribeReceipt(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "align-scribe-receipt is not configured in this fixture");

    public CommandResult EmitFormalizationReceipt(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "emit-formalization-receipt is not configured in this fixture");

    public CommandResult Route(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "route is not configured in this fixture");

    public ExplicitCommandResult ValidateBlueprintPins(IReadOnlyList<string> arguments) =>
        blueprintPins ?? new(2, string.Empty, "blueprint pin validation is not configured in this fixture");

    public CommandResult SelfTest(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "selftest is not configured in this fixture");

    public CommandResult RenderDag(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "dag rendering is not configured in this fixture");

    public CommandResult AppendLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger append is not configured in this fixture");

    public CommandResult ReattestLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger reattest is not configured in this fixture");

    public CommandResult SupersedeLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger supersede is not configured in this fixture");

    public CommandResult SyncLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger sync is not configured in this fixture");

    public CommandResult CleanLanes(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "clean lanes is not configured in this fixture");

    public CommandResult AppendPerf(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "perf append is not configured in this fixture");

    public CommandResult PerfReport(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "perf report is not configured in this fixture");

    public CommandResult Worktree(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "worktree is not configured in this fixture");
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
