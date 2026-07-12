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

    private static AdmissionOutcome Outcome(string fixture) => fixture switch
    {
        "admitted" => Admitted(),
        "rejected" => new AdmissionOutcome.RuleRejected(ImmutableArray.Create(
            new Diagnostic(
                RuleId.CreateKnown(6),
                "Generated status",
                DisplaySeverity.Error,
                AdmissionEffect.Block,
                "Blueprint/D5/S0/Carrier/Ring.md",
                "hand-written status badge is forbidden"))),
        "infrastructure" => new AdmissionOutcome.InfrastructureFailure("fixture tool failure"),
        "human" => new AdmissionOutcome.HumanReviewRequired(ImmutableArray.Create(
            new Diagnostic(
                RuleId.CreateKnown(22),
                "Meta bootstrap gate",
                DisplaySeverity.Warning,
                AdmissionEffect.HumanGate,
                "Meta/StrataLint/StrataLint.Engine/Coordinates/Gid.cs",
                "meta change requires external human review"))),
        _ => throw new ArgumentOutOfRangeException(nameof(fixture)),
    };

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
            context.MetaClear);
    }
}

internal sealed class StubCliEnvironment(AdmissionOutcome outcome) : ICliEnvironment
{
    public AdmissionOutcome Check(IReadOnlyList<string> arguments) => outcome;

    public AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments) =>
        new AdmissionTopologyOutcome.InfrastructureFailure("topology is not configured in this fixture");

    public CommandResult Route(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "route is not configured in this fixture");

    public CommandResult SelfTest(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "selftest is not configured in this fixture");

    public CommandResult GenerateLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger generation is not configured in this fixture");

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
