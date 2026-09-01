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

    // 判词产出却不可见即浮账(CLAUDE.md 第 20 条红线:允许 open,不允许浮账)。
    // admitted 路径此前把 Observe 判词全部丢掉——Observe 罕见时不显眼,而理论卷
    // 「尚未消化」改判 Observe 后,它就成了承重缺口:一个没人看得见的 open,与没有
    // 检测无异。本测试钉住「准入仍为 0,但观察项照样打印」。
    [Fact]
    public void AdmittedOutputCarriesNonBlockingObservationsInsteadOfDroppingThem()
    {
        var console = new BufferedConsole();
        var admitted = Assert.IsType<AdmissionOutcome.Admitted>(Admitted());
        var observation = new Diagnostic(
            RuleId.CreateKnown(16),
            "Backfill inventory",
            DisplaySeverity.Warning,
            AdmissionEffect.Observe,
            "Meta/BACKFILL.yaml",
            "theory document 'docs/develop/theory/PROBE.md' has no digestion source: run make ingest");
        var environment = new StubCliEnvironment(
            new AdmissionOutcome.Admitted(admitted.Certificate, [observation]));

        var exitCode = CliApplication.Run(["check"], environment, console);

        // 不阻断:退出码仍是 0。
        Assert.Equal(0, exitCode);
        Assert.Contains("ADMITTED", console.Output, StringComparison.Ordinal);
        // 但看得见:判词与其补救命令都在输出里。
        Assert.Contains("OBSERVED", console.Output, StringComparison.Ordinal);
        Assert.Contains("has no digestion source", console.Output, StringComparison.Ordinal);
        Assert.Contains("run make ingest", console.Output, StringComparison.Ordinal);
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
                "protected-surface change detected (SL-022)")),
            ImmutableArray<Diagnostic>.Empty);
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
    ExplicitCommandResult? fileMapConform = null,
    CommandResult? cleanLanes = null,
    ExplicitCommandResult? capacityAudit = null) : ICliEnvironment
{
    internal IReadOnlyList<string> CleanLanesArguments { get; private set; } = [];

    public AdmissionOutcome Check(IReadOnlyList<string> arguments) => outcome;

    public ExplicitCommandResult CapacityAudit(IReadOnlyList<string> arguments) =>
        capacityAudit ?? new(2, string.Empty, "capacity audit is not configured in this fixture");

    public AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments) =>
        new AdmissionTopologyOutcome.InfrastructureFailure("topology is not configured in this fixture");

    public CommandResult Coverage(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "coverage is not configured in this fixture");

    public CommandResult DigestStatus(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "digest status is not configured in this fixture");

    public CommandResult ShowAtom(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "show atom is not configured in this fixture");

    public ExplicitCommandResult EchoVerify(IReadOnlyList<string> arguments) =>
        echoVerify ?? new(2, string.Empty, "echo verify is not configured in this fixture");

    public ExplicitCommandResult GateAuthority(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "gate authority is not configured in this fixture");

    public ExplicitCommandResult FileMapConform(IReadOnlyList<string> arguments) =>
        fileMapConform ?? new(2, string.Empty, "filemap conformance is not configured in this fixture");

    public ExplicitCommandResult DepositHeaderCheck(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "deposit header check is not configured in this fixture");

    public CommandResult Ingest(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ingest is not configured in this fixture");

    public CommandResult AlignDigestionStatus(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "align digestion status is not configured in this fixture");

    public CommandResult CoverAtom(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "cover-atom is not configured in this fixture");

    public CommandResult AlignScribeReceipt(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "align-scribe-receipt is not configured in this fixture");

    public CommandResult EmitFormalizationReceipt(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "emit-formalization-receipt is not configured in this fixture");

    public CommandResult Route(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "route is not configured in this fixture");

    public CommandResult SelfTest(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "selftest is not configured in this fixture");

    public CommandResult RenderDag(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "dag rendering is not configured in this fixture");

    public CommandResult AppendLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger append is not configured in this fixture");

    public CommandResult RevokeLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "ledger revoke is not configured in this fixture");

    public CommandResult ReanchorMathlibLedger(IReadOnlyList<string> arguments) =>
        new(false, string.Empty, "mathlib ledger reanchor is not configured in this fixture");

    public ExplicitCommandResult TruthExport(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "truth export is not configured in this fixture");

    public ExplicitCommandResult TruthRelease(IReadOnlyList<string> arguments) =>
        new(2, string.Empty, "truth release is not configured in this fixture");

    public CommandResult CleanLanes(IReadOnlyList<string> arguments)
    {
        CleanLanesArguments = arguments.ToArray();
        return cleanLanes ?? new(false, string.Empty, "clean lanes is not configured in this fixture");
    }

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
