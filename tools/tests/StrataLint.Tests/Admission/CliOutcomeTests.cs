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
        var descriptor = RuleCatalog.Default.Descriptors.Single(item =>
            item.Id == RuleId.CreateKnown(22));
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
