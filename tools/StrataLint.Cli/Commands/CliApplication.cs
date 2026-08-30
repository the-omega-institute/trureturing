using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record CommandResult(
    bool Success,
    string Output,
    string Error,
    int? ExitCode = null);

internal sealed record ExplicitCommandResult(int ExitCode, string Output, string Error);

internal interface ICliEnvironment
{
    ExplicitCommandResult CapacityAudit(IReadOnlyList<string> arguments);

    AdmissionOutcome Check(IReadOnlyList<string> arguments);

    AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments);

    CommandResult Coverage(IReadOnlyList<string> arguments);

    CommandResult DigestStatus(IReadOnlyList<string> arguments);

    CommandResult ShowAtom(IReadOnlyList<string> arguments);

    CommandResult ReviewEnvelope(IReadOnlyList<string> arguments);

    ExplicitCommandResult EchoVerify(IReadOnlyList<string> arguments);

    ExplicitCommandResult GateAuthority(IReadOnlyList<string> arguments);

    ExplicitCommandResult FileMapConform(IReadOnlyList<string> arguments);

    ExplicitCommandResult DepositHeaderCheck(IReadOnlyList<string> arguments);

    CommandResult Ingest(IReadOnlyList<string> arguments);

    CommandResult AlignDigestionStatus(IReadOnlyList<string> arguments);

    CommandResult CoverAtom(IReadOnlyList<string> arguments);

    CommandResult AlignScribeReceipt(IReadOnlyList<string> arguments);

    CommandResult EmitFormalizationReceipt(IReadOnlyList<string> arguments);

    CommandResult Route(IReadOnlyList<string> arguments);

    CommandResult SelfTest(IReadOnlyList<string> arguments);

    CommandResult RenderDag(IReadOnlyList<string> arguments);

    CommandResult AppendLedger(IReadOnlyList<string> arguments);

    CommandResult RevokeLedger(IReadOnlyList<string> arguments);

    ExplicitCommandResult TruthExport(IReadOnlyList<string> arguments);

    ExplicitCommandResult TruthRelease(IReadOnlyList<string> arguments);

    CommandResult CleanLanes(IReadOnlyList<string> arguments);

    CommandResult Worktree(IReadOnlyList<string> arguments);

}

internal interface ICliConsole
{
    void WriteOutput(string value);

    void WriteError(string value);
}

internal sealed class SystemCliConsole : ICliConsole
{
    public void WriteOutput(string value) => Console.Out.Write(value);

    public void WriteError(string value) => Console.Error.Write(value);
}

internal static class CliApplication
{
    // 这张表是动词的唯一真源:dispatch 查它,USAGE 由它渲染,`CliVerbLinkageTests` 也据它
    // 判 Makefile 与脚本里的调用是否悬空。此前 USAGE 是手抄的第二份清单,既包含悬空
    // 动词,又漏掉了已实现的动词。
    private static readonly ImmutableDictionary<
        string,
        Func<ICliEnvironment, string[], ICliConsole, int>> Handlers =
        new Dictionary<string, Func<ICliEnvironment, string[], ICliConsole, int>>(StringComparer.Ordinal)
        {
            ["align-digestion-status"] = static (environment, tail, console) =>
                RenderCommand(environment.AlignDigestionStatus(tail), console),
            ["align-scribe-receipt"] = static (environment, tail, console) =>
                RenderCommand(environment.AlignScribeReceipt(tail), console),
            ["capacity-audit"] = static (environment, tail, console) =>
                RenderExplicit(environment.CapacityAudit(tail), console),
            ["check"] = static (environment, tail, console) =>
                RenderAdmission(environment.Check(tail), console),
            ["clean-lanes"] = static (environment, tail, console) =>
                RenderCommand(environment.CleanLanes(tail), console),
            ["coverage"] = static (environment, tail, console) =>
                RenderCommand(environment.Coverage(tail), console),
            ["cover-atom"] = static (environment, tail, console) =>
                RenderCommand(environment.CoverAtom(tail), console),
            ["dag-render"] = static (environment, tail, console) =>
                RenderCommand(environment.RenderDag(tail), console),
            ["deposit-header-check"] = static (environment, tail, console) =>
                RenderExplicit(environment.DepositHeaderCheck(tail), console),
            ["digest-status"] = static (environment, tail, console) =>
                RenderCommand(environment.DigestStatus(tail), console),
            ["echo-verify"] = static (environment, tail, console) =>
                RenderExplicit(environment.EchoVerify(tail), console),
            ["emit-formalization-receipt"] = static (environment, tail, console) =>
                RenderCommand(environment.EmitFormalizationReceipt(tail), console),
            ["gate-authority"] = static (environment, tail, console) =>
                RenderExplicit(environment.GateAuthority(tail), console),
            ["filemap-conform"] = static (environment, tail, console) =>
                RenderExplicit(environment.FileMapConform(tail), console),
            ["ingest"] = static (environment, tail, console) =>
                RenderCommand(environment.Ingest(tail), console),
            ["ledger-append"] = static (environment, tail, console) =>
                RenderCommand(environment.AppendLedger(tail), console),
            ["ledger-revoke"] = static (environment, tail, console) =>
                RenderCommand(environment.RevokeLedger(tail), console),
            ["review-envelope"] = static (environment, tail, console) =>
                RenderCommand(environment.ReviewEnvelope(tail), console),
            ["route"] = static (environment, tail, console) =>
                RenderCommand(environment.Route(tail), console),
            ["selftest"] = static (environment, tail, console) =>
                RenderCommand(environment.SelfTest(tail), console),
            ["show-atom"] = static (environment, tail, console) =>
                RenderCommand(environment.ShowAtom(tail), console),
            ["topology"] = static (environment, tail, console) =>
                RenderTopology(environment.Topology(tail), console),
            ["truth-export"] = static (environment, tail, console) =>
                RenderExplicit(environment.TruthExport(tail), console),
            ["truth-release"] = static (environment, tail, console) =>
                RenderExplicit(environment.TruthRelease(tail), console),
            ["worktree"] = static (environment, tail, console) =>
                RenderCommand(environment.Worktree(tail), console),
        }.ToImmutableDictionary(StringComparer.Ordinal);

    internal static ImmutableArray<string> ImplementedCommands { get; } =
        [.. Handlers.Keys.Order(StringComparer.Ordinal)];

    private static string Usage =>
        "USAGE: StrataLint " + string.Join('|', ImplementedCommands) + "\n";

    internal static int Run(
        IReadOnlyList<string> arguments,
        ICliEnvironment environment,
        ICliConsole console)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(environment);
        ArgumentNullException.ThrowIfNull(console);
        try
        {
            return RunCore(arguments, environment, console);
        }
        catch (Exception exception)
        {
            try
            {
                console.WriteError($"INFRASTRUCTURE_FAILURE output: {exception.Message}\n");
            }
            catch (Exception outputException) when (outputException is IOException or ObjectDisposedException)
            {
                // The exit code remains the final fail-closed signal when both streams fail.
            }

            return 2;
        }
    }

    private static int RunCore(
        IReadOnlyList<string> arguments,
        ICliEnvironment environment,
        ICliConsole console)
    {
        if (arguments.Count == 0)
        {
            console.WriteError(Usage);
            return 2;
        }

        var tail = arguments.Skip(1).ToArray();
        return Handlers.TryGetValue(arguments[0], out var handler)
            ? handler(environment, tail, console)
            : UnknownCommand(arguments[0], console);
    }

    private static int RenderTopology(AdmissionTopologyOutcome outcome, ICliConsole console)
    {
        switch (outcome)
        {
            case AdmissionTopologyOutcome.BootstrapNotActive bootstrap:
                console.WriteOutput(
                    $"BOOTSTRAP-NOT-ACTIVE:baseline gate 尚未注入 {bootstrap.DefaultBranch},当前非机器门控态,须人类可信注入(D5-T0017)\n");
                return 3;
            case AdmissionTopologyOutcome.SteadyStateActive active:
                console.WriteOutput(
                    $"STEADY-STATE-ACTIVE:dev-baseline workflow 已注入 {active.DefaultBranch};required_status_checks/enforce_admins 仍须外部核验(D5-T0017)\n");
                return 0;
            case AdmissionTopologyOutcome.InfrastructureFailure failure:
                console.WriteError($"INFRASTRUCTURE_FAILURE topology: {failure.Message}\n");
                return 2;
            default:
                throw new InvalidOperationException("unknown admission topology outcome");
        }
    }

    private static int RenderAdmission(AdmissionOutcome outcome, ICliConsole console) => outcome switch
    {
        AdmissionOutcome.Admitted admitted => RenderAdmitted(admitted, console),
        AdmissionOutcome.RuleRejected rejected => RenderRejected(rejected, console),
        AdmissionOutcome.InfrastructureFailure failure => RenderInfrastructureFailure(failure, console),
        AdmissionOutcome.ProtectedSurfaceVerificationRequired verification =>
            RenderProtectedSurfaceVerification(verification, console),
        AdmissionOutcome.ProtectedSurfaceChange protectedChange =>
            RenderProtectedSurfaceChange(protectedChange, console),
    };

    private static int RenderAdmitted(AdmissionOutcome.Admitted admitted, ICliConsole console)
    {
        console.WriteOutput(
            $"ADMITTED {admitted.Certificate.Fingerprint} canonical={admitted.Certificate.CanonicalSha256}\n");
        foreach (var deferred in admitted.Certificate.DeferredRules)
        {
            console.WriteOutput(
                $"DEFERRED {deferred.RuleId.Value} case={deferred.CaseId.Value} {deferred.Title}\n");
        }

        // 非阻断的观察项照样打印。判词产出却不可见即浮账(CLAUDE.md 第 20 条红线:
        // 允许 open,不允许浮账),而此前本路径把 Observe 判词全部丢掉——在 Observe
        // 罕见时不显眼,理论卷「尚未消化」改判 Observe 后它就成了承重缺口。
        RenderObservations(admitted.Observations, console);

        return 0;
    }

    private static void RenderObservations(
        ImmutableArray<Diagnostic> observations,
        ICliConsole console)
    {
        foreach (var observation in observations
            .OrderBy(static item => item.RuleId.Value, StringComparer.Ordinal)
            .ThenBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.Message, StringComparer.Ordinal))
        {
            console.WriteOutput("OBSERVED " + observation.Render() + "\n");
        }
    }

    private static int RenderRejected(AdmissionOutcome.RuleRejected rejected, ICliConsole console)
    {
        foreach (var diagnostic in rejected.Diagnostics
            .OrderBy(static item => item.RuleId.Value, StringComparer.Ordinal)
            .ThenBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.Message, StringComparer.Ordinal))
        {
            console.WriteOutput(diagnostic.Render() + "\n");
        }

        console.WriteOutput($"RULE_REJECTED count={rejected.Diagnostics.Length}\n");
        return 1;
    }

    private static int RenderInfrastructureFailure(
        AdmissionOutcome.InfrastructureFailure failure,
        ICliConsole console)
    {
        console.WriteError($"INFRASTRUCTURE_FAILURE {failure.Message}\n");
        return 2;
    }

    private static int RenderProtectedSurfaceVerification(
        AdmissionOutcome.ProtectedSurfaceVerificationRequired verification,
        ICliConsole console)
    {
        foreach (var diagnostic in verification.Diagnostics
            .OrderBy(static item => item.Path, StringComparer.Ordinal))
        {
            console.WriteOutput(diagnostic.Render() + "\n");
        }

        console.WriteOutput($"HUMAN_REVIEW_REQUIRED count={verification.Diagnostics.Length}\n");
        return 3;
    }

    private static int RenderProtectedSurfaceChange(
        AdmissionOutcome.ProtectedSurfaceChange protectedChange,
        ICliConsole console)
    {
        foreach (var diagnostic in protectedChange.Sl022Diagnostics
            .OrderBy(static item => item.Path, StringComparer.Ordinal))
        {
            console.WriteOutput(diagnostic.Render() + "\n");
        }

        foreach (var deferred in protectedChange.ContentCertificate.DeferredRules)
        {
            console.WriteOutput(
                $"DEFERRED {deferred.RuleId.Value} case={deferred.CaseId.Value} {deferred.Title}\n");
        }

        RenderObservations(protectedChange.Observations, console);

        console.WriteOutput(
            $"PROTECTED_SURFACE_CHANGE count={protectedChange.Sl022Diagnostics.Length} "
            + $"content={protectedChange.ContentCertificate.Fingerprint} "
            + $"canonical={protectedChange.ContentCertificate.CanonicalSha256}\n");
        return 3;
    }

    private static int RenderCommand(CommandResult result, ICliConsole console)
    {
        if (result.Output.Length > 0) console.WriteOutput(result.Output);
        if (result.Error.Length > 0) console.WriteError(result.Error);
        var exitCode = result.ExitCode ?? (result.Success ? 0 : 2);
        if (exitCode is < 0 or > 255 || result.Success != (exitCode == 0))
        {
            throw new InvalidOperationException("command returned an invalid exit code");
        }

        return exitCode;
    }

    private static int RenderExplicit(ExplicitCommandResult result, ICliConsole console)
    {
        if (result.ExitCode is < 0 or > 2)
        {
            throw new InvalidOperationException("explicit command returned an invalid exit code");
        }

        if (result.Output.Length > 0) console.WriteOutput(result.Output);
        if (result.Error.Length > 0) console.WriteError(result.Error);
        return result.ExitCode;
    }

    private static int UnknownCommand(string command, ICliConsole console)
    {
        console.WriteError($"UNKNOWN_COMMAND {command}\n");
        return 2;
    }
}
