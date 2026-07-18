using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record CommandResult(bool Success, string Output, string Error);

internal sealed record ExplicitCommandResult(int ExitCode, string Output, string Error);

internal interface ICliEnvironment
{
    AdmissionOutcome Check(IReadOnlyList<string> arguments);

    AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments);

    CommandResult Coverage(IReadOnlyList<string> arguments);

    CommandResult DigestStatus(IReadOnlyList<string> arguments);

    CommandResult Ingest(IReadOnlyList<string> arguments);

    CommandResult Route(IReadOnlyList<string> arguments);

    CommandResult RecordGolden(IReadOnlyList<string> arguments);

    CommandResult SelfTest(IReadOnlyList<string> arguments);

    CommandResult GenerateLedger(IReadOnlyList<string> arguments);

    CommandResult AppendLedger(IReadOnlyList<string> arguments);

    CommandResult ReattestLedger(IReadOnlyList<string> arguments);

    CommandResult CleanLanes(IReadOnlyList<string> arguments);

    CommandResult Worktree(IReadOnlyList<string> arguments);

    CommandResult RenewC0(IReadOnlyList<string> arguments);

    ExplicitCommandResult VerifyConservative(IReadOnlyList<string> arguments);

    ExplicitCommandResult EvaluateConservativeCorpus(IReadOnlyList<string> arguments);
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
            console.WriteError(
                "USAGE: StrataLint c0-renew|check|clean-lanes|coverage|digest-status|ingest|golden-record|ledger-genesis|route|selftest|topology|worktree|ledger-append|ledger-reattest|verify-conservative|evaluate-conservative-corpus\n");
            return 2;
        }

        var tail = arguments.Skip(1).ToArray();
        return arguments[0] switch
        {
            "c0-renew" => RenderCommand(environment.RenewC0(tail), console),
            "check" => RenderAdmission(environment.Check(tail), console),
            "clean-lanes" => RenderCommand(environment.CleanLanes(tail), console),
            "coverage" => RenderCommand(environment.Coverage(tail), console),
            "digest-status" => RenderCommand(environment.DigestStatus(tail), console),
            "ingest" => RenderCommand(environment.Ingest(tail), console),
            "evaluate-conservative-corpus" =>
                RenderExplicit(environment.EvaluateConservativeCorpus(tail), console),
            "golden-record" => RenderCommand(environment.RecordGolden(tail), console),
            "ledger-genesis" => RenderCommand(environment.GenerateLedger(tail), console),
            "ledger-append" => RenderCommand(environment.AppendLedger(tail), console),
            "ledger-reattest" => RenderCommand(environment.ReattestLedger(tail), console),
            "route" => RenderCommand(environment.Route(tail), console),
            "selftest" => RenderCommand(environment.SelfTest(tail), console),
            "topology" => RenderTopology(environment.Topology(tail), console),
            "verify-conservative" => RenderExplicit(environment.VerifyConservative(tail), console),
            "worktree" => RenderCommand(environment.Worktree(tail), console),
            _ => UnknownCommand(arguments[0], console),
        };
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
        AdmissionOutcome.HumanReviewRequired required => RenderHumanReview(required, console),
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

        return 0;
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

    private static int RenderHumanReview(
        AdmissionOutcome.HumanReviewRequired required,
        ICliConsole console)
    {
        foreach (var diagnostic in required.Diagnostics.OrderBy(static item => item.Path, StringComparer.Ordinal))
        {
            console.WriteOutput(diagnostic.Render() + "\n");
        }

        console.WriteOutput($"HUMAN_REVIEW_REQUIRED count={required.Diagnostics.Length}\n");
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
        return result.Success ? 0 : 2;
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
