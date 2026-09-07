using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed partial class ProductionCliEnvironment
{
    public AdmissionTopologyOutcome Topology(IReadOnlyList<string> arguments)
    {
        try
        {
            return arguments.Count == 0
                ? repository.InspectAdmissionTopology()
                : new AdmissionTopologyOutcome.InfrastructureFailure("USAGE: StrataLint topology");
        }
        catch (Exception exception)
        {
            return new AdmissionTopologyOutcome.InfrastructureFailure(exception.Message);
        }
    }

    public CommandResult Coverage(IReadOnlyList<string> arguments) =>
        CoverageCommand.Run(repository, leanReportSource, arguments);

    public CommandResult DigestStatus(IReadOnlyList<string> arguments) =>
        scribeEmissionVerifier is null
            ? new CommandResult(
                false,
                string.Empty,
                "DIGEST_STATUS_INVALID Scribe emission verifier is unavailable\n")
            : DigestStatusCommand.Run(
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                arguments,
                atomHistorySource,
                timeProvider);

    public CommandResult ShowAtom(IReadOnlyList<string> arguments) =>
        ShowAtomCommand.Run(repository, arguments);

    public CommandResult AtomContext(IReadOnlyList<string> arguments) =>
        AtomContextCommand.Run(repository, arguments);

    public ExplicitCommandResult EchoVerify(IReadOnlyList<string> arguments) =>
        scribeEmissionVerifier is null
            ? new ExplicitCommandResult(
                2,
                string.Empty,
                "ECHO_VERIFY_INFRASTRUCTURE Scribe emission verifier is unavailable\n")
            : EchoVerifyCommand.Run(
                repositoryRoot,
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                arguments,
                atomHistorySource,
                timeProvider);

    public ExplicitCommandResult GateAuthority(IReadOnlyList<string> arguments) =>
        GateAuthorityCommand.Run(repositoryRoot, arguments);

    public ExplicitCommandResult FileMapConform(IReadOnlyList<string> arguments) =>
        FileMapConformCommand.Run(arguments, repositoryRoot);

    public ExplicitCommandResult DepositHeaderCheck(IReadOnlyList<string> arguments) =>
        DepositHeaderCheckCommand.Run(repository, leanReportSource, arguments);

    public ExplicitCommandResult LedgerFrozen(IReadOnlyList<string> arguments) =>
        LedgerFrozenCommand.Run(repositoryRoot, repository, arguments);

    public CommandResult Ingest(IReadOnlyList<string> arguments) =>
        IngestCommand.RunReportFree(
            repositoryRoot,
            repository,
            arguments,
            reportFreeIngestDependencies);

    public CommandResult AlignDigestionStatus(IReadOnlyList<string> arguments) =>
        scribeEmissionVerifier is null
            ? new CommandResult(
                false,
                string.Empty,
                "ALIGN_DIGESTION_STATUS_INVALID Scribe emission verifier is unavailable\n")
            : IngestCommand.Run(
                repositoryRoot,
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                arguments);

    public CommandResult CoverAtom(IReadOnlyList<string> arguments) =>
        scribeEmissionVerifier is null
            ? new CommandResult(
                false,
                string.Empty,
                "COVER_INVALID Scribe emission verifier is unavailable\n")
            : CoverAtomCommand.Run(
                repositoryRoot,
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                timeProvider.GetUtcNow(),
                arguments);

    public CommandResult QuarantineAtom(IReadOnlyList<string> arguments) =>
        QuarantineAtomCommand.Run(repositoryRoot, repository, arguments);

    public CommandResult SettleAtom(IReadOnlyList<string> arguments) =>
        SettleAtomCommand.Run(repositoryRoot, repository, arguments);

    public CommandResult DecomposeAtom(IReadOnlyList<string> arguments) =>
        DecomposeAtomCommand.Run(repositoryRoot, repository, arguments);

    public CommandResult AlignScribeReceipt(IReadOnlyList<string> arguments)
    {
        if (scribeEmissionVerifier is null)
        {
            return new CommandResult(
                false,
                string.Empty,
                "ALIGN_SCRIBE_RECEIPT_INVALID Scribe emission verifier is unavailable\n");
        }

        try
        {
            return AlignScribeReceiptCommand.Run(
                repositoryRoot,
                repository,
                leanReportSource,
                scribeEmissionVerifier,
                arguments);
        }
        catch (Exception exception)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"ALIGN_SCRIBE_RECEIPT_INVALID {exception.Message}\n");
        }
    }

    public CommandResult Route(IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 1)
            {
                return new CommandResult(false, string.Empty, "USAGE: StrataLint route MANIFEST|-\n");
            }

            var registry = LoadRegistry();
            var manifestBytes = arguments[0] == "-"
                ? ReadStandardInput()
                : ReadRepositoryFile(arguments[0]);
            var manifestOutcome = ManifestLoader.Load(manifestBytes);
            if (manifestOutcome is ManifestLoadOutcome.InfrastructureFailure manifestFailure)
            {
                return new CommandResult(false, string.Empty, $"INFRASTRUCTURE_FAILURE {manifestFailure.Message}\n");
            }

            var manifest = ((ManifestLoadOutcome.Loaded)manifestOutcome).Syntax;
            return RouteEngine.Route(registry.Policy, manifest) switch
            {
                RouteOutcome.Routed routed => RenderRoute(registry.Policy, routed),
                RouteOutcome.Rejected rejected => new CommandResult(
                    false,
                    string.Empty,
                    $"{rejected.RuleId.Value} route: {rejected.Message}\n"),
            };
        }
        catch (Exception exception)
        {
            return new CommandResult(false, string.Empty, $"INFRASTRUCTURE_FAILURE {exception.Message}\n");
        }
    }

    private CommandResult RenderRoute(ValidatedPolicy policy, RouteOutcome.Routed routed)
    {
        var capacityFailure = routed.Result.Gid.ToTarget() switch
        {
            Target.Formal formal => RouteCapacityPreflight.Evaluate(
                repository.ReadCurrent(),
                policy,
                routed.Result.Stratum,
                formal),
            Target.Blueprint blueprint => RouteCapacityPreflight.Evaluate(
                repository.ReadCurrent(),
                policy,
                routed.Result.Stratum,
                blueprint),
            _ => null,
        };
        if (capacityFailure is not null)
        {
            return new CommandResult(false, string.Empty, $"SL-003 route: {capacityFailure}\n");
        }

        return new CommandResult(
            true,
            JsonSerializer.Serialize(
                new
                {
                    gid = routed.Result.Gid.Value,
                    path = routed.Result.Path.Value,
                    stratum = routed.Result.Stratum?.ToString(),
                    skeleton = routed.Result.Skeleton,
                },
                RouteJsonOptions) + "\n",
            string.Empty);
    }
}
