using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class CheckFidelityAttestationCommand
{
    internal static CommandResult Run(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            if (arguments.Count != 2
                || !string.Equals(arguments[0], "--attestation", StringComparison.Ordinal)
                || string.IsNullOrWhiteSpace(arguments[1]))
            {
                throw new FormatException(
                    "USAGE: StrataLint check-fidelity-attestation --attestation PATH");
            }

            var snapshot = Decode(repository.ReadCurrent());
            var report = leanReportSource.Load(snapshot);
            var evaluation = DigestionFidelityAttestationChecker.Verify(
                snapshot,
                report,
                arguments[1]);
            return new CommandResult(
                true,
                $"FIDELITY_ATTESTATION_VALID path={arguments[1]} "
                + $"clauses={evaluation.ClauseCount} "
                + $"undischarged={evaluation.UndischargedCount} "
                + $"failed_grader_traps={evaluation.FailedGraderTrapCount}\n",
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"FIDELITY_ATTESTATION_INVALID {exception.Message}\n");
        }
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new FormatException(failure.Message),
        };
}
