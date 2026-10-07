using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class LedgerFrozenCommand
{
    internal static ExplicitCommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        if (arguments.Count != 2
            || !string.Equals(arguments[0], "--target", StringComparison.Ordinal)
            || !RepoPath.TryCreate(arguments[1], out var target)
            || !FrozenStatePath.TryFromModulePath(target, out var statePath))
        {
            return new(2, string.Empty, "USAGE: StrataLint ledger-frozen --target D5/.../*.lean\n");
        }

        try
        {
            var decoded = SnapshotDecoder.Decode(repository.ReadCurrent(
                [":(literal)" + statePath.Value]));
            if (decoded is SnapshotDecodeOutcome.InfrastructureFailure failure)
            {
                return Invalid(failure.Message);
            }

            var snapshot = ((SnapshotDecodeOutcome.Decoded)decoded).Snapshot;
            if (!snapshot.TryGetFile(statePath.Value, out var file))
                return new ExplicitCommandResult(1, string.Empty, string.Empty);
            _ = FrozenStateRecordLoader.Load(file);
            return new ExplicitCommandResult(0, string.Empty, string.Empty);
        }
        catch (Exception exception)
        {
            return Invalid(exception.Message);
        }
    }

    private static ExplicitCommandResult Invalid(string message) =>
        new(2, string.Empty, $"LEDGER_FROZEN_INVALID {message}\n");
}
