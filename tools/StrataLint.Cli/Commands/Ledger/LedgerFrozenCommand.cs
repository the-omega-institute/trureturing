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
            || !RepoPath.TryCreate(arguments[1], out var target))
        {
            return new(2, string.Empty, "USAGE: StrataLint ledger-frozen --target D5/.../*.lean\n");
        }

        var ledgerDirectory = Path.Combine(
            repositoryRoot,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar));
        if (!Directory.Exists(ledgerDirectory))
        {
            return Invalid($"frozen ledger is missing: {FrozenLedgerChangeClassifier.AcceptedRoot}");
        }

        try
        {
            var decoded = SnapshotDecoder.Decode(repository.ReadCurrent());
            if (decoded is SnapshotDecodeOutcome.InfrastructureFailure failure)
            {
                return Invalid(failure.Message);
            }

            var snapshot = ((SnapshotDecodeOutcome.Decoded)decoded).Snapshot;
            var frozen = FrozenLedgerBaseViewReader.Read(snapshot).ActiveByPath.ContainsKey(target);
            return new ExplicitCommandResult(frozen ? 0 : 1, string.Empty, string.Empty);
        }
        catch (Exception exception)
        {
            return Invalid(exception.Message);
        }
    }

    private static ExplicitCommandResult Invalid(string message) =>
        new(2, string.Empty, $"LEDGER_FROZEN_INVALID {message}\n");
}
