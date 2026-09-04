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
        var target = ParseTarget(arguments);
        if (target is null)
        {
            return Usage();
        }

        var ledgerDirectory = Path.Combine(
            repositoryRoot,
            FrozenLedgerChangeClassifier.AcceptedRoot.Replace(
                '/',
                Path.DirectorySeparatorChar));
        if (!Directory.Exists(ledgerDirectory))
        {
            return Invalid(
                $"frozen ledger is missing: {FrozenLedgerChangeClassifier.AcceptedRoot}");
        }

        try
        {
            var current = Decode(repository.ReadCurrent());
            var view = FrozenLedgerBaseViewReader.Read(current);
            return new ExplicitCommandResult(
                view.ActiveByPath.ContainsKey(target) ? 0 : 1,
                string.Empty,
                string.Empty);
        }
        catch (Exception exception)
        {
            return Invalid(exception.Message);
        }
    }

    private static RepoPath? ParseTarget(IReadOnlyList<string> arguments)
    {
        return arguments.Count == 2
            && string.Equals(arguments[0], "--target", StringComparison.Ordinal)
            && RepoPath.TryCreate(arguments[1], out var target)
                ? target
                : null;
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static ExplicitCommandResult Usage() => new(
        2,
        string.Empty,
        "USAGE: StrataLint ledger-frozen --target D5/.../*.lean\n");

    private static ExplicitCommandResult Invalid(string message) => new(
        2,
        string.Empty,
        $"LEDGER_FROZEN_INVALID {message}\n");
}
