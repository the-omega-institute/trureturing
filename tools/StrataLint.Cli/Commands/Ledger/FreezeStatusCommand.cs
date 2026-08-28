using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class FreezeStatusCommand
{
    internal static ExplicitCommandResult Run(
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 2
            || arguments[0] != "--path"
            || !RepoPath.TryCreate(arguments[1], out var path))
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                "USAGE: StrataLint freeze-status --path REPOSITORY_PATH\n");
        }

        try
        {
            var snapshot = SnapshotDecoder.Decode(repository.ReadCurrent()) switch
            {
                SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
                SnapshotDecodeOutcome.InfrastructureFailure failure =>
                    throw new InvalidOperationException(failure.Message),
            };
            var frozen = FrozenLedgerBaseViewReader.Read(snapshot)
                .ActiveByPath.ContainsKey(path);
            return new ExplicitCommandResult(
                frozen ? 0 : 1,
                $"{(frozen ? "FROZEN" : "NOT_FROZEN")} path={path.Value}\n",
                string.Empty);
        }
        catch (Exception exception)
        {
            return new ExplicitCommandResult(
                2,
                string.Empty,
                $"FREEZE_STATUS_UNAVAILABLE path={path.Value} detail={exception.Message}\n");
        }
    }
}
