using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class C0TrustRootReconcileCommand
{
    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 0)
            {
                throw new ArgumentException("USAGE: StrataLint c0-reconcile-trust-root");
            }

            var repository = new GitRepositoryGateway(repositoryRoot);
            var snapshot = Decode(repository.ReadCurrent());
            if (!snapshot.TryGetFile(RepositoryRules.TowerManifestPath, out var tower))
            {
                throw new FormatException("TOWER is missing");
            }

            var reconciled = C0CeremonyProjection.ReconcileTrustRoot(tower.RawBytes.AsSpan(), snapshot);
            var changed = !reconciled.SequenceEqual(tower.RawBytes) ? 1 : 0;
            if (changed != 0)
            {
                File.WriteAllBytes(
                    Path.Combine(repositoryRoot, RepositoryRules.TowerManifestPath),
                    reconciled.AsSpan());
            }

            var members = C0TowerProjection.ReadMembers(reconciled.AsSpan());
            if (!C0CeremonyProjection.TrustRootMatchesSnapshot(
                    members,
                    snapshot,
                    out var reason))
            {
                throw new InvalidOperationException(reason);
            }

            return new CommandResult(
                true,
                $"C0_TRUST_ROOT_RECONCILED changed_files={changed}\n",
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"C0_TRUST_ROOT_RECONCILE_FAILED [{exception.GetType().Name}] {exception.Message}\n");
        }
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
}
