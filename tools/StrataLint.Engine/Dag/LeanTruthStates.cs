using System.Collections.Immutable;

namespace StrataLint.Engine;

public static class LeanTruthStates
{
    public static ImmutableDictionary<RepoPath, TruthState> Resolve(
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);

        return snapshot.Files.Keys
            .Where(static path => LeanClosureValidator.IsManagedLean(path.Value))
            .ToImmutableDictionary(
                static path => path,
                path => AcyclicTruthDag.DeriveState(snapshot.Files[path], lean.Report));
    }
}
