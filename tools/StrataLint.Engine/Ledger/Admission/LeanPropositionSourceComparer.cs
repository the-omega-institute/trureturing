using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class LeanPropositionSourceComparer
{
    internal static bool AreEquivalent(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        ImmutableHashSet<RepoPath> reanchoredPaths,
        FrozenStateCatalog baseState,
        LeanAxiomReport candidateReport)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(reanchoredPaths);
        ArgumentNullException.ThrowIfNull(baseState);
        ArgumentNullException.ThrowIfNull(candidateReport);
        try
        {
            var baseSources = LeanSourceCatalog.Parse(protectedBase);
            var candidateSources = LeanSourceCatalog.Parse(candidate);
            foreach (var path in reanchoredPaths.OrderBy(
                static path => path.Value,
                StringComparer.Ordinal))
            {
                if (!baseState.Records.TryGetValue(path, out var recorded)
                    || !candidateReport.Files.TryGetValue(path, out var current))
                {
                    return false;
                }

                var baseFingerprint = baseSources.ExtractPropositionSource(
                    path,
                    recorded.Declarations);
                var candidateFingerprint = candidateSources.ExtractPropositionSource(
                    path,
                    FrozenStateRecord.Project(current));
                if (!baseFingerprint.AsSpan().SequenceEqual(candidateFingerprint.AsSpan()))
                {
                    return false;
                }
            }

            return true;
        }
        catch (LeanSourceExtractionException)
        {
            return false;
        }
    }
}

internal sealed class LeanSourceExtractionException(string message) : FormatException(message);
