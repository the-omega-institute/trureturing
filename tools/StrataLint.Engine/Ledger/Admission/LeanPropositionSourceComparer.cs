using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class LeanPropositionSourceComparer
{
    internal static bool AreEquivalent(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        ImmutableHashSet<RepoPath> reanchoredPaths,
        FrozenLedgerBaseView baseView,
        FrozenMaterialCatalog candidateCatalog)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(reanchoredPaths);
        ArgumentNullException.ThrowIfNull(baseView);
        ArgumentNullException.ThrowIfNull(candidateCatalog);
        try
        {
            var baseSources = LeanSourceCatalog.Parse(protectedBase);
            var candidateSources = LeanSourceCatalog.Parse(candidate);
            foreach (var path in reanchoredPaths.OrderBy(
                static path => path.Value,
                StringComparer.Ordinal))
            {
                if (!baseView.ActiveByPath.TryGetValue(path, out var recorded)
                    || !candidateCatalog.ByPath.TryGetValue(path, out var current))
                {
                    return false;
                }

                var baseFingerprint = baseSources.ExtractPropositionSource(
                    path,
                    recorded.Material.DeclarationStatementIds);
                var candidateFingerprint = candidateSources.ExtractPropositionSource(
                    path,
                    current.DeclarationStatementIds);
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
