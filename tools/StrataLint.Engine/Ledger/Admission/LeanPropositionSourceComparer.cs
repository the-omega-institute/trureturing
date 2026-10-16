using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class LeanPropositionSourceComparer
{
    internal static (LeanSourceCatalog Base, LeanSourceCatalog Candidate) ParseSources(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate)
    {
        var unchanged = protectedBase.Files
            .Where(pair => LeanClosureValidator.IsManagedLean(pair.Key.Value)
                && pair.Value.ContentWasRead && !pair.Value.RawBytes.IsDefault
                && candidate.Files.TryGetValue(pair.Key, out var current)
                && current.ContentWasRead && !current.RawBytes.IsDefault
                && pair.Value.RawBytes.AsSpan().SequenceEqual(current.RawBytes.AsSpan()))
            .Select(static pair => pair.Key).ToImmutableHashSet();
        return (LeanSourceCatalog.Parse(protectedBase, unchanged),
            LeanSourceCatalog.Parse(candidate, unchanged));
    }

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
            var (baseSources, candidateSources) = ParseSources(protectedBase, candidate);
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

internal enum LeanSourceExtractionFailure { UnsupportedSyntax, IndentedDeclaration, UnresolvedPrivateOwner }

internal sealed class LeanSourceExtractionException(
    string message,
    LeanSourceExtractionFailure failure = LeanSourceExtractionFailure.UnsupportedSyntax) : FormatException(message)
{
    internal LeanSourceExtractionFailure Failure { get; } = failure;
}
