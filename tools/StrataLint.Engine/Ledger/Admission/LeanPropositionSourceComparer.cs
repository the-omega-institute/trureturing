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
        LeanAxiomReport candidateReport,
        FrozenStatementWitness? oldWitness = null)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(reanchoredPaths);
        ArgumentNullException.ThrowIfNull(baseState);
        ArgumentNullException.ThrowIfNull(candidateReport);
        try
        {
            return FindFailures(protectedBase, candidate, reanchoredPaths, baseState, candidateReport, oldWitness).IsEmpty;
        }
        catch (LeanSourceExtractionException)
        {
            return false;
        }
    }

    internal static ImmutableArray<RepoPath> FindFailures(RepositorySnapshot protectedBase,
        RepositorySnapshot candidate, ImmutableHashSet<RepoPath> paths, FrozenStateCatalog baseState,
        LeanAxiomReport candidateReport, FrozenStatementWitness? oldWitness = null)
    {
        var failures = ImmutableArray.CreateBuilder<RepoPath>();
        var (baseSources, candidateSources) = ParseSources(protectedBase, candidate);
        foreach (var path in paths.OrderBy(static path => path.Value, StringComparer.Ordinal))
        {
            try
            {
                if (!baseState.Records.TryGetValue(path, out var recorded)
                    || !candidateReport.Files.TryGetValue(path, out var current)
                    || !ModuleIsEquivalent(path, recorded, current, baseSources, candidateSources, oldWitness))
                    failures.Add(path);
            }
            catch (LeanSourceExtractionException) { failures.Add(path); }
        }
        return failures.ToImmutable();
    }

    private static bool ModuleIsEquivalent(RepoPath path, FrozenStateRecord recorded, LeanFileReport current,
        LeanSourceCatalog baseSources, LeanSourceCatalog candidateSources, FrozenStatementWitness? oldWitness)
    {
        if (oldWitness is not null && !recorded.Declarations.SequenceEqual(FrozenStateRecord.Project(current))
            && LeanAuthenticatedIndexAliases.AreEquivalent(path, recorded, current, baseSources, candidateSources, oldWitness))
            return true;
        return baseSources.ExtractPropositionSource(path, recorded.Declarations).AsSpan()
            .SequenceEqual(candidateSources.ExtractPropositionSource(path, FrozenStateRecord.Project(current)).AsSpan());
    }

}

internal enum LeanSourceExtractionFailure { UnsupportedSyntax, IndentedDeclaration, UnresolvedPrivateOwner }

internal sealed class LeanSourceExtractionException(
    string message,
    LeanSourceExtractionFailure failure = LeanSourceExtractionFailure.UnsupportedSyntax) : FormatException(message)
{
    internal LeanSourceExtractionFailure Failure { get; } = failure;
}
