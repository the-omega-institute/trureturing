using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class MathlibUpgradePropositionSourceDiagnostics
{
    internal static ImmutableArray<RepoPath> FindFailures(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        ImmutableHashSet<RepoPath> reanchoredPaths,
        FrozenStateCatalog baseState,
        LeanAxiomReport candidateReport)
    {
        var failures = ImmutableArray.CreateBuilder<RepoPath>();
        var (baseSources, candidateSources) = LeanPropositionSourceComparer.ParseSources(protectedBase, candidate);
        foreach (var path in reanchoredPaths.OrderBy(
            static path => path.Value,
            StringComparer.Ordinal))
        {
            try
            {
                if (!baseState.Records.TryGetValue(path, out var recorded)
                    || !candidateReport.Files.TryGetValue(path, out var current)
                    || !baseSources.ExtractPropositionSource(
                                path,
                                recorded.Declarations)
                            .AsSpan().SequenceEqual(candidateSources.ExtractPropositionSource(
                                path,
                                FrozenStateRecord.Project(current)).AsSpan()))
                {
                    failures.Add(path);
                }
            }
            catch (LeanSourceExtractionException)
            {
                failures.Add(path);
            }
        }

        return failures.ToImmutable();
    }

}
