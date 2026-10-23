using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class MathlibUpgradePropositionSourceDiagnostics
{
    internal static ImmutableArray<RepoPath> FindFailures(RepositorySnapshot protectedBase,
        RepositorySnapshot candidate, ImmutableHashSet<RepoPath> reanchoredPaths, FrozenStateCatalog baseState,
        LeanAxiomReport candidateReport, FrozenStatementWitness? oldWitness = null) =>
        LeanPropositionSourceComparer.FindFailures(protectedBase, candidate, reanchoredPaths,
            baseState, candidateReport, oldWitness);
}
