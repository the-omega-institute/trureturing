using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class MathlibUpgradePropositionSourceDiagnostics
{
    internal static ImmutableArray<RepoPath> FindFailures(LeanSourceComparisonResult result) =>
        result.Failures.Select(failure => failure.Path).Distinct().ToImmutableArray();
}
