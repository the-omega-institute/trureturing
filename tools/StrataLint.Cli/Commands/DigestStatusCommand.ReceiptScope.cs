using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class DigestStatusCommand
{
    private sealed record ReceiptGateScope(
        RawChangeSet Changes,
        Func<string, bool> IsBaseFactAffected);

    private static ReceiptGateScope ResolveReceiptGateScope(
        RepositorySnapshot current,
        RepositorySnapshot? baseline,
        LeanAxiomReport report,
        BackfillInventoryDocument document,
        RawChangeSet repositoryChanges)
    {
        var changes = baseline is null
            ? repositoryChanges
            : BackfillDeltaImpactResolver.Resolve(
                current,
                baseline,
                report,
                document,
                repositoryChanges).EvaluationChanges;
        var affectedPaths = changes.Paths
            .Select(static path => path.Value)
            .ToHashSet(StringComparer.Ordinal);
        return new ReceiptGateScope(changes, affectedPaths.Contains);
    }
}
