using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class DigestionCoverageTargetAligner
{
    internal static BackfillInventoryDocument Align(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        IReadOnlyDictionary<RepoPath, TruthState>? truthStates = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);

        var states = truthStates ?? LeanTruthStates.Resolve(snapshot, lean);
        var frozenStatements = FrozenStatementIndex.Create(
            FrozenStateCatalog.Load(snapshot),
            lean.Report);
        return document.WithDigestionSources(document.RequireDigestionSources()
            .Select(source => source with
            {
                Entries = source.Entries.Select(entry => entry with
                {
                    Coverage = entry.Coverage.Select(edge => edge with
                    {
                        TargetStatementId = CurrentEdgeValidator.Validate(
                            edge.Gid,
                            snapshot,
                            lean.Report,
                            states,
                            frozenStatements).TargetStatementId,
                    }).ToImmutableArray(),
                }).ToImmutableArray(),
            }).ToImmutableArray());
    }
}
