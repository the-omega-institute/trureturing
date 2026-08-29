using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class MathlibUpgradeDigestionReanchor
{
    internal static BackfillInventoryDocument Apply(
        BackfillInventoryDocument document,
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        RawChangeSet changes,
        AcceptedLeanClosure lean)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(changes);
        ArgumentNullException.ThrowIfNull(lean);
        var reanchoredPaths = AuthorizedPaths(protectedBase, candidate, changes, lean);
        if (reanchoredPaths is null)
        {
            return document;
        }

        var baselineStatements = FrozenStatementIndex.Load(protectedBase);
        var candidateStatements = FrozenStatementIndex.Load(candidate);
        var changed = false;
        var sources = document.RequireDigestionSources()
            .Select(source => source with
            {
                Entries = source.Entries.Select(entry =>
                {
                    var coverage = entry.Receipts.Coverage.Select(receipt =>
                    {
                        var replacement = ReanchorReceipt(
                            entry,
                            receipt,
                            reanchoredPaths,
                            baselineStatements,
                            candidateStatements);
                        changed |= replacement != receipt;
                        return replacement;
                    }).ToImmutableArray();
                    return entry with
                    {
                        Receipts = entry.Receipts with { Coverage = coverage },
                    };
                }).ToImmutableArray(),
            })
            .ToImmutableArray();
        return changed ? document.WithDigestionSources(sources) : document;
    }

    private static ImmutableHashSet<RepoPath>? AuthorizedPaths(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        RawChangeSet changes,
        AcceptedLeanClosure lean)
    {
        try
        {
            var services = new ProductionFrozenLedgerAdmissionServices(
                repositoryRoot: ".",
                ImmutableHashSet<string>.Empty);
            var preparation = services.Prepare(candidate, protectedBase, changes);
            var states = LeanTruthStates.Resolve(candidate, lean);
            var adjacency = LeanImportAdjacency.Build(candidate, lean);
            var selectedPaths = states
                .Where(static item => item.Value is TruthState.Closed)
                .Select(static item => item.Key)
                .ToImmutableHashSet();
            var catalog = FrozenContentAddress.BuildAdmissionCatalog(
                candidate,
                lean,
                states,
                adjacency,
                selectedPaths,
                preparation.BaseView.ActiveByPath.ToDictionary(
                    static item => item.Key,
                    static item => item.Value.Material));
            var recognition = FrozenLedgerIncrementalReplacementRecognition.Recognize(
                preparation.BaseView,
                candidate,
                changes,
                preparation.DeltaEvents,
                catalog);
            if (recognition is null)
            {
                return null;
            }

            var authorization = new MathlibUpgradeFrozenLedgerReplacementAuthorization(
                protectedBase,
                candidate);
            var context = new FrozenLedgerReplacementAuthorizationContext(
                recognition,
                preparation.BaseView,
                catalog);
            if (!authorization.IsAuthorized(context))
            {
                return null;
            }

            preparation = preparation with { Replacement = recognition };
            var scope = FrozenLedgerAdmissionScope.Create(
                changes,
                preparation,
                states,
                adjacency);
            return FrozenLedger.ValidateAdmissionDelta(
                    preparation,
                    scope,
                    catalog,
                    authorization) is null
                ? recognition.ReanchoredModulePaths
                : null;
        }
        catch (Exception exception) when (exception is ArgumentException
            or FormatException
            or InvalidOperationException
            or KeyNotFoundException)
        {
            return null;
        }
    }

    private static DigestionCoverageReceipt ReanchorReceipt(
        DigestionLedgerEntry entry,
        DigestionCoverageReceipt receipt,
        ImmutableHashSet<RepoPath> reanchoredPaths,
        FrozenStatementIndex baselineStatements,
        FrozenStatementIndex candidateStatements)
    {
        if (receipt.SourceSha256 != entry.Fingerprints.RawSha256
            || entry.CoverageGids.Count(gid => gid == receipt.Gid) != 1
            || entry.Receipts.Coverage.Count(item => item.Gid == receipt.Gid) != 1
            || !Gid.TryParse(receipt.Gid, out var gid)
            || !reanchoredPaths.Contains(gid.Path)
            || !baselineStatements.TryResolve(gid, out var baselineStatement, out _)
            || receipt.TargetStatementId != baselineStatement!.Value
            || !candidateStatements.TryResolve(gid, out var candidateStatement, out _)
            || candidateStatement == baselineStatement)
        {
            return receipt;
        }

        return receipt with { TargetStatementId = candidateStatement!.Value };
    }
}
