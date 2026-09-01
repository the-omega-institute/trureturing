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
        var reanchoredPaths = ReceiptReanchorPaths(protectedBase, candidate, changes, lean);
        if (reanchoredPaths is null)
        {
            return document;
        }

        return ApplyRecognizedReplacement(
            document,
            protectedBase,
            candidate,
            reanchoredPaths);
    }

    internal static BackfillInventoryDocument ApplyRecognizedReplacement(
        BackfillInventoryDocument document,
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        ImmutableHashSet<RepoPath> reanchoredPaths)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(protectedBase);
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(reanchoredPaths);
        if (!EffectiveLeanPins.TryRead(protectedBase, out var basePins)
            || !EffectiveLeanPins.TryRead(candidate, out var candidatePins)
            || basePins == candidatePins)
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
                            candidateStatements,
                            basePins!,
                            candidatePins!);
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

    private static ImmutableHashSet<RepoPath>? ReceiptReanchorPaths(
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
            var candidateView = FrozenLedgerBaseViewReader.Read(candidate);
            var catalog = FrozenContentAddress.BuildAdmissionCatalog(
                candidate,
                lean,
                states,
                adjacency,
                selectedPaths,
                candidateView.ActiveByPath);
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

            if (!EffectiveLeanPins.TryRead(protectedBase, out var basePins)
                || !EffectiveLeanPins.TryRead(candidate, out var candidatePins)
                || basePins == candidatePins)
            {
                return null;
            }

            return recognition.ReanchoredModulePaths;
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
        FrozenStatementIndex candidateStatements,
        EffectiveLeanPins basePins,
        EffectiveLeanPins candidatePins)
    {
        if (receipt.SourceSha256 != entry.Fingerprints.RawSha256
            || entry.CoverageGids.Count(gid => gid == receipt.Gid) != 1
            || entry.Receipts.Coverage.Count(item => item.Gid == receipt.Gid) != 1
            || !Gid.TryParse(receipt.Gid, out var gid)
            || !reanchoredPaths.Contains(gid.Path)
            || !baselineStatements.TryResolve(gid, out var baselineStatement, out _)
            || !candidateStatements.TryResolve(gid, out var candidateStatement, out _)
            || candidateStatement == baselineStatement
            || receipt.TargetStatementId != baselineStatement!.Value
                && receipt.TargetStatementId != candidateStatement!.Value)
        {
            return receipt;
        }

        var transition = new DigestionStatementIdHistoryEntry(
            baselineStatement.Value,
            basePins,
            candidatePins);
        var history = receipt.StatementIdHistory.IsDefault
            ? ImmutableArray<DigestionStatementIdHistoryEntry>.Empty
            : receipt.StatementIdHistory;
        if (!history.IsEmpty && history[^1] == transition)
        {
            return receipt.TargetStatementId == candidateStatement!.Value
                ? receipt
                : receipt with { TargetStatementId = candidateStatement.Value };
        }

        return receipt with
        {
            TargetStatementId = candidateStatement!.Value,
            StatementIdHistory = history.Add(transition),
        };
    }
}

internal static class MathlibUpgradePropositionSourceDiagnostics
{
    internal static ImmutableArray<RepoPath> FindFailures(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        ImmutableHashSet<RepoPath> reanchoredPaths,
        FrozenLedgerBaseView baseView,
        FrozenMaterialCatalog candidateCatalog)
    {
        var failures = ImmutableArray.CreateBuilder<RepoPath>();
        var baseSources = LeanSourceCatalog.Parse(protectedBase);
        var candidateSources = LeanSourceCatalog.Parse(candidate);
        foreach (var path in reanchoredPaths.OrderBy(
            static path => path.Value,
            StringComparer.Ordinal))
        {
            try
            {
                if (!baseView.ActiveByPath.TryGetValue(path, out var recorded)
                    || !candidateCatalog.ByPath.TryGetValue(path, out var current)
                    || !SourceBytesMatch(protectedBase, candidate, path)
                        && !baseSources.ExtractPropositionSource(
                                path,
                                recorded.Material.DeclarationStatementIds)
                            .AsSpan().SequenceEqual(candidateSources.ExtractPropositionSource(
                                path,
                                current.DeclarationStatementIds).AsSpan()))
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

    private static bool SourceBytesMatch(
        RepositorySnapshot protectedBase,
        RepositorySnapshot candidate,
        RepoPath path) =>
        protectedBase.Files.TryGetValue(path, out var baseFile)
        && candidate.Files.TryGetValue(path, out var candidateFile)
        && baseFile.RawBytes.AsSpan().SequenceEqual(candidateFile.RawBytes.AsSpan());
}
