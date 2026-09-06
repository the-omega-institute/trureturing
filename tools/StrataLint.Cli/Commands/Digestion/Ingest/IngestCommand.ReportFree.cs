using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    internal static CommandResult RunReportFree(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var options = ParseReportFreeArguments(arguments);
            var inputs = ReadInputs(
                repository,
                options.BaselineRevision,
                requireBaselineSourceMetadata: true);
            var (sourceIds, registrationPaths) = ResolveSources(inputs, options.Sources);
            var currentObservations = IngestPreservedExistingObserver.ObserveCurrent(
                inputs.CurrentDocument,
                inputs.BaselineDocument,
                sourceIds);

            var repositoryChanges = repository.ReadChanges(options.BaselineRevision);
            var plan = Plan(
                inputs,
                repositoryChanges,
                sourceIds,
                registrationPaths,
                DigestionIngestStrategy.AppendOnly);
            var prepared = Prepare(
                inputs,
                repositoryChanges,
                plan,
                report: null,
                sourceIds);
            var observations = IngestPreservedExistingObserver.Combine(
                currentObservations,
                prepared.Plan.PreservedExisting,
                IngestPreservedExistingObserver.ObserveAuthorityChanges(
                    prepared.CurrentDocument,
                    prepared.BaselineDocument,
                    prepared.Plan.Alignment,
                    prepared.PlannedScope,
                    prepared.RepositoryChanges,
                    sourceIds));
            var appendOnlyChanges = EffectiveChanges(
                prepared.CurrentRaw,
                prepared.PlannedRaw);
            var validationChanges = ReportFreeValidationChanges(
                appendOnlyChanges,
                prepared.RepositoryChanges,
                prepared.CurrentRaw,
                prepared.BaselineRaw);

            var evaluation = DigestionStatusEvaluator.EvaluateUncovered(
                DigestionEvaluationScope.ChangedSet,
                prepared.PlannedDocument,
                prepared.PlannedSnapshot,
                prepared.BaselineDocument,
                validationChanges,
                validationChanges,
                sourceIds,
                preservedAtomIds: prepared.CurrentDocument.RequireDigestionEntries()
                    .Select(static entry => entry.AtomId)
                    .ToImmutableHashSet(StringComparer.Ordinal));
            RequireValidReportFreeEvaluation(evaluation);
            var backfillObservations = DigestionBackfillValidation.RequireValidBackfillWithoutTruthAlignment(
                prepared.PlannedDocument,
                prepared.PlannedSnapshot,
                prepared.Baseline,
                LoadPolicy(prepared.PlannedSnapshot),
                validationChanges,
                casChanges: validationChanges,
                sourceIds: sourceIds);
            return WriteResult(
                repositoryRoot,
                prepared,
                prepared.PlannedRaw,
                prepared.PlannedDocument,
                evaluation,
                backfillObservations,
                observations,
                sourceIds);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"INGEST_INVALID {exception.Message}\n");
        }
    }

    private static void RequireValidReportFreeEvaluation(DigestionLedgerEvaluation evaluation)
    {
        if (evaluation.Findings.Length > 0)
        {
            throw new InvalidOperationException(
                "report-free digest status is invalid: "
                + string.Join("; ", evaluation.Findings));
        }
    }

    private static RawChangeSet ReportFreeValidationChanges(
        RawChangeSet appendOnlyChanges,
        RawChangeSet repositoryChanges,
        RawRepositorySnapshot current,
        RawRepositorySnapshot baseline)
    {
        var changes = appendOnlyChanges.Entries.ToDictionary(
            static change => change.Path.Value,
            static change => change.Kind,
            StringComparer.Ordinal);
        var currentPaths = current.Entries.Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        var baselinePaths = baseline.Entries.Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var change in repositoryChanges.Entries.Where(change =>
                     DigestionCasStore.IsCanonicalPath(change.Path.Value)
                     && currentPaths.Contains(change.Path.Value)
                     && !baselinePaths.Contains(change.Path.Value)))
        {
            changes[change.Path.Value] = change.Kind;
        }

        return RawChangeSet.CreateWithKinds(changes
            .OrderBy(static item => item.Key, StringComparer.Ordinal)
            .Select(static item => (item.Key, item.Value)));
    }

    private static CommandResult WriteResult(
        string repositoryRoot,
        IngestPreparation prepared,
        RawRepositorySnapshot finalRaw,
        BackfillInventoryDocument finalDocument,
        DigestionLedgerEvaluation evaluation,
        string backfillObservations,
        ImmutableArray<DigestionIngestObservation> observations = default,
        ImmutableHashSet<string>? sourceIds = null)
    {
        if (observations.IsDefault) observations = [];
        var ledgerUpdates = LedgerUpdates(prepared.CurrentRaw, finalRaw, sourceIds);
        RequireScopedCasObjects(prepared.Plan.CasObjects, finalDocument, sourceIds);
        if (prepared.Plan.Strategy == DigestionIngestStrategy.AppendOnly)
        {
            RequireAppendOnlyWriteSet(
                prepared.CurrentRaw,
                prepared.CurrentDocument,
                finalDocument,
                ledgerUpdates,
                prepared.Plan.CasObjects,
                prepared.Plan.AddedAtomIds,
                sourceIds);
        }
        var changed = ledgerUpdates.Length > 0;
        var openGenres = finalDocument.RequireDigestionSources()
            .Where(source => sourceIds is null || sourceIds.Contains(source.SourceId))
            .SelectMany(static source => source.GenreRegistryCheck.UnregisteredGenres.Select(token =>
                (source.SourceId, Token: token)))
            .OrderBy(static item => item.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item.Token, StringComparer.Ordinal)
            .ToImmutableArray();
        var createdCasPaths = WriteCasObjects(repositoryRoot, prepared.Plan.CasObjects);
        try
        {
            ApplyLedgerUpdatesAtomically(repositoryRoot, prepared.CurrentRaw, ledgerUpdates);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            RollbackCasObjects(createdCasPaths, exception);
            throw;
        }

        return new CommandResult(
            true,
            $"INGEST stale_acknowledged={prepared.Plan.StaleAcknowledged} "
            + $"residual_open_added={prepared.Plan.ResidualOpenAdded} "
            + $"coarse_fallbacks={prepared.Plan.Fallbacks.Length} "
            + $"open_genres={openGenres.Length} "
            + (prepared.Plan.Strategy == DigestionIngestStrategy.AppendOnly
                ? $"preserved_existing={observations.Length} "
                : string.Empty)
            + $"cas_objects_written={createdCasPaths.Length} "
            + $"ledger_changed={changed.ToString().ToLowerInvariant()}\n"
            + string.Concat(observations.Select(static observation =>
                $"INGEST_PRESERVED_EXISTING atom={observation.AtomId} "
                + $"source={observation.SourceId} kind={observation.Kind}\n"))
            + string.Concat(openGenres.Select(static item =>
                $"INGEST_OPEN_GENRE source={item.SourceId} "
                + $"token={DigestStatusCommand.RenderDetail(item.Token)}\n"))
            + string.Concat(prepared.Plan.Fallbacks.Select(static fallback =>
                $"INGEST_FALLBACK source={fallback.SourceId} reason={fallback.Reason}\n"))
            + string.Concat(prepared.SilentZeroWarnings.Select(static warning =>
                $"WARNING silent-zero-extraction source={warning.SourceId} "
                + $"path={warning.SourcePath}\n"))
            + prepared.CrossVolumeClearanceGaps
            + backfillObservations
            + DigestStatusCommand.RenderText(evaluation)
            + (prepared.Plan.Fallbacks.Length == 0
                ? string.Empty
                : $"INGEST_INCOMPLETE {prepared.Plan.Fallbacks.Length} source"
                    + (prepared.Plan.Fallbacks.Length == 1 ? string.Empty : "s")
                    + " registered without being atomised: "
                    + string.Join(", ", prepared.Plan.Fallbacks.Select(static item => item.SourceId))
                    + "\n"),
            string.Empty);
    }

    private static ReportFreeOptions ParseReportFreeArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count >= 2
            && arguments[0] == "--base"
            && !string.IsNullOrWhiteSpace(arguments[1]))
        {
            var sources = ImmutableArray.CreateBuilder<string>();
            for (var index = 2; index < arguments.Count; index += 2)
            {
                if (arguments[index] != "--source")
                    throw SourceUsage($"unexpected argument '{arguments[index]}'");
                if (index + 1 == arguments.Count)
                    throw SourceUsage("--source missing value");
                if (string.IsNullOrWhiteSpace(arguments[index + 1]))
                    throw SourceUsage($"invalid --source selector '{arguments[index + 1]}'");
                sources.Add(arguments[index + 1]);
            }
            return new ReportFreeOptions(arguments[1], sources.ToImmutable());
        }

        throw SourceUsage("invalid arguments");
    }

    private sealed record ReportFreeOptions(
        string BaselineRevision,
        ImmutableArray<string> Sources);

    private sealed record IngestInputs(
        RawRepositorySnapshot CurrentRaw,
        RawRepositorySnapshot BaselineRaw,
        RepositorySnapshot Current,
        RepositorySnapshot Baseline,
        BackfillInventoryDocument CurrentDocument,
        BackfillInventoryDocument BaselineDocument);

    private sealed record IngestPreparation(
        RawRepositorySnapshot CurrentRaw,
        RawRepositorySnapshot BaselineRaw,
        RepositorySnapshot Current,
        RepositorySnapshot Baseline,
        BackfillInventoryDocument CurrentDocument,
        BackfillInventoryDocument BaselineDocument,
        DigestionIngestPlan Plan,
        RawChangeSet RepositoryChanges,
        RawRepositorySnapshot PlannedRaw,
        RepositorySnapshot PlannedSnapshot,
        BackfillInventoryDocument PlannedDocument,
        RawChangeSet PlannedChanges,
        RawChangeSet PlannedEvaluationChanges,
        RawChangeSet PlannedReceiptVerificationChanges,
        RawChangeSet PlannedCasChanges,
        DigestionEvaluationScope PlannedScope,
        string CrossVolumeClearanceGaps,
        ImmutableArray<DigestionLedgerSource> SilentZeroWarnings);
}
