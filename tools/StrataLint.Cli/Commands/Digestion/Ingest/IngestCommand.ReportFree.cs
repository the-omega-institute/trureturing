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
            var classification = IngestTruthAlignmentClassifier.ClassifyCurrent(
                options.ReportInputState,
                inputs.CurrentDocument,
                inputs.BaselineDocument,
                sourceIds);
            if (!classification.IsUncoveredOnly)
            {
                return TruthAlignmentRequired(classification);
            }

            var repositoryChanges = repository.ReadChanges(options.BaselineRevision);
            var plan = Plan(inputs, repositoryChanges, sourceIds, registrationPaths);
            var prepared = Prepare(
                inputs,
                repositoryChanges,
                plan,
                report: null,
                sourceIds);
            classification = IngestTruthAlignmentClassifier.ClassifyPlanned(
                prepared.CurrentDocument,
                prepared.BaselineDocument,
                prepared.PlannedDocument,
                prepared.Plan.Alignment,
                prepared.PlannedScope,
                prepared.RepositoryChanges,
                sourceIds);
            if (!classification.IsUncoveredOnly)
            {
                return TruthAlignmentRequired(classification);
            }

            var evaluation = DigestionStatusEvaluator.EvaluateUncovered(
                DigestionEvaluationScope.FullScan,
                prepared.PlannedDocument,
                prepared.PlannedSnapshot,
                prepared.BaselineDocument,
                prepared.PlannedReceiptVerificationChanges,
                prepared.PlannedCasChanges,
                sourceIds);
            RequireValidReportFreeEvaluation(evaluation);
            var backfillObservations = DigestionBackfillValidation.RequireValidBackfillWithoutTruthAlignment(
                prepared.PlannedDocument,
                prepared.PlannedSnapshot,
                prepared.Baseline,
                LoadPolicy(prepared.PlannedSnapshot),
                DigestionEvaluationScopes.ResolveChanges(
                    prepared.PlannedScope,
                    prepared.PlannedReceiptVerificationChanges),
                casChanges: prepared.PlannedCasChanges,
                sourceIds: sourceIds);
            return WriteResult(
                repositoryRoot,
                prepared,
                prepared.PlannedRaw,
                prepared.PlannedDocument,
                evaluation,
                backfillObservations,
                sourceIds);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"INGEST_INVALID {exception.Message}\n");
        }
    }

    private static CommandResult TruthAlignmentRequired(
        IngestTruthAlignmentClassification classification) =>
        new(
            false,
            string.Empty,
            "INGEST_TRUTH_ALIGNMENT_REQUIRED "
            + classification.Witness
            + "; run make align-digestion-status\n");

    private static void RequireValidReportFreeEvaluation(DigestionLedgerEvaluation evaluation)
    {
        if (evaluation.Findings.Length > 0)
        {
            throw new InvalidOperationException(
                "report-free digest status is invalid: "
                + string.Join("; ", evaluation.Findings));
        }
    }

    private static CommandResult WriteResult(
        string repositoryRoot,
        IngestPreparation prepared,
        RawRepositorySnapshot finalRaw,
        BackfillInventoryDocument finalDocument,
        DigestionLedgerEvaluation evaluation,
        string backfillObservations,
        ImmutableHashSet<string>? sourceIds = null)
    {
        var ledgerUpdates = LedgerUpdates(prepared.CurrentRaw, finalRaw, sourceIds);
        RequireScopedCasObjects(prepared.Plan.CasObjects, finalDocument, sourceIds);
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
            + $"cas_objects_written={createdCasPaths.Length} "
            + $"ledger_changed={changed.ToString().ToLowerInvariant()}\n"
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
        if (arguments.Count >= 4
            && arguments[0] == "--base"
            && !string.IsNullOrWhiteSpace(arguments[1])
            && arguments[2] == "--report-input-state"
            && Enum.TryParse<LeanReportInputState>(arguments[3], ignoreCase: true, out var state))
        {
            var sources = ImmutableArray.CreateBuilder<string>();
            for (var index = 4; index < arguments.Count; index += 2)
            {
                if (arguments[index] != "--source")
                    throw SourceUsage($"unexpected argument '{arguments[index]}'");
                if (index + 1 == arguments.Count)
                    throw SourceUsage("--source missing value");
                if (string.IsNullOrWhiteSpace(arguments[index + 1]))
                    throw SourceUsage($"invalid --source selector '{arguments[index + 1]}'");
                sources.Add(arguments[index + 1]);
            }
            return new ReportFreeOptions(arguments[1], state, sources.ToImmutable());
        }

        throw SourceUsage("invalid arguments");
    }

    private sealed record ReportFreeOptions(
        string BaselineRevision,
        LeanReportInputState ReportInputState,
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
