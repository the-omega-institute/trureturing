using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    private static CommandResult RenderAlignmentPlan(
        string repositoryRoot,
        string baselineRevision,
        IngestPreparation prepared,
        BackfillInventoryDocument finalDocument,
        ImmutableArray<LedgerUpdate> ledgerUpdates,
        DigestionLedgerEvaluation evaluation,
        DigestionEvaluationScope evaluationScope,
        string backfillObservations)
    {
        var pendingCas = ReadPendingCasObjects(repositoryRoot, prepared.Plan.CasObjects);
        if (ledgerUpdates.Length > 0)
        {
            RequireLedgerUnchanged(repositoryRoot, prepared.CurrentRaw);
        }

        var current = prepared.CurrentRaw.Entries.ToDictionary(
            static entry => entry.Path, StringComparer.Ordinal);
        var writes = pendingCas.Select(item => new
        {
            domain = "cas",
            action = "create",
            path = item.Object.RelativePath,
            before = AlignmentFileValue(null),
            after = AlignmentFileValue(item.Object.Bytes),
            durability_order = (int?)null,
        }).Concat(ledgerUpdates.Select(update =>
        {
            var before = current.TryGetValue(update.Path, out var entry)
                ? (ImmutableArray<byte>?)entry.Bytes : null;
            return new
            {
                domain = "ledger",
                action = before is null ? "create" : update.Bytes is null ? "delete" : "change",
                path = update.Path,
                before = AlignmentFileValue(before),
                after = AlignmentFileValue(update.Bytes),
                durability_order = (int?)update.DurabilityOrder,
            };
        }));
        var output = new
        {
            schema = "digestion-alignment-plan-v1",
            baseline_revision = baselineRevision,
            applied = false,
            writes,
            validation = new
            {
                fixed_point = "converged",
                scope = evaluationScope.ToString(),
                lean = "accepted",
                scribe = "accepted",
                backfill = "accepted",
            },
            diagnostics = new
            {
                cross_volume_clearance_gaps = prepared.CrossVolumeClearanceGaps,
                backfill_observations = backfillObservations,
                silent_zero_sources = prepared.SilentZeroWarnings.Select(static source => new
                {
                    source_id = source.SourceId,
                    source_path = source.SourcePath,
                }),
                fallback_sources = prepared.Plan.Fallbacks.Select(static fallback => new
                {
                    source_id = fallback.SourceId,
                    reason = fallback.Reason,
                }),
                open_genres = finalDocument.RequireDigestionSources()
                    .SelectMany(static source => source.GenreRegistryCheck.UnregisteredGenres
                        .Select(token => new { source_id = source.SourceId, token }))
                    .OrderBy(static item => item.source_id, StringComparer.Ordinal)
                    .ThenBy(static item => item.token, StringComparer.Ordinal),
                digestion_status_text = DigestStatusCommand.RenderText(evaluation),
            },
        };
        return new CommandResult(true, JsonSerializer.Serialize(output) + "\n", string.Empty);
    }

    private static object? AlignmentFileValue(ImmutableArray<byte>? bytes) => bytes is { } value
        ? new
        {
            byte_length = value.Length,
            sha256 = Convert.ToHexString(SHA256.HashData(value.AsSpan())).ToLowerInvariant(),
            base64 = Convert.ToBase64String(value.AsSpan()),
        }
        : null;
}
