using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class IngestCommand
{
    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var baselineRevision = ParseArguments(arguments);
            var currentRaw = repository.ReadCurrent();
            var baselineRaw = repository.ReadRevision(baselineRevision);
            var current = Decode(currentRaw);
            var baseline = Decode(baselineRaw);
            var document = LoadDocument(current, "candidate");
            var baselineDocument = LoadDocument(baseline, "baseline");
            var plan = DigestionIngestor.Plan(document, current, baselineDocument);
            var plannedBytes = BackfillInventoryWriter.Write(plan.Document);
            var plannedSnapshot = Decode(ReplaceLedger(currentRaw, plannedBytes));
            var report = leanReportSource.Load(current);
            var lean = ValidateLean(plannedSnapshot, report);
            var verifiedScribeEmissions = scribeEmissionVerifier.Verify(report);
            var derived = DigestionStatusEvaluator.Evaluate(
                plan.Document,
                plannedSnapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument,
                validateProjectedStatus: false);
            RequireNoFindings(derived);

            var statusByAtomId = derived.Entries.ToDictionary(
                static item => item.Entry.AtomId,
                static item => item.DerivedStatus,
                StringComparer.Ordinal);
            var refreshed = plan.Document.WithDigestionSources(
                plan.Document.RequireDigestionSources()
                    .Select(source => source with
                    {
                        Entries = source.Entries
                            .Select(entry => entry with
                            {
                                ProjectedStatus = statusByAtomId[entry.AtomId],
                            })
                            .ToImmutableArray(),
                    })
                    .ToImmutableArray());
            var finalBytes = BackfillInventoryWriter.Write(refreshed);
            var finalSnapshot = Decode(ReplaceLedger(currentRaw, finalBytes));
            var evaluation = DigestionStatusEvaluator.Evaluate(
                refreshed,
                finalSnapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument);
            RequireNoFindings(evaluation);

            var currentLedger = currentRaw.Entries.Single(static entry =>
                entry.Path == BackfillInventoryLoader.RelativePath);
            var changed = !currentLedger.Bytes.AsSpan().SequenceEqual(finalBytes.AsSpan());
            if (changed)
            {
                var outputPath = Path.Combine(
                    Path.GetFullPath(repositoryRoot),
                    BackfillInventoryLoader.RelativePath.Replace('/', Path.DirectorySeparatorChar));
                File.WriteAllBytes(outputPath, finalBytes.AsSpan());
            }

            return new CommandResult(
                true,
                $"INGEST stale_acknowledged={plan.StaleAcknowledged} "
                + $"residual_open_added={plan.ResidualOpenAdded} "
                + $"ledger_changed={changed.ToString().ToLowerInvariant()}\n"
                + DigestStatusCommand.RenderText(evaluation),
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"INGEST_INVALID {exception.Message}\n");
        }
    }

    private static string ParseArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 2
            && arguments[0] == "--base"
            && !string.IsNullOrWhiteSpace(arguments[1]))
        {
            return arguments[1];
        }

        throw new InvalidOperationException("USAGE: StrataLint ingest --base REV");
    }

    private static BackfillInventoryDocument LoadDocument(
        RepositorySnapshot snapshot,
        string side)
    {
        if (!snapshot.TryGetFile(BackfillInventoryLoader.RelativePath, out var file))
        {
            throw new InvalidOperationException(
                $"{side} {BackfillInventoryLoader.RelativePath} is missing");
        }

        return BackfillInventoryLoader.Load(file.Text);
    }

    private static RawRepositorySnapshot ReplaceLedger(
        RawRepositorySnapshot snapshot,
        ImmutableArray<byte> bytes)
    {
        var matches = snapshot.Entries.Count(static entry =>
            entry.Path == BackfillInventoryLoader.RelativePath);
        if (matches != 1)
        {
            throw new InvalidOperationException(
                $"snapshot must contain exactly one {BackfillInventoryLoader.RelativePath}");
        }

        return RawRepositorySnapshot.Create(snapshot.Entries.Select(entry =>
            entry.Path == BackfillInventoryLoader.RelativePath
                ? new RawRepositoryEntry(entry.Path, bytes)
                : entry));
    }

    private static void RequireNoFindings(DigestionLedgerEvaluation evaluation)
    {
        if (evaluation.Findings.Length > 0)
        {
            throw new InvalidOperationException(
                "digest status is invalid: " + string.Join("; ", evaluation.Findings));
        }
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
}
