using System.Text.Encodings.Web;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestStatusCommand
{
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    internal static CommandResult Run(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var options = ParseArguments(arguments);
            var initial = options.FormalizeCandidates
                ? DigestionWorkingTree.ReadLedger(
                    repository,
                    Decode,
                    static current => BackfillInventoryLoader.LoadForDigestion(current))
                : default;
            var selectedInitial = options.FormalizeAtomId is null
                ? null
                : initial.Document.RequireDigestionEntries()
                    .SingleOrDefault(entry => entry.AtomId == options.FormalizeAtomId);
            var reportFreeCandidates = options.FormalizeCandidates
                && (options.FormalizeAtomId is null || selectedInitial?.CoverageGids.IsEmpty == true);
            var loaded = reportFreeCandidates
                ? DigestionWorkingTree.ReadUncovered(
                    repository,
                    initial.Raw,
                    Decode,
                    static current => BackfillInventoryLoader.LoadForDigestion(current))
                : DigestionWorkingTree.ReadEvaluation(
                    repository,
                    Decode,
                    static current => BackfillInventoryLoader.LoadForDigestion(current));
            var snapshot = loaded.Snapshot;
            var document = loaded.Document;

            if (options.FormalizeCandidates)
            {
                if (options.FormalizeAtomId is not null
                    && !document.RequireDigestionEntries().Any(entry =>
                        string.Equals(entry.AtomId, options.FormalizeAtomId, StringComparison.Ordinal)))
                {
                    throw new InvalidOperationException(
                        $"formalize atom {options.FormalizeAtomId} is absent from the ledger");
                }

                var formalizeEvaluation = options.FormalizeAtomId is null
                    ? DigestionStatusEvaluator.EvaluateUncovered(
                        DigestionEvaluationScope.FullScan,
                        document,
                        snapshot)
                    : Evaluate(document, snapshot, leanReportSource);
                if (options.FormalizeAtomId is null
                    ? formalizeEvaluation.Findings.Length > 0
                    : formalizeEvaluation.HasReceiptIntegrityFailure)
                {
                    return InvalidEvaluation(formalizeEvaluation);
                }

                var formalizeFrontier = DigestionFrontierProjection.Create(
                    document,
                    formalizeEvaluation,
                    DigestionContentKindResolver.Resolve(snapshot, document));
                return new CommandResult(
                    true,
                    DigestFormalizeCandidates.Render(
                        formalizeFrontier,
                        snapshot,
                        document,
                        options.FormalizeAtomId),
                    string.Empty);
            }

            var evaluation = Evaluate(document, snapshot, leanReportSource);
            var readinessDiagnostics = string.Empty;
            if (options.Readiness)
            {
                var sourceGaps = DigestionReadinessQuery.SourceOccurrenceGaps(
                    evaluation.Entries,
                    sourceId => DigestionAtomContextProjection.MaterializeSource(snapshot, document, sourceId),
                    out var unreadableSources);
                readinessDiagnostics = string.Concat(sourceGaps.Select(static item =>
                    $"GAP atom={item.AtomId} code={item.Gap.Code} detail={RenderDetail(item.Gap.Detail)}\n"))
                    + string.Concat(unreadableSources.Select(static source =>
                        $"READINESS_SOURCE_UNAVAILABLE source={source.SourceId} code={source.Code} "
                        + $"detail={RenderDetail(source.Detail)}\n"));
            }

            if (evaluation.HasReceiptIntegrityFailure)
            {
                var invalid = InvalidEvaluation(evaluation);
                return invalid with { Error = invalid.Error + readinessDiagnostics };
            }

            DigestionFrontierProjection? frontier = null;
            if (options.Readiness || options.ResidualSummary || options.Json)
            {
                frontier = Frontier(document, snapshot, evaluation);
            }

            if (options.Readiness)
            {
                return new CommandResult(
                    true,
                    RenderReadiness(DigestionReadinessQuery.Classify(
                        frontier!)),
                    readinessDiagnostics);
            }

            return new CommandResult(
                true,
                options.ResidualSummary
                    ? DigestResidualSummary.Render(evaluation, frontier!)
                    : options.Json
                        ? RenderJson(evaluation, frontier!)
                        : RenderText(evaluation),
                string.Empty);
        }
        catch (Exception exception) when (
            exception is FormatException
                or InvalidOperationException
                or IOException
                or ArgumentException)
        {
            return new CommandResult(false, string.Empty, $"DIGEST_STATUS_INVALID {exception.Message}\n");
        }
    }

    // The residual summary and its per-source shards, from one evaluation of the ledger.
    internal static (string Summary, IReadOnlyDictionary<string, string> Shards) RenderResidual(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        var (_, snapshot, document) = DigestionWorkingTree.ReadEvaluation(
            repository,
            Decode,
            static current => BackfillInventoryLoader.LoadForDigestion(current));
        var evaluation = Evaluate(document, snapshot, leanReportSource);
        if (evaluation.HasReceiptIntegrityFailure)
        {
            throw new InvalidOperationException(InvalidEvaluation(evaluation).Error.TrimEnd());
        }

        var frontier = Frontier(document, snapshot, evaluation);
        return (
            DigestResidualSummary.Render(evaluation, frontier),
            DigestResidualSummary.RenderShards(evaluation, frontier));
    }

    // The query reports what the current tree derives.  Projected status is
    // updated by the operation that changes the atom; there is no separate
    // whole-ledger alignment command.
    private static DigestionLedgerEvaluation Evaluate(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        ILeanReportSource leanReportSource) =>
        DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            document,
            snapshot,
            ValidateLean(snapshot, leanReportSource.Load(snapshot)),
            validateProjectedStatus: false);

    private static DigestionFrontierProjection Frontier(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        DigestionLedgerEvaluation evaluation) =>
        DigestionFrontierProjection.Create(
            document,
            evaluation,
            DigestionContentKindResolver.Resolve(snapshot, document));

    private static DigestStatusOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        var json = false;
        var residualSummary = false;
        var formalizeCandidates = false;
        var readiness = false;
        string? formalizeAtomId = null;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--json" when !json:
                    json = true;
                    break;
                case "--residual-summary" when !residualSummary:
                    residualSummary = true;
                    break;
                case "--formalize-candidates" when !formalizeCandidates:
                    formalizeCandidates = true;
                    break;
                case "--readiness" when !readiness:
                    readiness = true;
                    break;
                case "--atom-id" when formalizeAtomId is null && index + 1 < arguments.Count:
                    formalizeAtomId = arguments[++index];
                    if (string.IsNullOrWhiteSpace(formalizeAtomId)) throw Usage();
                    break;
                default:
                    throw Usage();
            }
        }

        if ((json ? 1 : 0)
                + (residualSummary ? 1 : 0)
                + (formalizeCandidates ? 1 : 0)
                + (readiness ? 1 : 0) > 1
            || (formalizeAtomId is not null && !formalizeCandidates))
        {
            throw Usage();
        }

        return new DigestStatusOptions(
            json,
            residualSummary,
            formalizeCandidates,
            readiness,
            formalizeAtomId);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint digest-status [--json|--residual-summary|--readiness|--formalize-candidates "
        + "[--atom-id ATOM_ID]]");

    internal static string RenderText(DigestionLedgerEvaluation evaluation)
    {
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.WriteLine(
            $"DIGEST_STATUS entries={evaluation.Entries.Length} deletable_now={evaluation.DeletableCount}");
        foreach (var entry in evaluation.Entries
                     .OrderBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
                     .ThenBy(static item => item.Entry.AtomId, StringComparer.Ordinal))
        {
            writer.WriteLine("ENTRY " + entry.Render());
            foreach (var gap in entry.Gaps)
            {
                writer.WriteLine(
                    $"GAP atom={entry.Entry.AtomId} code={gap.Code} detail={RenderDetail(gap.Detail)}");
            }
        }

        return writer.ToString();
    }

    internal static string RenderDetail(string detail) => JsonSerializer.Serialize(detail, JsonOptions);

    internal static string RenderJson(
        DigestionLedgerEvaluation evaluation,
        DigestionFrontierProjection frontier)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
        ArgumentNullException.ThrowIfNull(frontier);
        var material = new
        {
            schema = "stratalint-digest-status-v1",
            entries_total = evaluation.Entries.Length,
            deletable_now = evaluation.DeletableCount,
            frontier = new
            {
                total = FrontierCounts(frontier.Total),
                per_source = frontier.PerSource.Select(static source => new
                {
                    source_id = source.SourceId,
                    counts = FrontierCounts(source.Counts),
                }),
                entries = frontier.Entries.Select(entry => new
                {
                    source_id = entry.Entry.SourceId,
                    atom_id = entry.Entry.AtomId,
                    primary_disposition = entry.PrimaryDispositionLabel,
                    primary_detail = entry.PrimaryDetail,
                    kind_label = entry.KindLabel,
                    is_chain_child = entry.IsChainChild,
                    parent_atom_ids = entry.ParentAtomIds,
                }),
            },
            entries = evaluation.Entries
                .OrderBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
                .ThenBy(static item => item.Entry.AtomId, StringComparer.Ordinal)
                .Select(item => new
                {
                    source_id = item.Entry.SourceId,
                    atom_id = item.Entry.AtomId,
                    coverage_gids = item.Entry.CoverageGids,
                    alignment = DigestionReceiptAlignmentNames.Render(item.Alignment),
                    migration = DigestionStatusNames.Migration(item.DerivedStatus.Migration),
                    truth = DigestionStatusNames.Truth(item.DerivedStatus.Truth),
                    deletable = item.Deletable,
                    gaps = item.Gaps.Select(static gap => new
                    {
                        code = gap.Code,
                        detail = gap.Detail,
                    }),
                }),
        };
        return JsonSerializer.Serialize(material, JsonOptions) + "\n";
    }

    private static object FrontierCounts(DigestionFrontierCounts counts) => new
    {
        residual_open = counts.ResidualOpen,
        formalization_frontier = counts.FormalizationFrontier,
        quarantined = counts.Quarantined,
        withheld = counts.Withheld,
        chain_child = counts.ChainChild,
        not_formalizable = counts.NotFormalizable,
        formalizable_claim = counts.FormalizableClaim,
    };

    internal static string RenderReadiness(IEnumerable<DigestionReadinessRecord> entries)
    {
        ArgumentNullException.ThrowIfNull(entries);
        var material = new
        {
            schema = "stratalint-digestion-readiness-v1",
            entries = entries.Select(static item => new
            {
                source_id = item.SourceId,
                atom_id = item.AtomId,
                coverage_gids = item.CoverageGids,
                action = item.Action,
                ordered_blockers = item.OrderedBlockers,
                unknown_predicates = item.UnknownPredicates,
            }),
        };
        return JsonSerializer.Serialize(material, JsonOptions) + "\n";
    }

    private static CommandResult InvalidEvaluation(DigestionLedgerEvaluation evaluation)
    {
        var gapCount = evaluation.Entries.Sum(static entry => entry.Gaps.Length);
        var error = "DIGEST_STATUS_INVALID count=" + (evaluation.Findings.Length + gapCount) + "\n"
            + string.Concat(evaluation.Findings.Select(static finding => $"FINDING {finding}\n"))
            + string.Concat(evaluation.Entries.SelectMany(static entry => entry.Gaps.Select(gap =>
                $"GAP atom={entry.Entry.AtomId} code={gap.Code} "
                + $"detail={JsonSerializer.Serialize(gap.Detail)}\n")));
        return new CommandResult(false, string.Empty, error);
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

    private sealed record DigestStatusOptions(
        bool Json,
        bool ResidualSummary,
        bool FormalizeCandidates,
        bool Readiness,
        string? FormalizeAtomId);

}
