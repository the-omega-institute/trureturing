using System.Text.Encodings.Web;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestStatusCommand
{
    private const string ImplementationPath = "tools/StrataLint.Cli/Commands/DigestStatusCommand.cs";
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    internal static CommandResult Run(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments,
        IAtomHistorySource atomHistorySource,
        TimeProvider ageTimeProvider)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(atomHistorySource);
        ArgumentNullException.ThrowIfNull(ageTimeProvider);
        try
        {
            var options = ParseArguments(arguments);
            var snapshot = Decode(repository.ReadCurrent());
            var changes = options.BaselineRevision is null
                ? repository.ReadCurrentChanges()
                : repository.ReadChanges(options.BaselineRevision);
            var scope = DigestionEvaluationScopes.ForChanges(changes, ImplementationPath);

            if (options.FormalizeCandidates)
            {
                var formalizeLeanReport = leanReportSource.Load(snapshot);
                var formalizeDocument = BackfillInventoryLoader.Load(snapshot, scope, changes);
                BackfillInventoryDocument? formalizeBaselineDocument = null;
                RepositorySnapshot? formalizeBaselineSnapshot = null;
                if (options.BaselineRevision is not null)
                {
                    formalizeBaselineSnapshot = Decode(
                        repository.ReadRevision(options.BaselineRevision));
                    formalizeBaselineDocument = BackfillInventoryLoader.LoadBaseline(
                        formalizeBaselineSnapshot);
                }

                if (options.FormalizeAtomId is not null
                    && !formalizeDocument.RequireDigestionEntries().Any(entry =>
                        string.Equals(entry.AtomId, options.FormalizeAtomId, StringComparison.Ordinal)))
                {
                    throw new InvalidOperationException(
                        $"formalize atom {options.FormalizeAtomId} is absent from the ledger");
                }

                var formalizeEvaluation = options.FormalizeAtomId is null
                    ? DigestionStatusEvaluator.EvaluateUncovered(
                        scope,
                        formalizeDocument,
                        snapshot,
                        formalizeBaselineDocument,
                        changes: changes)
                    : DigestionStatusEvaluator.Evaluate(
                        scope,
                        formalizeDocument,
                        snapshot,
                        ValidateLean(snapshot, formalizeLeanReport),
                        scribeEmissionVerifier.Verify(snapshot, formalizeLeanReport, changes),
                        formalizeBaselineDocument,
                        baselineSnapshot: formalizeBaselineSnapshot,
                        changes: changes,
                        projectedStatusChanges: changes);
                if (options.FormalizeAtomId is null
                    ? formalizeEvaluation.Findings.Length > 0
                    : formalizeEvaluation.HasReceiptIntegrityFailure)
                {
                    return InvalidEvaluation(formalizeEvaluation);
                }

                var formalizeContentKinds = DigestionContentKindResolver.Resolve(
                    snapshot,
                    formalizeDocument);
                var formalizeFrontier = DigestionFrontierProjection.Create(
                    formalizeDocument,
                    formalizeEvaluation,
                    formalizeContentKinds,
                    options.RetryDispositions);
                return new CommandResult(
                    true,
                    DigestFormalizeCandidates.Render(
                        formalizeFrontier,
                        snapshot,
                        formalizeDocument,
                        options.FormalizeAtomId),
                    string.Empty);
            }

            var leanReport = leanReportSource.Load(snapshot);
            var lean = ValidateLean(snapshot, leanReport);
            var document = BackfillInventoryLoader.Load(snapshot, scope, changes);
            BackfillInventoryDocument? baselineDocument = null;
            RepositorySnapshot? baselineSnapshot = null;
            if (options.BaselineRevision is not null)
            {
                baselineSnapshot = Decode(repository.ReadRevision(options.BaselineRevision));
                baselineDocument = BackfillInventoryLoader.LoadBaseline(baselineSnapshot);
            }
            var receiptGateScope = ResolveReceiptGateScope(
                snapshot,
                baselineSnapshot,
                leanReport,
                document,
                changes);
            var verifiedScribeEmissions = scribeEmissionVerifier.Verify(
                snapshot,
                leanReport,
                receiptGateScope.Changes);

            var ruleImplementationChanged = BaseFactImpact.RuleImplementationChanged(changes);
            bool IsBaseFactAffected(string path) =>
                BaseFactImpact.IsAffected(changes, ruleImplementationChanged, path);
            var casChanges = DigestionEvaluationScopes.ResolveChanges(scope, changes);
            var casEvaluation = DigestionCasStore.Evaluate(
                document,
                snapshot,
                casChanges,
                IsBaseFactAffected);
            var evaluation = DigestionStatusEvaluator.Evaluate(
                scope,
                document,
                snapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument,
                baselineSnapshot: baselineSnapshot,
                casEvaluation: casEvaluation,
                changes: receiptGateScope.Changes,
                casChanges: casChanges,
                isBaseFactAffected: IsBaseFactAffected,
                projectedStatusChanges: changes,
                receiptGateChanges: receiptGateScope.Changes,
                isReceiptGateBaseFactAffected: receiptGateScope.IsBaseFactAffected);
            if (evaluation.HasReceiptIntegrityFailure)
            {
                return InvalidEvaluation(evaluation);
            }

            DigestionFrontierProjection? frontier = null;
            if (options.Readiness || options.ResidualSummary || options.Json)
            {
                frontier = DigestionFrontierProjection.Create(
                    document,
                    evaluation,
                    DigestionContentKindResolver.Resolve(snapshot, document),
                    retryDispositions: false);
            }

            if (options.Readiness)
            {
                return new CommandResult(
                    true,
                    RenderReadiness(DigestionReadinessQuery.Classify(
                        frontier!)),
                    string.Empty);
            }

            var age = options.ResidualSummary || options.Json
                ? DigestAtomAge.Read(evaluation, frontier!, atomHistorySource, ageTimeProvider)
                : null;
            return new CommandResult(
                true,
                options.ResidualSummary
                    ? DigestResidualSummary.Render(evaluation, frontier!) + age!.RenderSummary()
                    : options.Json
                        ? RenderJson(evaluation, frontier!, age!)
                        : RenderText(evaluation),
                string.Empty);
        }
        catch (AtomHistoryUnavailableException exception)
        {
            return new CommandResult(false, string.Empty,
                $"DIGEST_AGE_HISTORY_UNAVAILABLE {exception.Message}\n");
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

    internal static IReadOnlyDictionary<string, string> RenderShards(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        string baselineRevision)
    {
        var snapshot = Decode(repository.ReadCurrent());
        var baseline = Decode(repository.ReadRevision(baselineRevision));
        var changes = repository.ReadChanges(baselineRevision);
        var leanReport = leanReportSource.Load(snapshot);
        var ruleImplementationChanged = BaseFactImpact.RuleImplementationChanged(changes);
        bool IsBaseFactAffected(string path) =>
            BaseFactImpact.IsAffected(changes, ruleImplementationChanged, path);
        var scope = DigestionEvaluationScopes.ForChanges(changes, ImplementationPath);
        var document = BackfillInventoryLoader.Load(snapshot, scope, changes);
        var receiptGateScope = ResolveReceiptGateScope(
            snapshot,
            baseline,
            leanReport,
            document,
            changes);
        var casChanges = DigestionEvaluationScopes.ResolveChanges(scope, changes);
        var evaluation = DigestionStatusEvaluator.Evaluate(
            scope,
            document,
            snapshot,
            ValidateLean(snapshot, leanReport),
            scribeEmissionVerifier.Verify(snapshot, leanReport, receiptGateScope.Changes),
            BackfillInventoryLoader.LoadBaseline(baseline),
            baselineSnapshot: baseline,
            casEvaluation: DigestionCasStore.Evaluate(
                document,
                snapshot,
                casChanges,
                IsBaseFactAffected),
            changes: receiptGateScope.Changes,
            casChanges: casChanges,
            isBaseFactAffected: IsBaseFactAffected,
            projectedStatusChanges: changes,
            receiptGateChanges: receiptGateScope.Changes,
            isReceiptGateBaseFactAffected: receiptGateScope.IsBaseFactAffected);
        if (evaluation.HasReceiptIntegrityFailure)
        {
            throw new InvalidOperationException(InvalidEvaluation(evaluation).Error.TrimEnd());
        }

        var frontier = DigestionFrontierProjection.Create(
            document,
            evaluation,
            DigestionContentKindResolver.Resolve(snapshot, document),
            retryDispositions: false);
        return DigestResidualSummary.RenderShards(evaluation, frontier);
    }

    private static DigestStatusOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        var json = false;
        var residualSummary = false;
        var formalizeCandidates = false;
        var readiness = false;
        var retryDispositions = false;
        string? baselineRevision = null;
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
                case "--retry-dispositions" when !retryDispositions:
                    retryDispositions = true;
                    break;
                case "--base" when baselineRevision is null && index + 1 < arguments.Count:
                    baselineRevision = arguments[++index];
                    if (string.IsNullOrWhiteSpace(baselineRevision)) throw Usage();
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
            || (formalizeAtomId is not null && !formalizeCandidates)
            || (retryDispositions && !formalizeCandidates))
        {
            throw Usage();
        }

        return new DigestStatusOptions(
            json,
            residualSummary,
            formalizeCandidates,
            readiness,
            retryDispositions,
            baselineRevision,
            formalizeAtomId);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint digest-status [--json|--residual-summary|--readiness|--formalize-candidates "
        + "[--atom-id ATOM_ID] [--retry-dispositions]] [--base REV]");

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
            foreach (var observation in entry.ReceiptObservations)
                writer.WriteLine($"OBSERVATION atom={entry.Entry.AtomId} code={observation.Code} detail={RenderDetail(observation.Detail)}");
        }

        return writer.ToString();
    }

    internal static string RenderDetail(string detail) => JsonSerializer.Serialize(detail, JsonOptions);

    internal static string RenderJson(
        DigestionLedgerEvaluation evaluation,
        DigestionFrontierProjection frontier,
        DigestAtomAge age)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
        ArgumentNullException.ThrowIfNull(frontier);
        var material = new
        {
            schema = "stratalint-digest-status-v1",
            entries_total = evaluation.Entries.Length,
            deletable_now = evaluation.DeletableCount,
            age_histogram = new { total = age.Total, per_source = age.PerSource },
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
                    first_seen_date = age.Entries[entry.Entry.AtomId].FirstSeenDate,
                    age_days = age.Entries[entry.Entry.AtomId].AgeDays,
                    age_bucket = age.Entries[entry.Entry.AtomId].AgeBucket,
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
                    first_seen_date = age.Entries.GetValueOrDefault(item.Entry.AtomId)?.FirstSeenDate,
                    age_days = age.Entries.GetValueOrDefault(item.Entry.AtomId)?.AgeDays,
                    age_bucket = age.Entries.GetValueOrDefault(item.Entry.AtomId)?.AgeBucket,
                    gaps = item.Gaps.Select(static gap => new
                    {
                        code = gap.Code,
                        detail = gap.Detail,
                    }),
                    receipt_observations = item.ReceiptObservations.Select(static observation => new
                    {
                        code = observation.Code,
                        detail = observation.Detail,
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
        bool RetryDispositions,
        string? BaselineRevision,
        string? FormalizeAtomId);

}
