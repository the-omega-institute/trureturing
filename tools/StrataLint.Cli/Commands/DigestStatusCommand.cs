using System.Collections.Immutable;
using System.Text;
using System.Text.Encodings.Web;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestStatusCommand
{
    private const string ImplementationPath = "tools/StrataLint.Cli/Commands/DigestStatusCommand.cs";
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

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
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(arguments);
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

                return new CommandResult(
                    true,
                    RenderFormalizeCandidates(
                        formalizeEvaluation,
                        snapshot,
                        formalizeDocument,
                        formalizeLeanReport,
                        options.FormalizeAtomId,
                        options.RetryDispositions),
                    string.Empty);
            }

            var leanReport = leanReportSource.Load(snapshot);
            var lean = ValidateLean(snapshot, leanReport);
            var verifiedScribeEmissions = scribeEmissionVerifier.Verify(snapshot, leanReport, changes);
            var document = BackfillInventoryLoader.Load(snapshot, scope, changes);
            BackfillInventoryDocument? baselineDocument = null;
            RepositorySnapshot? baselineSnapshot = null;
            if (options.BaselineRevision is not null)
            {
                baselineSnapshot = Decode(repository.ReadRevision(options.BaselineRevision));
                baselineDocument = BackfillInventoryLoader.LoadBaseline(baselineSnapshot);
            }

            var ruleImplementationChanged = BaseFactImpact.RuleImplementationChanged(changes);
            bool IsBaseFactAffected(string path) =>
                BaseFactImpact.IsAffected(changes, ruleImplementationChanged, path);
            var casEvaluation = DigestionCasStore.Evaluate(
                document,
                snapshot,
                DigestionEvaluationScopes.ResolveChanges(scope, changes),
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
                changes: changes,
                isBaseFactAffected: IsBaseFactAffected,
                projectedStatusChanges: changes);
            if (evaluation.HasReceiptIntegrityFailure)
            {
                return InvalidEvaluation(evaluation);
            }

            if (options.Readiness)
            {
                var readinessEntries = evaluation.Entries
                    .Where(static item =>
                        item.DerivedStatus.Migration == DigestionMigrationState.Residual
                        && item.DerivedStatus.Truth == DigestionTruthState.Open)
                    .ToArray();
                var presentReceiptAtomIds = readinessEntries
                    .Where(item => snapshot.TryGetFile(
                        DigestionFormalizationReceipt.PathForAtom(item.Entry.AtomId),
                        out _))
                    .Select(static item => item.Entry.AtomId)
                    .ToImmutableHashSet(StringComparer.Ordinal);
                var currentReceipts = readinessEntries
                    .Select(item => (
                        item.Entry.AtomId,
                        Receipt: CurrentFormalizationReceiptModel(
                            item.Entry,
                            snapshot,
                            leanReport)))
                    .Where(static item => item.Receipt is not null)
                    .ToDictionary(
                        static item => item.AtomId,
                        static item => item.Receipt!,
                        StringComparer.Ordinal);
                return new CommandResult(
                    true,
                    RenderReadiness(DigestionReadinessQuery.Classify(
                        document,
                        evaluation,
                        currentReceipts,
                        presentReceiptAtomIds,
                        verifiedScribeEmissions)),
                    string.Empty);
            }

            return new CommandResult(
                true,
                options.ResidualSummary
                    ? DigestResidualSummary.Render(evaluation)
                    : options.Json
                        ? RenderJson(evaluation)
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
        var evaluation = DigestionStatusEvaluator.Evaluate(
            scope,
            document,
            snapshot,
            ValidateLean(snapshot, leanReport),
            scribeEmissionVerifier.Verify(snapshot, leanReport, changes),
            BackfillInventoryLoader.LoadBaseline(baseline),
            baselineSnapshot: baseline,
            casEvaluation: DigestionCasStore.Evaluate(
                document,
                snapshot,
                DigestionEvaluationScopes.ResolveChanges(scope, changes),
                IsBaseFactAffected),
            changes: changes,
            isBaseFactAffected: IsBaseFactAffected,
            projectedStatusChanges: changes);
        if (evaluation.HasReceiptIntegrityFailure)
        {
            throw new InvalidOperationException(InvalidEvaluation(evaluation).Error.TrimEnd());
        }

        return DigestResidualSummary.RenderShards(evaluation);
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
        }

        return writer.ToString();
    }

    internal static string RenderDetail(string detail) => JsonSerializer.Serialize(detail, JsonOptions);

    private static string RenderJson(DigestionLedgerEvaluation evaluation)
    {
        var material = new
        {
            schema = "stratalint-digest-status-v1",
            entries_total = evaluation.Entries.Length,
            deletable_now = evaluation.DeletableCount,
            entries = evaluation.Entries
                .OrderBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
                .ThenBy(static item => item.Entry.AtomId, StringComparer.Ordinal)
                .Select(static item => new
                {
                    source_id = item.Entry.SourceId,
                    atom_id = item.Entry.AtomId,
                    ast_path = item.Entry.AstPath,
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
                ast_path = item.AstPath,
                action = item.Action,
                ordered_blockers = item.OrderedBlockers,
                unknown_predicates = item.UnknownPredicates,
            }),
        };
        return JsonSerializer.Serialize(material, JsonOptions) + "\n";
    }

    private static string RenderFormalizeCandidates(
        DigestionLedgerEvaluation evaluation,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument ledger,
        LeanAxiomReport leanReport,
        string? selectedAtomId,
        bool retryDispositions)
    {
        var projections = evaluation.Entries
            .Where(item =>
                item.Alignment == DigestionReceiptAlignment.Seen
                && (selectedAtomId is not null
                    ? string.Equals(item.Entry.AtomId, selectedAtomId, StringComparison.Ordinal)
                    : item.DerivedStatus.Migration == DigestionMigrationState.Residual
                        && item.DerivedStatus.Truth == DigestionTruthState.Open
                        && item.Entry.CoverageGids.Length == 0))
            .Select(item => Projection(item, snapshot, leanReport, retryDispositions))
            .Where(static item => item is not null)
            .OrderBy(static item => item!.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item!.AtomId, StringComparer.Ordinal)
            .Select(static item => item!)
            .ToArray();
        var material = new
        {
            // v4 (2026-08-30, #4125): 新增顶层结果族 `quarantined[]`;本仓惯例是每加一个顶层结果族就升一版
            // (v1→v2 加 withheld,v2→v3 加 recorded_formalizations)。消费者按 schema 值接受,见测试断言。
            schema = "stratalint-formalize-candidates-v4",
            ledger_sha256 = DigestionLedgerPreimage.ComputeSha256(ledger),
            candidates = projections
                .Where(static item => item.Candidate is not null)
                .Select(static item => item.Candidate!),
            recorded_formalizations = projections
                .Where(static item => item.RecordedFormalization is not null)
                .Select(static item => item.RecordedFormalization!),
            quarantined = projections
                .Where(static item => item.Quarantined is not null)
                .Select(static item => item.Quarantined!),
            withheld = projections
                .Where(static item => item.Withheld is not null)
                .Select(static item => item.Withheld!),
        };
        return JsonSerializer.Serialize(material, JsonOptions) + "\n";
    }

    private static FormalizeProjection? Projection(
        DigestionEntryEvaluation evaluation,
        RepositorySnapshot snapshot,
        LeanAxiomReport leanReport,
        bool retryDispositions)
    {
        var entry = evaluation.Entry;
        var dispositionSelection = DigestionCoverDispositionSelector.Classify(
            entry,
            retryDispositions);
        if (!DigestionAstKindPolicy.TryGetFormalizableKind(entry.AstPath, out var kind))
        {
            return null;
        }

        if (entry.Receipts.Quarantine is { } quarantine)
        {
            return new FormalizeProjection(
                entry.SourceId,
                entry.AtomId,
                null,
                null,
                new QuarantinedFormalizeCandidate(
                    entry.SourceId,
                    entry.AtomId,
                    entry.AstPath,
                    quarantine.Justification,
                    quarantine.ReentryCondition,
                    quarantine.BlockerClass),
                null);
        }

        if (dispositionSelection == DigestionCoverDispositionSelection.Withheld)
        {
            return new FormalizeProjection(
                entry.SourceId,
                entry.AtomId,
                null,
                null,
                null,
                new WithheldFormalizeCandidate(
                    entry.AtomId,
                    DigestionCoverDispositionSelector.WithholdReason,
                    null));
        }

        var recordedFormalization = dispositionSelection == DigestionCoverDispositionSelection.Retry
            ? null
            : CurrentFormalizationProjection(entry, snapshot, leanReport);
        if (recordedFormalization is not null)
        {
            return new FormalizeProjection(
                entry.SourceId,
                entry.AtomId,
                null,
                recordedFormalization,
                null,
                null);
        }

        var casPath = DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..];
        if (!snapshot.TryGetFile(casPath, out var atom))
        {
            throw new InvalidOperationException($"entry {entry.AtomId} CAS blob is missing: {casPath}");
        }

        string atomText;
        try
        {
            atomText = StrictUtf8.GetString(atom.RawBytes.AsSpan());
        }
        catch (DecoderFallbackException exception)
        {
            throw new FormatException(
                $"entry {entry.AtomId} CAS blob must contain strict UTF-8: {casPath}",
                exception);
        }

        var status = evaluation.Atom?.StatusMarker
            ?? throw new FormatException($"entry {entry.AtomId} has no canonical atom alignment");
        if (status.Kind == DigestionAtomStatusMarkerKind.Malformed)
        {
            return new FormalizeProjection(
                entry.SourceId,
                entry.AtomId,
                null,
                null,
                null,
                new WithheldFormalizeCandidate(
                    entry.AtomId,
                    "malformed-status-marker",
                    status.Qualifier));
        }

        if (status is
            {
                Kind: DigestionAtomStatusMarkerKind.Valid,
                Status: "closed",
                Qualifier.Length: > 0,
            })
        {
            return new FormalizeProjection(
                entry.SourceId,
                entry.AtomId,
                null,
                null,
                null,
                new WithheldFormalizeCandidate(
                    entry.AtomId,
                    "qualified-closed-status",
                    status.Qualifier));
        }

        return new FormalizeProjection(
            entry.SourceId,
            entry.AtomId,
            new FormalizeCandidate(
                entry.SourceId,
                entry.AtomId,
                entry.AstPath,
                kind,
                entry.CasRef,
                entry.Fingerprints.RawSha256,
                atomText),
            null,
            null,
            null);
    }

    private static RecordedFormalization? CurrentFormalizationProjection(
        DigestionLedgerEntry entry,
        RepositorySnapshot snapshot,
        LeanAxiomReport leanReport)
    {
        var receipt = CurrentFormalizationReceiptModel(entry, snapshot, leanReport);
        return receipt is null
            ? null
            : new RecordedFormalization(
                entry.SourceId,
                entry.AtomId,
                "current-formalization-receipt",
                receipt.PrimaryGid,
                receipt.RegisteredGids,
                DigestionFormalizationReceipt.PathForAtom(entry.AtomId));
    }

    private static DigestionFormalizationReceipt? CurrentFormalizationReceiptModel(
        DigestionLedgerEntry entry,
        RepositorySnapshot snapshot,
        LeanAxiomReport leanReport)
    {
        var path = DigestionFormalizationReceipt.PathForAtom(entry.AtomId);
        if (!DigestionFormalizationReceipt.IsCanonicalPath(path))
        {
            return null;
        }

        if (!snapshot.TryGetFile(path, out _))
        {
            return null;
        }

        try
        {
            var receipt = DigestionFormalizationReceipt.Load(snapshot, path);
            if (!string.Equals(receipt.AtomId, entry.AtomId, StringComparison.Ordinal)
                || !string.Equals(receipt.CasRef, entry.CasRef, StringComparison.Ordinal)
                || !string.Equals(
                    receipt.RawSha256,
                    entry.Fingerprints.RawSha256,
                    StringComparison.Ordinal)
                || !Gid.TryParse(receipt.PrimaryGid, out var gid))
            {
                return null;
            }

            var currentSignature = DigestionFormalizationReceipt.ResolveSignature(gid, leanReport);
            if (receipt.Signature != currentSignature)
            {
                return null;
            }

            foreach (var extension in receipt.HostedExtensions)
            {
                if (!Gid.TryParse(extension.Gid, out var extensionGid)
                    || extension.Signature
                        != DigestionFormalizationReceipt.ResolveSignature(extensionGid, leanReport))
                {
                    return null;
                }
            }

            return receipt;
        }
        catch (Exception exception) when (exception is FormatException or JsonException)
        {
            return null;
        }
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
        bool RetryDispositions,
        string? BaselineRevision,
        string? FormalizeAtomId);

    private sealed record FormalizeCandidate(
        string SourceId,
        string AtomId,
        string AstPath,
        string Kind,
        string CasRef,
        string RawSha256,
        string AtomText);

    private sealed record WithheldFormalizeCandidate(
        string AtomId,
        string WithholdReason,
        string? StatusQualifier);

    private sealed record QuarantinedFormalizeCandidate(
        string SourceId,
        string AtomId,
        string AstPath,
        string Justification,
        string ReentryCondition,
        string? BlockerClass);

    private sealed record FormalizeProjection(
        string SourceId,
        string AtomId,
        FormalizeCandidate? Candidate,
        RecordedFormalization? RecordedFormalization,
        QuarantinedFormalizeCandidate? Quarantined,
        WithheldFormalizeCandidate? Withheld);

    private sealed record RecordedFormalization(
        string SourceId,
        string AtomId,
        string EvidenceKind,
        string PrimaryGid,
        ImmutableArray<string> Gids,
        string ReceiptPath);
}
