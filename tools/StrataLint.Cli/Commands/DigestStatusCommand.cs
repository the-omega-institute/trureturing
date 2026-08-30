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

        if ((json ? 1 : 0) + (residualSummary ? 1 : 0) + (formalizeCandidates ? 1 : 0) > 1
            || (formalizeAtomId is not null && !formalizeCandidates)
            || (retryDispositions && !formalizeCandidates))
        {
            throw Usage();
        }

        return new DigestStatusOptions(
            json,
            residualSummary,
            formalizeCandidates,
            retryDispositions,
            baselineRevision,
            formalizeAtomId);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint digest-status [--json|--residual-summary|--formalize-candidates "
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
            schema = "stratalint-formalize-candidates-v3",
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
        var separator = entry.AstPath.IndexOf('/', StringComparison.Ordinal);
        if (separator <= 0)
        {
            return null;
        }

        var kind = entry.AstPath[..separator];
        if (kind is not (
            "theorem" or "proposition" or "lemma" or "corollary"
            or "定理" or "命题" or "引理" or "推论"))
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
            : CurrentFormalizationReceipt(entry, snapshot, leanReport);
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

    private static RecordedFormalization? CurrentFormalizationReceipt(
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

            return new RecordedFormalization(
                entry.SourceId,
                entry.AtomId,
                "current-formalization-receipt",
                receipt.PrimaryGid,
                receipt.RegisteredGids,
                path);
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

internal static class DigestResidualSummary
{
    private const string ResidualGapCode = "unresolved-subitem";
    private const string ShardDirectory = "Generated/echo-residuals/";

    internal static IReadOnlyDictionary<string, string> RenderShards(
        DigestionLedgerEvaluation evaluation)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
        var shards = new SortedDictionary<string, string>(StringComparer.Ordinal);
        foreach (var source in evaluation.Entries
                     .GroupBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
                     .OrderBy(static group => group.Key, StringComparer.Ordinal))
        {
            var atoms = source
                .Where(static item => !DigestionCoverDispositionSelector.IsWithheld(item.Entry))
                .Select(static item => new AtomResiduals(
                    item.Entry.AtomId,
                    item.Gaps
                        .Where(static gap => gap.Code == ResidualGapCode)
                        .Select(static gap => gap.Detail)
                        .OrderBy(static detail => detail, StringComparer.Ordinal)
                        .ToArray()))
                .Where(static atom => atom.Subitems.Length > 0)
                .OrderBy(static atom => atom.AtomId, StringComparer.Ordinal)
                .ToArray();
            var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
            writer.WriteLine($"# Echo Residual Summary — `{source.Key}`");
            writer.WriteLine();
            writer.WriteLine($"- unresolved_subitems: {atoms.Sum(static atom => atom.Subitems.Length)}");
            writer.WriteLine($"- mother_residual_atom_ids: {atoms.Length}");
            writer.WriteLine();
            if (atoms.Length == 0)
            {
                writer.WriteLine("Mother residual atoms: none.");
            }
            else
            {
                writer.WriteLine("Mother residual atoms:");
                writer.WriteLine();
                foreach (var atom in atoms)
                {
                    writer.WriteLine($"- `{atom.AtomId}` ({atom.Subitems.Length})");
                    foreach (var subitem in atom.Subitems)
                    {
                        writer.WriteLine($"  - `{subitem}`");
                    }
                }
            }

            shards.Add(
                $"{ShardDirectory}{source.Key}.md",
                EchoResidualBlock.RenderShard(source.Key, writer.ToString()));
        }

        return shards;
    }

    internal static string Render(DigestionLedgerEvaluation evaluation)
    {
        ArgumentNullException.ThrowIfNull(evaluation);
        var sources = evaluation.Entries
            .GroupBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
            .OrderBy(static group => group.Key, StringComparer.Ordinal)
            .Select(static group => new SourceResiduals(
                group.Key,
                group
                    .Where(static item =>
                        item.Entry.Receipts.Quarantine is null
                        && !DigestionCoverDispositionSelector.IsWithheld(item.Entry))
                    .Select(static item => new AtomResiduals(
                        item.Entry.AtomId,
                        item.Gaps
                            .Where(static gap => gap.Code == ResidualGapCode)
                            .Select(static gap => gap.Detail)
                            .OrderBy(static detail => detail, StringComparer.Ordinal)
                            .ToArray()))
                    .Where(static item => item.Subitems.Length > 0)
                    .OrderBy(static item => item.AtomId, StringComparer.Ordinal)
                    .ToArray()))
            .ToArray();
        var sharedResidues = sources
            .SelectMany(static source => source.Atoms.SelectMany(atom =>
                atom.Subitems.Select(residue => new ResidueHost(residue, source.SourceId, atom.AtomId))))
            .GroupBy(static host => host.Residue, StringComparer.Ordinal)
            .Select(static group => new SharedResidue(
                group.Key,
                group.Distinct().OrderBy(static host => host.SourceId, StringComparer.Ordinal)
                    .ThenBy(static host => host.AtomId, StringComparer.Ordinal)
                    .ToArray()))
            .Where(static residue => residue.Hosts
                .Select(static host => host.SourceId)
                .Distinct(StringComparer.Ordinal)
                .Count() > 1)
            .OrderBy(static residue => residue.Name, StringComparer.Ordinal)
            .ToArray();
        var quarantined = evaluation.Entries
            .Where(static item => item.Entry.Receipts.Quarantine is not null)
            .Select(static item => new QuarantinedResiduals(
                item.Entry.SourceId,
                item.Entry.AtomId,
                item.Entry.Receipts.Quarantine!,
                item.Gaps
                    .Where(static gap => gap.Code == ResidualGapCode)
                    .Select(static gap => gap.Detail)
                    .OrderBy(static detail => detail, StringComparer.Ordinal)
                    .ToArray()))
            .Where(static item => item.Subitems.Length > 0)
            .OrderBy(static item => item.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item.AtomId, StringComparer.Ordinal)
            .ToArray();
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.WriteLine("# Echo Residual Summary");
        writer.WriteLine();
        writer.WriteLine($"- unresolved_subitems: {sources.Sum(static source => source.SubitemCount)}");
        writer.WriteLine($"- mother_residual_atom_ids: {sources.Sum(static source => source.Atoms.Length)}");
        writer.WriteLine();
        writer.WriteLine("## quarantined residuals");
        writer.WriteLine();
        writer.WriteLine($"- quarantined_subitems: {quarantined.Sum(static item => item.Subitems.Length)}");
        writer.WriteLine($"- mother_quarantined_atom_ids: {quarantined.Length}");
        writer.WriteLine();
        if (quarantined.Length == 0)
        {
            writer.WriteLine("Quarantined residual atoms: none.");
        }
        else
        {
            writer.WriteLine("Quarantined residual atoms:");
            writer.WriteLine();
            foreach (var item in quarantined)
            {
                writer.WriteLine($"- `{item.SourceId}/{item.AtomId}` ({item.Subitems.Length})");
                writer.WriteLine($"  - justification: `{item.Quarantine.Justification}`");
                writer.WriteLine($"  - reentry_condition: `{item.Quarantine.ReentryCondition}`");
                foreach (var subitem in item.Subitems)
                {
                    writer.WriteLine($"  - `{subitem}`");
                }
            }
        }

        writer.WriteLine();
        writer.WriteLine("## cross-volume shared residues");
        writer.WriteLine();
        writer.WriteLine($"- shared_residue_names: {sharedResidues.Length}");
        writer.WriteLine($"- host_atoms: {sharedResidues.Sum(static residue => residue.Hosts.Length)}");
        writer.WriteLine();
        if (sharedResidues.Length == 0)
        {
            writer.WriteLine("Shared residue hosts: none.");
        }
        else
        {
            writer.WriteLine("Shared residue hosts:");
            writer.WriteLine();
            foreach (var residue in sharedResidues)
            {
                var volumeCount = residue.Hosts
                    .Select(static host => host.SourceId)
                    .Distinct(StringComparer.Ordinal)
                    .Count();
                var hosts = string.Join(
                    ", ",
                    residue.Hosts.Select(static host => $"`{host.SourceId}/{host.AtomId}`"));
                writer.WriteLine(
                    $"- `{residue.Name}` ({volumeCount} volumes, {residue.Hosts.Length} host atoms): {hosts}");
            }
        }

        foreach (var source in sources)
        {
            writer.WriteLine();
            writer.WriteLine($"## `{source.SourceId}`");
            writer.WriteLine();
            writer.WriteLine($"- unresolved_subitems: {source.SubitemCount}");
            writer.WriteLine($"- mother_residual_atom_ids: {source.Atoms.Length}");
            writer.WriteLine();
            if (source.Atoms.Length == 0)
            {
                writer.WriteLine("Mother residual atoms: none.");
                continue;
            }

            writer.WriteLine("Mother residual atoms:");
            writer.WriteLine();
            foreach (var atom in source.Atoms)
            {
                writer.WriteLine($"- `{atom.AtomId}` ({atom.Subitems.Length})");
                foreach (var subitem in atom.Subitems)
                {
                    writer.WriteLine($"  - `{subitem}`");
                }
            }
        }

        return writer.ToString();
    }

    private sealed record AtomResiduals(string AtomId, string[] Subitems);

    private sealed record ResidueHost(string Residue, string SourceId, string AtomId);

    private sealed record SharedResidue(string Name, ResidueHost[] Hosts);

    private sealed record QuarantinedResiduals(
        string SourceId,
        string AtomId,
        DigestionQuarantine Quarantine,
        string[] Subitems);

    private sealed record SourceResiduals(string SourceId, AtomResiduals[] Atoms)
    {
        internal int SubitemCount => Atoms.Sum(static atom => atom.Subitems.Length);
    }
}
