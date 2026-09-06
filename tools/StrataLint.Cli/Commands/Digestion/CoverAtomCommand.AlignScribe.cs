using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CoverAtomCommand
{
    internal static CommandResult AlignScribeReceipt(
        string root,
        IRepositoryGateway repository,
        ILeanReportSource reportSource,
        IScribeEmissionVerifier verifier,
        IReadOnlyList<string> arguments,
        Func<string, string, ImmutableArray<byte>>? readDocuments = null,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>>? applyUpdates = null)
    {
        var options = ParseAlignArguments(arguments, root, readDocuments);
        var raw = repository.ReadCurrent();
        var current = Decode(raw);
        var baseline = Decode(repository.ReadRevision(options.BaseRevision));
        var document = BackfillInventoryLoader.Load(current);
        var baselineDocument = BackfillInventoryLoader.LoadBaseline(baseline);
        var report = reportSource.Load(current);
        var lean = LeanClosureValidator.Validate(current, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
        var states = LeanTruthStates.Resolve(current, lean);
        var frozen = FrozenStatementIndex.Create(FrozenStateCatalog.Load(current), report);
        var verified = verifier.Verify(current, report);
        var pairs = ResolveAlignPairs(options, document);
        var entries = document.RequireDigestionEntries();
        var baselineEntries = baselineDocument.RequireDigestionEntries();
        var plans = pairs.Select(pair => InspectRefresh(
                pair,
                entries,
                baselineEntries,
                current,
                report,
                states,
                frozen,
                verified))
            .ToImmutableArray();
        if (plans.Any(static plan => !plan.Accepted))
        {
            var rejected = plans.Where(static plan => !plan.Accepted).ToArray();
            return new CommandResult(
                false,
                options.IsDocumentSelection
                    ? RenderRefreshPlans(plans, options.DryRun, ledgerChanged: false)
                    : string.Empty,
                "ALIGN_SCRIBE_RECEIPT_INVALID "
                    + string.Join("; ", rejected.Select(static plan =>
                        $"{plan.Pair.AtomId}:{plan.Pair.Gid}:{plan.Reason}"))
                    + "\n");
        }

        var replacements = plans.ToDictionary(
            static plan => RefreshKey(plan.Pair.AtomId, plan.Pair.Gid),
            static plan => plan.RefreshedReceipt!,
            StringComparer.Ordinal);
        var planned = MapRefreshDocument(document, entry =>
        {
            var relevant = entry.Receipts.Scribe.Any(receipt =>
                replacements.ContainsKey(RefreshKey(entry.AtomId, receipt.Gid)));
            return relevant
                ? entry with
                {
                    Receipts = entry.Receipts with
                    {
                        Scribe = entry.Receipts.Scribe.Select(receipt =>
                            replacements.GetValueOrDefault(
                                RefreshKey(entry.AtomId, receipt.Gid),
                                receipt)).ToImmutableArray(),
                    },
                }
                : entry;
        });

        var selectedAtomIds = plans
            .Select(static plan => plan.Pair.AtomId)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var authorizedClosure = DigestionStatusEvaluator.ExpandStatusAuthorityChanges(
            entries,
            selectedAtomIds);
        var selectedDocumentGids = plans
            .Select(static plan => plan.DocumentGid)
            .ToHashSet(StringComparer.Ordinal);
        var dependencyEntries = entries
            .Where(entry => entry.Receipts.Scribe.Any(receipt =>
                Gid.TryParse(receipt.Gid, out _)
                && selectedDocumentGids.Contains(
                    ScribeEmissionAttestation.DocumentGid(receipt.Gid))))
            .ToArray();
        var validationClosure = authorizedClosure.Union(
            dependencyEntries.Select(static entry => entry.AtomId));
        var selectedPaths = plans
            .Select(static plan => plan.EntryPath!)
            .Distinct(StringComparer.Ordinal)
            .ToImmutableArray();
        var validationPaths = dependencyEntries
            .Select(RefreshEntryPath)
            .Concat(selectedPaths)
            .Distinct(StringComparer.Ordinal)
            .ToImmutableArray();
        var derived = Evaluate(
            planned,
            current,
            RawChangeSet.Create(validationPaths),
            RawChangeSet.Create(selectedPaths),
            validateStatus: false);
        RequireNoRefreshIntegrityFailure(derived, validationClosure);
        var statusChanges = derived.Entries
            .Where(static item => item.StatusAuthorityChanged
                && item.DerivedStatus != item.Entry.ProjectedStatus)
            .ToDictionary(static item => item.Entry.AtomId, StringComparer.Ordinal);
        RequireRefreshStatusChangesInsideClosure(statusChanges.Keys, authorizedClosure);
        planned = MapRefreshDocument(planned, entry =>
            statusChanges.TryGetValue(entry.AtomId, out var change)
                ? entry with { ProjectedStatus = change.DerivedStatus }
                : entry);

        var finalRaw = IngestCommand.ReplaceLedger(raw, document, planned);
        var final = Decode(finalRaw);
        LeanTruthStates.RequireSameManagedInputs(current, final);
        var updates = IngestCommand.LedgerUpdates(raw, finalRaw);
        var finalValidationScope = RawChangeSet.Create(validationPaths.Concat(
            updates.Select(static update => update.Path)).Distinct(StringComparer.Ordinal));
        var finalStatusScope = RawChangeSet.Create(selectedPaths.Concat(
            updates.Select(static update => update.Path)).Distinct(StringComparer.Ordinal));
        var finalEvaluation = Evaluate(
            BackfillInventoryLoader.Load(final),
            final,
            finalValidationScope,
            finalStatusScope,
            validateStatus: true);
        RequireNoRefreshIntegrityFailure(finalEvaluation, validationClosure);

        if (!options.DryRun && updates.Length > 0)
        {
            var latest = repository.ReadCurrent();
            RequirePlannedEntriesUnchanged(raw, latest, updates);
            (applyUpdates ?? (static (repositoryRoot, currentRaw, ledgerUpdates) =>
                IngestCommand.ApplyLedgerUpdatesAtomically(repositoryRoot, currentRaw, ledgerUpdates)))(
                root,
                latest,
                updates);
        }

        var ledgerChanged = !options.DryRun && updates.Length > 0;
        var output = options.IsDocumentSelection
            ? RenderRefreshPlans(plans, options.DryRun, ledgerChanged)
                + RenderRefreshWriteSet(updates)
            : RenderAlignPlans(plans, ledgerChanged);
        return new CommandResult(true, output, string.Empty);

        DigestionLedgerEvaluation Evaluate(
            BackfillInventoryDocument candidate,
            RepositorySnapshot snapshot,
            RawChangeSet changes,
            RawChangeSet projectedStatusChanges,
            bool validateStatus) =>
            DigestionStatusEvaluator.Evaluate(
                DigestionEvaluationScope.ChangedSet,
                candidate,
                snapshot,
                lean,
                verified,
                baselineDocument,
                validateProjectedStatus: validateStatus,
                baselineSnapshot: baseline,
                changes: changes,
                projectedStatusChanges: projectedStatusChanges,
                truthStates: states);
    }

    private static ImmutableArray<AlignPair> ResolveAlignPairs(
        AlignOptions options,
        BackfillInventoryDocument document)
    {
        if (!options.IsDocumentSelection)
        {
            return options.Pairs;
        }

        var selectedDocuments = options.DocumentGids.ToHashSet(StringComparer.Ordinal);
        var dependencies = BackfillDeltaImpactResolver.ExpandScribeReceiptDocuments(
            document,
            selectedDocuments);
        var resolvedDocuments = dependencies
            .Select(static dependency => dependency.DocumentGid)
            .ToHashSet(StringComparer.Ordinal);
        var unresolvedDocuments = selectedDocuments
            .Except(resolvedDocuments, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (unresolvedDocuments.Length > 0)
        {
            throw new InvalidOperationException(
                "document-selection-unresolved: " + string.Join(',', unresolvedDocuments));
        }

        return dependencies
            .Select(static dependency => new AlignPair(
                dependency.Entry.AtomId,
                dependency.Receipt.Gid))
            .ToImmutableArray();
    }

    private static RefreshPlan InspectRefresh(
        AlignPair pair,
        ImmutableArray<DigestionLedgerEntry> allEntries,
        ImmutableArray<DigestionLedgerEntry> baselineEntries,
        RepositorySnapshot current,
        LeanAxiomReport report,
        IReadOnlyDictionary<RepoPath, TruthState> states,
        FrozenStatementIndex frozen,
        VerifiedScribeEmissions verified)
    {
        var atomMatches = allEntries
            .Where(entry => string.Equals(entry.AtomId, pair.AtomId, StringComparison.Ordinal))
            .ToArray();
        if (atomMatches.Length != 1)
        {
            return Reject(pair, "atom-cardinality-invalid");
        }

        var entry = atomMatches[0];
        var edges = entry.Coverage
            .Where(edge => string.Equals(edge.Gid, pair.Gid, StringComparison.Ordinal))
            .ToArray();
        if (edges.Length != 1)
        {
            return Reject(pair, "coverage-edge-cardinality-invalid");
        }

        var receiptMatches = entry.Receipts.Scribe
            .Where(receipt => string.Equals(receipt.Gid, pair.Gid, StringComparison.Ordinal))
            .ToArray();
        if (receiptMatches.Length != 1)
        {
            return Reject(pair, "scribe-receipt-cardinality-invalid");
        }

        var baselineAtomMatches = baselineEntries
            .Where(candidate => string.Equals(candidate.AtomId, pair.AtomId, StringComparison.Ordinal))
            .ToArray();
        if (baselineAtomMatches.Length != 1)
        {
            return Reject(pair, "protected-base-atom-identity-absent");
        }

        if (!Gid.TryParse(pair.Gid, out var gid)
            || gid.ToTarget() is not Target.Formal formal)
        {
            return Reject(pair, "coverage-gid-invalid");
        }

        var edge = CurrentEdgeValidator.Validate(pair.Gid, current, report, states, frozen);
        if (!edge.IsResolved || !edge.IsClosed)
        {
            return Reject(pair, "target-not-closed:" + edge.Diagnostic);
        }

        if (!string.Equals(edges[0].TargetStatementId, edge.TargetStatementId, StringComparison.Ordinal))
        {
            return Reject(pair, "coverage-target-mismatch");
        }

        var baselineEntry = baselineAtomMatches[0];
        if (baselineEntry.Coverage.Count(candidate =>
                string.Equals(candidate.Gid, pair.Gid, StringComparison.Ordinal)
                && string.Equals(
                    candidate.TargetStatementId,
                    edges[0].TargetStatementId,
                    StringComparison.Ordinal)) != 1)
        {
            return Reject(pair, "protected-base-coverage-edge-identity-absent");
        }

        if (baselineEntry.Receipts.Scribe.Count(receipt =>
                string.Equals(receipt.Gid, pair.Gid, StringComparison.Ordinal)) != 1)
        {
            return Reject(pair, "protected-base-scribe-receipt-identity-absent");
        }

        var documentGid = ScribeEmissionAttestation.DocumentGid(pair.Gid);
        var definitionPath = ScribeEmissionAttestation.DefinitionPath(documentGid);
        if (!current.TryGetFile(definitionPath, out var definition))
        {
            return Reject(pair, "scribe-definition-missing");
        }

        if (!verified.TryGet(documentGid, out var record))
        {
            return Reject(pair, "scribe-emission-unverified");
        }

        var definitionSha256 = DigestionFingerprint.Compute(
            definition.RawBytes.AsSpan()).RawSha256;
        if (record.DefinitionSha256 != definitionSha256)
        {
            return Reject(pair, "scribe-definition-mismatch");
        }

        if (record.DefinitionPath != definitionPath
            || record.EmissionPath != ScribeEmissionAttestation.EmissionPath(documentGid))
        {
            return Reject(pair, "scribe-document-verification-failed");
        }

        if (formal.Declaration is not null && !verified.ReferencesDeclaration(pair.Gid))
        {
            return Reject(pair, "declaration-reference-missing");
        }

        var oldReceipt = receiptMatches[0];
        var refreshed = oldReceipt with
        {
            DefinitionSha256 = record.DefinitionSha256,
            EmissionSha256 = record.EmissionSha256,
        };
        return new RefreshPlan(
            pair,
            documentGid,
            RefreshEntryPath(entry),
            oldReceipt,
            Accepted: true,
            refreshed == oldReceipt ? "noop" : "needed",
            string.Empty,
            refreshed);
    }

    private static RefreshPlan Reject(AlignPair pair, string reason) => new(
        pair,
        Gid.TryParse(pair.Gid, out _)
            ? ScribeEmissionAttestation.DocumentGid(pair.Gid)
            : string.Empty,
        EntryPath: null,
        OldReceipt: null,
        Accepted: false,
        "rejected",
        reason,
        RefreshedReceipt: null);

    private static AlignOptions ParseAlignArguments(
        IReadOnlyList<string> arguments,
        string root,
        Func<string, string, ImmutableArray<byte>>? readDocuments)
    {
        if (arguments.Contains("--refresh", StringComparer.Ordinal))
        {
            return ParseRefreshArguments(
                arguments,
                root,
                readDocuments ?? throw new InvalidOperationException(AlignScribeReceiptCommand.Usage));
        }

        string? baselineRevision = null;
        string? pendingAtomId = null;
        var pairs = ImmutableArray.CreateBuilder<AlignPair>();
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count)
            {
                throw AlignUsage();
            }

            var value = arguments[index + 1];
            switch (arguments[index])
            {
                case "--atom-id" when pendingAtomId is null:
                    pendingAtomId = value;
                    break;
                case "--gid" when pendingAtomId is not null:
                    pairs.Add(new AlignPair(pendingAtomId, value));
                    pendingAtomId = null;
                    break;
                case "--base" when baselineRevision is null:
                    baselineRevision = value;
                    break;
                default:
                    throw AlignUsage();
            }
        }

        if (pendingAtomId is not null
            || pairs.Count == 0
            || string.IsNullOrWhiteSpace(baselineRevision)
            || pairs.Any(pair =>
                string.IsNullOrWhiteSpace(pair.AtomId) || string.IsNullOrWhiteSpace(pair.Gid))
            || pairs.Distinct().Count() != pairs.Count)
        {
            throw AlignUsage();
        }

        return new AlignOptions(
            pairs.ToImmutable(),
            DocumentGids: [],
            baselineRevision,
            DryRun: false,
            IsDocumentSelection: false);
    }

    private static AlignOptions ParseRefreshArguments(
        IReadOnlyList<string> arguments,
        string root,
        Func<string, string, ImmutableArray<byte>> readDocuments)
    {
        string? path = null, baseline = null;
        var refresh = false;
        var dryRun = false;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--refresh" when !refresh: refresh = true; break;
                case "--dry-run" when !dryRun: dryRun = true; break;
                case "--documents" when path is null: path = Value(); break;
                case "--base" when baseline is null: baseline = Value(); break;
                default: throw new InvalidOperationException(AlignScribeReceiptCommand.Usage);
            }

            string Value()
            {
                if (++index >= arguments.Count
                    || string.IsNullOrWhiteSpace(arguments[index])
                    || arguments[index] != arguments[index].Trim()
                    || arguments[index].StartsWith("--", StringComparison.Ordinal))
                {
                    throw new InvalidOperationException(AlignScribeReceiptCommand.Usage);
                }

                return arguments[index];
            }
        }

        if (!refresh || path is null || baseline is null)
        {
            throw new InvalidOperationException(AlignScribeReceiptCommand.Usage);
        }

        return new AlignOptions(
            Pairs: [],
            ReadRefreshDocuments(readDocuments(root, path)),
            baseline,
            dryRun,
            IsDocumentSelection: true);
    }

    private static ImmutableArray<string> ReadRefreshDocuments(ImmutableArray<byte> bytes)
    {
        if (bytes.IsEmpty
            || bytes[^1] != (byte)'\n'
            || bytes.AsSpan().Contains((byte)'\r')
            || bytes.AsSpan().StartsWith(Encoding.UTF8.Preamble))
        {
            throw new InvalidOperationException(
                "REFRESH_DOCUMENTS_INVALID expected UTF-8 without BOM/CR, ending in LF");
        }

        string text;
        try
        {
            text = new UTF8Encoding(false, true).GetString(bytes.AsSpan());
        }
        catch (DecoderFallbackException exception)
        {
            throw new InvalidOperationException("REFRESH_DOCUMENTS_INVALID UTF-8", exception);
        }

        var result = ImmutableArray.CreateBuilder<string>();
        using var reader = new StringReader(text);
        while (reader.ReadLine() is { } line)
        {
            if (string.IsNullOrWhiteSpace(line)
                || line != line.Trim()
                || !Gid.TryParse(line, out var gid)
                || gid.ToTarget() is not Target.Formal { Declaration: null })
            {
                throw new InvalidOperationException(
                    "REFRESH_DOCUMENTS_INVALID expected one Formal module GID per line");
            }

            result.Add(line);
        }

        var documents = result.ToImmutable();
        if (documents.IsEmpty || documents.Distinct(StringComparer.Ordinal).Count() != documents.Length)
        {
            throw new InvalidOperationException(
                "REFRESH_DOCUMENTS_INVALID document GIDs must be nonempty and unique");
        }

        return documents;
    }

    private static InvalidOperationException AlignUsage() => new(
        "USAGE: StrataLint align-scribe-receipt (--atom-id ATOM_ID --gid GID)+ --base REV");

    internal static void RequireRefreshStatusChangesInsideClosure(
        IEnumerable<string> changedAtomIds,
        IReadOnlySet<string> authorizedClosure)
    {
        var outside = changedAtomIds
            .Where(atomId => !authorizedClosure.Contains(atomId))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (outside.Length > 0)
        {
            throw new InvalidOperationException(
                "status-change-outside-refresh-closure: " + string.Join(',', outside));
        }
    }

    private static void RequirePlannedEntriesUnchanged(
        RawRepositorySnapshot plannedFrom,
        RawRepositorySnapshot latest,
        ImmutableArray<IngestCommand.LedgerUpdate> updates)
    {
        var expected = plannedFrom.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var actual = latest.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        foreach (var path in updates.Select(static update => update.Path).Distinct(StringComparer.Ordinal))
        {
            var expectedPresent = expected.TryGetValue(path, out var expectedEntry);
            var actualPresent = actual.TryGetValue(path, out var actualEntry);
            if (expectedPresent != actualPresent
                || expectedPresent
                && !expectedEntry!.Bytes.AsSpan().SequenceEqual(actualEntry!.Bytes.AsSpan()))
            {
                throw new InvalidOperationException(
                    $"ledger entry changed under us after planning: {path}");
            }
        }
    }

    private static void RequireNoRefreshIntegrityFailure(
        DigestionLedgerEvaluation evaluation,
        IReadOnlySet<string> validationAtomIds)
    {
        var reasons = evaluation.Findings.Concat(evaluation.ReceiptIntegrityGaps
                .Where(item => validationAtomIds.Contains(item.Entry.AtomId))
                .Select(static item =>
                    $"{item.Entry.AtomId}:{item.Gap.Code}:{item.Gap.Detail}"))
            .ToArray();
        if (reasons.Length > 0)
        {
            throw new InvalidOperationException(
                "digest status is invalid: " + string.Join("; ", reasons));
        }
    }

    private static string RenderRefreshPlans(
        IEnumerable<RefreshPlan> plans,
        bool dryRun,
        bool ledgerChanged) => string.Concat(plans.Select(plan =>
        $"SCRIBE_REFRESH atom_id={plan.Pair.AtomId} "
        + $"gid={plan.Pair.Gid} document_gid={plan.DocumentGid} "
        + $"refresh={plan.State} reason={plan.Reason} "
        + $"dry_run={dryRun.ToString().ToLowerInvariant()} "
        + $"ledger_changed={ledgerChanged.ToString().ToLowerInvariant()}\n"));

    private static string RenderAlignPlans(
        IEnumerable<RefreshPlan> plans,
        bool ledgerChanged) => string.Concat(plans.Select(plan =>
        $"ALIGN_SCRIBE_RECEIPT atom_id={plan.Pair.AtomId} gid={plan.Pair.Gid} "
        + $"old_definition_sha256={plan.OldReceipt!.DefinitionSha256} "
        + $"new_definition_sha256={plan.RefreshedReceipt!.DefinitionSha256} "
        + $"old_emission_sha256={plan.OldReceipt.EmissionSha256} "
        + $"new_emission_sha256={plan.RefreshedReceipt.EmissionSha256} "
        + $"ledger_changed={ledgerChanged.ToString().ToLowerInvariant()}\n"));

    private static string RenderRefreshWriteSet(
        ImmutableArray<IngestCommand.LedgerUpdate> updates) =>
        string.Concat(updates
            .OrderBy(static update => update.Path, StringComparer.Ordinal)
            .Select(static update => $"SCRIBE_REFRESH_WRITE path={update.Path}\n"))
        + $"SCRIBE_REFRESH_WRITE_SET count={updates.Length}\n";

    private static string RefreshKey(string atomId, string gid) => atomId + "\0" + gid;

    private static string RefreshEntryPath(DigestionLedgerEntry entry) =>
        BackfillInventoryLoader.RootPath + entry.SourceId + "/"
        + DigestionStatusNames.Migration(entry.ProjectedStatus.Migration) + "-"
        + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth) + "/"
        + entry.AtomId + ".yaml";

    private static BackfillInventoryDocument MapRefreshDocument(
        BackfillInventoryDocument document,
        Func<DigestionLedgerEntry, DigestionLedgerEntry> transform) =>
        document.WithDigestionSources(document.RequireDigestionSources().Select(source => source with
        {
            Entries = source.Entries.Select(transform).ToImmutableArray(),
        }).ToImmutableArray());

    private sealed record AlignOptions(
        ImmutableArray<AlignPair> Pairs,
        ImmutableArray<string> DocumentGids,
        string BaseRevision,
        bool DryRun,
        bool IsDocumentSelection);

    private sealed record RefreshPlan(
        AlignPair Pair,
        string DocumentGid,
        string? EntryPath,
        DigestionScribeReceipt? OldReceipt,
        bool Accepted,
        string State,
        string Reason,
        DigestionScribeReceipt? RefreshedReceipt);
}
