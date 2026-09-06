using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CoverAtomCommand
{
    internal static CommandResult AlignScribeReceiptRefresh(
        string root,
        IRepositoryGateway repository,
        ILeanReportSource reportSource,
        IScribeEmissionVerifier verifier,
        IReadOnlyList<string> arguments,
        Func<string, string, ImmutableArray<byte>> readDocuments,
        Action<string, RawRepositorySnapshot, ImmutableArray<IngestCommand.LedgerUpdate>> applyUpdates)
    {
        var options = ParseRefreshArguments(arguments, root, readDocuments);
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
        var selectedDocuments = options.DocumentGids.ToHashSet(StringComparer.Ordinal);
        var closure = BackfillDeltaImpactResolver.ExpandScribeReceiptDocuments(
            document,
            selectedDocuments);
        var resolvedDocuments = closure
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

        var entries = document.RequireDigestionEntries();
        var plans = closure.Select(dependency => InspectRefresh(
                dependency,
                entries,
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
                RenderRefreshPlans(plans, options.DryRun, ledgerChanged: false),
                "ALIGN_SCRIBE_RECEIPT_INVALID "
                    + string.Join("; ", rejected.Select(static plan =>
                        $"{plan.Dependency.Entry.AtomId}:{plan.Dependency.Receipt.Gid}:{plan.Reason}"))
                    + "\n");
        }

        var replacements = plans.ToDictionary(
            static plan => RefreshKey(
                plan.Dependency.Entry.AtomId,
                plan.Dependency.Receipt.Gid),
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

        var closurePaths = closure
            .Select(static dependency => dependency.EntryPath)
            .Distinct(StringComparer.Ordinal)
            .ToImmutableArray();
        var closureChanges = RawChangeSet.Create(closurePaths);
        var derived = Evaluate(planned, current, closureChanges, validateStatus: false);
        var validationAtomIds = derived.Entries
            .Where(static item => item.StatusAuthorityChanged)
            .Select(static item => item.Entry.AtomId)
            .Concat(closure.Select(static dependency => dependency.Entry.AtomId))
            .ToHashSet(StringComparer.Ordinal);
        RequireNoRefreshIntegrityFailure(derived, validationAtomIds);
        var statusChanges = derived.Entries
            .Where(static item => item.StatusAuthorityChanged
                && item.DerivedStatus != item.Entry.ProjectedStatus)
            .ToDictionary(static item => item.Entry.AtomId, StringComparer.Ordinal);
        planned = MapRefreshDocument(planned, entry => statusChanges.TryGetValue(entry.AtomId, out var change)
            ? entry with { ProjectedStatus = change.DerivedStatus }
            : entry);

        var finalRaw = IngestCommand.ReplaceLedger(raw, document, planned);
        var final = Decode(finalRaw);
        LeanTruthStates.RequireSameManagedInputs(current, final);
        var updates = IngestCommand.LedgerUpdates(raw, finalRaw);
        var finalScope = RawChangeSet.Create(closurePaths.Concat(
            updates.Select(static update => update.Path)).Distinct(StringComparer.Ordinal));
        var finalEvaluation = Evaluate(
            BackfillInventoryLoader.Load(final),
            final,
            finalScope,
            validateStatus: true);
        RequireNoRefreshIntegrityFailure(finalEvaluation, validationAtomIds);

        if (!options.DryRun && updates.Length > 0)
        {
            var latest = repository.ReadCurrent();
            RequirePlannedEntriesUnchanged(raw, latest, updates);
            applyUpdates(root, latest, updates);
        }

        var ledgerChanged = !options.DryRun && updates.Length > 0;
        return new CommandResult(
            true,
            RenderRefreshPlans(plans, options.DryRun, ledgerChanged)
                + RenderRefreshWriteSet(updates),
            string.Empty);

        DigestionLedgerEvaluation Evaluate(
            BackfillInventoryDocument candidate,
            RepositorySnapshot snapshot,
            RawChangeSet changes,
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
                truthStates: states);
    }

    private static RefreshPlan InspectRefresh(
        BackfillScribeReceiptDependency dependency,
        ImmutableArray<DigestionLedgerEntry> allEntries,
        RepositorySnapshot current,
        LeanAxiomReport report,
        IReadOnlyDictionary<RepoPath, TruthState> states,
        FrozenStatementIndex frozen,
        VerifiedScribeEmissions verified)
    {
        var atomId = dependency.Entry.AtomId;
        var gidText = dependency.Receipt.Gid;
        var atomMatches = allEntries
            .Where(entry => string.Equals(entry.AtomId, atomId, StringComparison.Ordinal))
            .ToArray();
        if (atomMatches.Length != 1)
        {
            return Reject(dependency, "atom-cardinality-invalid");
        }

        var entry = atomMatches[0];
        if (entry.Coverage.Count(edge => string.Equals(
                edge.Gid,
                gidText,
                StringComparison.Ordinal)) != 1)
        {
            return Reject(dependency, "coverage-edge-cardinality-invalid");
        }

        if (entry.Receipts.Scribe.Count(receipt => string.Equals(
                receipt.Gid,
                gidText,
                StringComparison.Ordinal)) != 1)
        {
            return Reject(dependency, "scribe-receipt-cardinality-invalid");
        }

        if (!Gid.TryParse(gidText, out var gid)
            || gid.ToTarget() is not Target.Formal formal)
        {
            return Reject(dependency, "coverage-gid-invalid");
        }

        var edge = CurrentEdgeValidator.Validate(gidText, current, report, states, frozen);
        if (!edge.IsResolved || !edge.IsClosed)
        {
            return Reject(dependency, "target-not-closed:" + edge.Diagnostic);
        }

        var persistedTarget = AssertSingleEdge(entry, gidText).TargetStatementId;
        if (!string.Equals(persistedTarget, edge.TargetStatementId, StringComparison.Ordinal))
        {
            return Reject(dependency, "target-statement-identity-changed");
        }

        var definitionPath = ScribeEmissionAttestation.DefinitionPath(dependency.DocumentGid);
        if (!current.TryGetFile(definitionPath, out var definition))
        {
            return Reject(dependency, "scribe-definition-missing");
        }

        if (!verified.TryGet(dependency.DocumentGid, out var record))
        {
            return Reject(dependency, "scribe-emission-unverified");
        }

        var definitionSha256 = DigestionFingerprint.Compute(
            definition.RawBytes.AsSpan()).RawSha256;
        if (record.DefinitionPath != definitionPath
            || record.EmissionPath != ScribeEmissionAttestation.EmissionPath(dependency.DocumentGid)
            || record.DefinitionSha256 != definitionSha256)
        {
            return Reject(dependency, "scribe-document-verification-failed");
        }

        if (formal.Declaration is not null && !verified.ReferencesDeclaration(gidText))
        {
            return Reject(dependency, "declaration-reference-missing");
        }

        var refreshed = dependency.Receipt with
        {
            DefinitionSha256 = record.DefinitionSha256,
            EmissionSha256 = record.EmissionSha256,
        };
        var needed = refreshed != dependency.Receipt;
        return new RefreshPlan(
            dependency,
            Accepted: true,
            needed ? "needed" : "noop",
            string.Empty,
            refreshed);
    }

    private static DigestionCoverageEdge AssertSingleEdge(
        DigestionLedgerEntry entry,
        string gid) => entry.Coverage.Single(edge =>
        string.Equals(edge.Gid, gid, StringComparison.Ordinal));

    private static RefreshPlan Reject(
        BackfillScribeReceiptDependency dependency,
        string reason) => new(
        dependency,
        Accepted: false,
        "rejected",
        reason,
        RefreshedReceipt: null);

    private static RefreshOptions ParseRefreshArguments(
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

        return new RefreshOptions(
            ReadRefreshDocuments(readDocuments(root, path)),
            baseline,
            dryRun);
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
        $"SCRIBE_REFRESH atom_id={plan.Dependency.Entry.AtomId} "
        + $"gid={plan.Dependency.Receipt.Gid} document_gid={plan.Dependency.DocumentGid} "
        + $"refresh={plan.State} reason={plan.Reason} "
        + $"dry_run={dryRun.ToString().ToLowerInvariant()} "
        + $"ledger_changed={ledgerChanged.ToString().ToLowerInvariant()}\n"));

    private static string RenderRefreshWriteSet(
        ImmutableArray<IngestCommand.LedgerUpdate> updates) =>
        string.Concat(updates
            .OrderBy(static update => update.Path, StringComparer.Ordinal)
            .Select(static update => $"SCRIBE_REFRESH_WRITE path={update.Path}\n"))
        + $"SCRIBE_REFRESH_WRITE_SET count={updates.Length}\n";

    private static string RefreshKey(string atomId, string gid) => atomId + "\0" + gid;

    private static BackfillInventoryDocument MapRefreshDocument(
        BackfillInventoryDocument document,
        Func<DigestionLedgerEntry, DigestionLedgerEntry> transform) =>
        document.WithDigestionSources(document.RequireDigestionSources().Select(source => source with
        {
            Entries = source.Entries.Select(transform).ToImmutableArray(),
        }).ToImmutableArray());

    private sealed record RefreshOptions(
        ImmutableArray<string> DocumentGids,
        string BaseRevision,
        bool DryRun);

    private sealed record RefreshPlan(
        BackfillScribeReceiptDependency Dependency,
        bool Accepted,
        string State,
        string Reason,
        DigestionScribeReceipt? RefreshedReceipt);
}
