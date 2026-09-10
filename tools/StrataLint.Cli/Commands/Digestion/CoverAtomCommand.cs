using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

// Phase 1 cover transaction: bind one or more already-proven Lean declarations to an
// existing open residual atom by writing a coverage edge.
// cover is the narrow sibling of ingest — it reuses
// DigestionStatusEvaluator for the structural gates and never adds residual
// atoms or rebinds boundaries. The write is all-or-nothing with a fail-closed
// check-then-act guard: every gate must pass and the on-disk ledger must still
// exist and be unchanged before ReplaceLedgerAtomically touches disk, otherwise
// BACKFILL.yaml is byte-unchanged. This is not a true CAS/lock — a residual
// sub-millisecond TOCTOU window remains between the reread and the atomic rename
// (serialized manual/CI invocation makes it sufficient; an OS file lock for a
// hard guarantee is deferred).
//
// kind exclusion remains a producer responsibility (spec section 5), not cover's.
internal static partial class CoverAtomCommand
{
    private const string ImplementationPath =
        "tools/StrataLint.Cli/Commands/Digestion/CoverAtomCommand.cs";

    internal static CommandResult Run(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        DateTimeOffset recordedAtUtc,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var options = ParseArguments(arguments);
            var session = new Session(repositoryRoot, repository, leanReportSource,
                scribeEmissionVerifier, recordedAtUtc, options.BaselineRevision, options.Gids[0]);
            return Apply(session, options, allowAlreadyApplied: false);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"COVER_INVALID {exception.Message}\n");
        }
    }

    private static CommandResult Apply(Session session, CoverArguments options, bool allowAlreadyApplied)
    {
        try
        {
            var currentRaw = session.CurrentRaw;
            var current = session.Current;
            var baseline = session.Baseline;
            var document = session.Document;
            var baselineDocument = session.BaselineDocument;
            var report = session.Report;
            var lean = session.Lean;

            // Gate ②(a): every cover GID must select a Lean declaration, not just a
            // module (module-level coverage is ingest's residual boundary, not a
            // single truth atom).
            var gids = options.Gids.Select(gidText =>
            {
                if (!Gid.TryParse(gidText, out var gid)
                    || gid.ToTarget() is not Target.Formal { Declaration: not null })
                {
                    throw new InvalidOperationException(
                        $"cover GID must select a Lean declaration: {gidText}");
                }

                return gid;
            }).ToImmutableArray();
            var frozenState = session.FrozenState;

            foreach (var gid in gids)
            {
                if (!frozenState.Records.ContainsKey(gid.Path))
                {
                    throw new InvalidOperationException(
                        $"cover target module {gid.Path.Value} is not frozen; "
                        + "run make deposit before cover");
                }
            }
            var frozenStatements = session.FrozenStatements;

            // Gate ①: locate the single target atom. An initial cover requires an
            // open atom; a hosted extension adds at least one declaration while
            // retaining all existing coverage.
            var sources = document.RequireDigestionSources();
            var target = LocateTarget(sources, options.AtomId, options.Gids, allowAlreadyApplied);
            var existingGids = target.CoverageGids.ToImmutableHashSet(StringComparer.Ordinal);
            var addedGids = options.Gids.Where(gid => !existingGids.Contains(gid)).ToImmutableArray();
            var repositoryChanges = session.Changes;
            var inputPaths = new HashSet<string>(StringComparer.Ordinal);
            var authorityEntryPaths = new HashSet<string>(StringComparer.Ordinal);
            var entriesByAtomId = document.RequireDigestionEntries()
                .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
                .Where(static group => group.Count() == 1)
                .ToDictionary(static group => group.Key, static group => group.Single(), StringComparer.Ordinal);
            var pendingAtomIds = new Stack<string>();
            var scopedAtomIds = new HashSet<string>(StringComparer.Ordinal);
            pendingAtomIds.Push(target.AtomId);
            while (pendingAtomIds.TryPop(out var atomId))
            {
                if (!scopedAtomIds.Add(atomId)
                    || !entriesByAtomId.TryGetValue(atomId, out var entry))
                {
                    continue;
                }

                var state = DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
                    + "-"
                    + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
                var entryPath =
                    $"{BackfillInventoryLoader.RootPath}{entry.SourceId}/{state}/{entry.AtomId}.yaml";
                inputPaths.Add(entryPath);
                authorityEntryPaths.Add(entryPath);
                inputPaths.Add($"{BackfillInventoryLoader.RootPath}{entry.SourceId}/source.toml");
                inputPaths.Add(entry.SourcePath);
                if (DigestionFingerprint.IsCanonicalSha256(entry.CasRef))
                {
                    inputPaths.Add(DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..]);
                }

                if (entry.Receipts.TailAuthorization is { } tailAuthorization)
                {
                    inputPaths.Add(tailAuthorization.Path);
                }

                foreach (var chainedAtomId in entry.Receipts.ChainAtoms)
                {
                    pendingAtomIds.Push(chainedAtomId);
                }

                foreach (var gidText in entry.CoverageGids)
                {
                    AddGidInputs(gidText);
                }
            }

            foreach (var gid in gids)
            {
                AddGidInputs(gid.Value);
            }

            void AddGidInputs(string gidText)
            {
                if (!Gid.TryParse(gidText, out var gid))
                {
                    return;
                }

                inputPaths.Add(gid.Path.Value);
                var documentGid = ScribeEmissionAttestation.DocumentGid(gidText);
                inputPaths.Add(ScribeEmissionAttestation.DefinitionPath(documentGid));
                inputPaths.Add(ScribeEmissionAttestation.EmissionPath(documentGid));
            }

            var repositoryPaths = repositoryChanges.Entries
                .Select(static entry => entry.Path.Value)
                .ToHashSet(StringComparer.Ordinal);
            var authorityChanges = RawChangeSet.CreateWithKinds(
                repositoryChanges.Entries
                    .Select(static entry => (Path: entry.Path.Value, Kind: entry.Kind))
                    .Concat(authorityEntryPaths
                        .Where(path => !repositoryPaths.Contains(path))
                        .Select(static path => (Path: path, Kind: RawChangeKind.Modified)))
                    .OrderBy(static entry => entry.Path, StringComparer.Ordinal));
            var authorityImpact = BackfillDeltaImpactResolver.Resolve(
                current,
                baseline,
                report,
                document,
                authorityChanges,
                frozenState: frozenState,
                frozenStatements: frozenStatements);
            var authorityPaths = authorityChanges.Paths
                .Select(static path => path.Value)
                .ToHashSet(StringComparer.Ordinal);
            var receiptSeedChanges = RawChangeSet.CreateWithKinds(
                authorityChanges.Entries
                    .Select(static entry => (Path: entry.Path.Value, Kind: entry.Kind))
                    .Concat(inputPaths
                        .Where(path => !authorityPaths.Contains(path) && ValueChanged(path))
                        .Select(static path => (Path: path, Kind: RawChangeKind.Modified)))
                    .OrderBy(static entry => entry.Path, StringComparer.Ordinal));
            var receiptImpact = BackfillDeltaImpactResolver.Resolve(
                current,
                baseline,
                report,
                document,
                receiptSeedChanges,
                frozenState: frozenState,
                frozenStatements: frozenStatements);
            var evaluationChanges = authorityImpact.EvaluationChanges;
            var receiptVerificationChanges = receiptImpact.ReceiptVerificationChanges;
            var evaluationScope = DigestionEvaluationScopes.ForChanges(
                authorityChanges,
                ImplementationPath);

            bool ValueChanged(string path)
            {
                var currentExists = current.TryGetFile(path, out var currentFile);
                var baselineExists = baseline.TryGetFile(path, out var baselineFile);
                return currentExists != baselineExists
                    || currentExists
                    && !currentFile!.RawBytes.AsSpan().SequenceEqual(
                        baselineFile!.RawBytes.AsSpan());
            }
            var truthStates = session.TruthStates;
            var addedCoverage = ImmutableArray.CreateBuilder<DigestionCoverageEdge>();
            foreach (var gid in gids)
            {
                var edge = CurrentEdgeValidator.Validate(
                    gid.Value,
                    current,
                    report,
                    truthStates,
                    frozenStatements);
                if (!edge.IsClosed)
                {
                    throw new InvalidOperationException(edge.Diagnostic);
                }

                if (!existingGids.Contains(gid.Value))
                {
                    addedCoverage.Add(new DigestionCoverageEdge(gid.Value, edge.TargetStatementId));
                }
                else if (allowAlreadyApplied && !string.Equals(
                             target.Coverage.Single(coverage => coverage.Gid == gid.Value).TargetStatementId,
                             edge.TargetStatementId, StringComparison.Ordinal))
                {
                    throw new InvalidOperationException($"coverage-target-mismatch: {gid.Value}");
                }
            }

            session.Scribe.Verify(
                current,
                report,
                receiptVerificationChanges,
                session.FrozenState,
                session.FrozenStatements);
            var beforeEvaluation = DigestionStatusEvaluator.Evaluate(
                evaluationScope,
                document,
                current,
                lean,
                baselineDocument,
                baselineSnapshot: baseline,
                changes: receiptVerificationChanges,
                projectedStatusChanges: evaluationChanges,
                truthStates: truthStates,
                frozenStatementIndex: frozenStatements);
            IngestCommand.RequireNoReceiptIntegrityFailure(beforeEvaluation);

            if (allowAlreadyApplied && addedGids.Length == 0)
            {
                session.RequireUnchanged();
                return new CommandResult(true,
                    $"COVER atom_id={options.AtomId} ledger_changed=false\n", string.Empty);
            }

            var covered = target with
            {
                Coverage = target.Coverage.AddRange(addedCoverage),
                Receipts = target.Receipts with
                {
                    CoverDisposition = null,
                },
            };
            var plannedDocument = ReplaceEntry(document, options.AtomId, covered);

            var derived = DigestionStatusEvaluator.Evaluate(
                evaluationScope,
                plannedDocument,
                current,
                lean,
                baselineDocument,
                validateProjectedStatus: false,
                baselineSnapshot: baseline,
                changes: receiptVerificationChanges,
                projectedStatusChanges: evaluationChanges,
                truthStates: truthStates,
                frozenStatementIndex: frozenStatements);
            IngestCommand.RequireNoReceiptIntegrityFailure(derived);

            var statusByAtomId = derived.Entries.ToDictionary(
                static item => item.Entry.AtomId,
                static item => item.DerivedStatus,
                StringComparer.Ordinal);
            var refreshed = plannedDocument.WithDigestionSources(
                plannedDocument.RequireDigestionSources()
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

            var finalRaw = IngestCommand.ReplaceLedger(
                currentRaw,
                document,
                refreshed);
            var finalSnapshot = Decode(finalRaw);
            LeanTruthStates.RequireSameManagedInputs(current, finalSnapshot);
            var finalDocument = LoadDocument(finalSnapshot);
            var evaluation = DigestionStatusEvaluator.Evaluate(
                evaluationScope,
                finalDocument,
                finalSnapshot,
                lean,
                baselineDocument,
                baselineSnapshot: baseline,
                changes: receiptVerificationChanges,
                projectedStatusChanges: evaluationChanges,
                truthStates: truthStates,
                frozenStatementIndex: frozenStatements);
            IngestCommand.RequireNoReceiptIntegrityFailure(evaluation);
            var backfillObservations = DigestionBackfillValidation.RequireValidBackfill(
                finalDocument,
                finalSnapshot,
                baseline,
                session.Policy,
                lean,
                DigestionEvaluationScopes.ResolveChanges(
                    evaluationScope,
                    receiptVerificationChanges),
                projectedStatusChanges: DigestionEvaluationScopes.ResolveChanges(
                    evaluationScope,
                    evaluationChanges),
                baselineDocument: baselineDocument,
                frozenStatementIndex: frozenStatements,
                truthStates: truthStates);

            var finalTarget = EvaluationFor(evaluation, options.AtomId);
            if (target.CoverageGids.Length == 0)
            {
                // Initial cover keeps the old semantics exactly: the atom must become
                // deletable Closed with no residual gap.
                if (!IsClosedDeletable(finalTarget))
                {
                    RecordCoverDisposition(
                        session,
                        target,
                        finalTarget,
                        options.Gids);
                }

                RequireClosedDeletable(finalTarget);
            }
            else
            {
                // A validated receipt host may append Closed declarations without
                // pretending that its remaining semantic residuals were discharged.
                // Its migration/truth projection and gap set may only stay equal or
                // improve.
                RequireHostedExtension(
                    EvaluationFor(beforeEvaluation, options.AtomId),
                    finalTarget,
                    addedGids,
                    truthStates);
            }

            var ledgerUpdates = IngestCommand.LedgerUpdates(currentRaw, finalRaw, document, finalDocument);
            var changed = ledgerUpdates.Length > 0;
            session.Commit(finalRaw, finalSnapshot, finalDocument, ledgerUpdates);

            return new CommandResult(
                true,
                $"COVER atom_id={options.AtomId} gid={string.Join(',', options.Gids)} "
                + $"ledger_changed={changed.ToString().ToLowerInvariant()}\n"
                + backfillObservations
                + (allowAlreadyApplied ? string.Empty : DigestStatusCommand.RenderText(evaluation)),
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(false, string.Empty, $"COVER_INVALID {exception.Message}\n");
        }
    }

    private static DigestionLedgerEntry LocateTarget(
        ImmutableArray<DigestionLedgerSource> sources,
        string atomId,
        ImmutableArray<string> requestedGids,
        bool allowAlreadyApplied)
    {
        var matches = sources
            .SelectMany(static source => source.Entries)
            .Where(entry => string.Equals(entry.AtomId, atomId, StringComparison.Ordinal))
            .ToArray();
        if (matches.Length == 0)
        {
            throw new InvalidOperationException($"cover atom {atomId} is absent from the ledger");
        }

        if (matches.Length > 1)
        {
            throw new InvalidOperationException($"cover atom {atomId} is ambiguous in the ledger");
        }

        var entry = matches[0];
        if (entry.CoverageGids.Length == 0
            && entry.ProjectedStatus.Truth != DigestionTruthState.Open)
        {
            throw new InvalidOperationException(
                $"cover atom {atomId} is not open "
                + $"(truth={DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)})");
        }

        var existing = entry.CoverageGids.ToImmutableHashSet(StringComparer.Ordinal);
        if (!allowAlreadyApplied && entry.CoverageGids.Length > 0 && requestedGids.All(existing.Contains))
        {
            throw new InvalidOperationException(
                $"cover atom {atomId} already has coverage: "
                + string.Join(", ", entry.CoverageGids));
        }

        return entry;
    }

    private static BackfillInventoryDocument ReplaceEntry(
        BackfillInventoryDocument document,
        string atomId,
        DigestionLedgerEntry covered) =>
        document.WithDigestionSources(
            document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries
                        .Select(entry => string.Equals(entry.AtomId, atomId, StringComparison.Ordinal)
                            ? covered
                            : entry)
                        .ToImmutableArray(),
                })
                .ToImmutableArray());

    private static DigestionEntryEvaluation EvaluationFor(
        DigestionLedgerEvaluation evaluation,
        string atomId) =>
        evaluation.Entries.Single(entry =>
            string.Equals(entry.Entry.AtomId, atomId, StringComparison.Ordinal));

    private static void RequireClosedDeletable(DigestionEntryEvaluation covered)
    {
        if (IsClosedDeletable(covered))
        {
            return;
        }

        throw new InvalidOperationException(
            $"cover atom {covered.Entry.AtomId} did not reach a deletable Closed state: "
            + $"{DigestionStatusNames.Migration(covered.DerivedStatus.Migration)}-"
            + $"{DigestionStatusNames.Truth(covered.DerivedStatus.Truth)} "
            + $"deletable={covered.Deletable.ToString().ToLowerInvariant()} "
            + $"gaps={string.Join(",", covered.Gaps.Select(static gap => gap.Code))}");
    }

    private static bool IsClosedDeletable(DigestionEntryEvaluation covered) =>
        covered.Deletable && covered.DerivedStatus.Truth == DigestionTruthState.Closed;

    private static void RecordCoverDisposition(
        Session session,
        DigestionLedgerEntry target,
        DigestionEntryEvaluation outcome,
        ImmutableArray<string> gids)
    {
        var disposition = new DigestionCoverDisposition(
            outcome.DerivedStatus,
            gids.Order(StringComparer.Ordinal).ToImmutableArray(),
            outcome.Gaps
                .Select(static gap => new DigestionDispositionGap(gap.Code, gap.Detail))
                .OrderBy(static gap => gap.Code, StringComparer.Ordinal)
                .ThenBy(static gap => gap.Detail, StringComparer.Ordinal)
                .ToImmutableArray());
        var dispositionDocument = ReplaceEntry(
            session.Document,
            target.AtomId,
            target with
            {
                Receipts = target.Receipts with { CoverDisposition = disposition },
            });
        var dispositionRaw = IngestCommand.ReplaceLedger(session.CurrentRaw, session.Document, dispositionDocument);
        var dispositionSnapshot = Decode(dispositionRaw);
        var finalDispositionDocument = LoadDocument(dispositionSnapshot);
        var ledgerUpdates = IngestCommand.LedgerUpdates(
            session.CurrentRaw, dispositionRaw, session.Document, finalDispositionDocument);
        session.Commit(dispositionRaw, dispositionSnapshot, finalDispositionDocument, ledgerUpdates);
    }

    private sealed record CoverArguments(
        string AtomId,
        ImmutableArray<string> Gids,
        string BaselineRevision);

    private static CoverArguments ParseArguments(IReadOnlyList<string> arguments)
    {
        string? atomId = null;
        var gids = ImmutableArray.CreateBuilder<string>();
        string? baselineRevision = null;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count)
            {
                throw Usage();
            }

            switch (arguments[index])
            {
                case "--cover-atom" when atomId is null:
                    atomId = arguments[index + 1];
                    break;
                case "--gid":
                    gids.Add(arguments[index + 1]);
                    break;
                case "--base" when baselineRevision is null:
                    baselineRevision = arguments[index + 1];
                    break;
                default:
                    throw Usage();
            }
        }

        if (string.IsNullOrWhiteSpace(atomId)
            || gids.Count == 0
            || gids.Any(string.IsNullOrWhiteSpace)
            || gids.Distinct(StringComparer.Ordinal).Count() != gids.Count
            || string.IsNullOrWhiteSpace(baselineRevision))
        {
            throw Usage();
        }

        return new CoverArguments(atomId, gids.ToImmutable(), baselineRevision);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint cover-atom --cover-atom ATOM_ID --gid DECL_GID [--gid DECL_GID ...] --base REV");

    private static BackfillInventoryDocument LoadDocument(RepositorySnapshot snapshot) =>
        IngestCommand.LoadDocument(snapshot);

    private static ValidatedPolicy LoadPolicy(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile("Meta/registry.yaml", out var registry)
            || !snapshot.TryGetFile("Meta/domains.yaml", out var domains))
        {
            throw new InvalidOperationException(
                "cover requires Meta/registry.yaml and Meta/domains.yaml");
        }

        return RegistryLoader.Load(registry.RawBytes.AsSpan(), domains.RawBytes.AsSpan()) switch
        {
            RegistryLoadOutcome.Accepted accepted => accepted.Policy,
            RegistryLoadOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };
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
