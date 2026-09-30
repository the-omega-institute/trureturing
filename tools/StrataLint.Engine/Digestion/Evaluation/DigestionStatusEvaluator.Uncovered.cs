using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class DigestionStatusEvaluator
{
    internal static DigestionLedgerEvaluation EvaluateUncovered(
        DigestionEvaluationScope scope,
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument? baselineDocument = null,
        RawChangeSet? changes = null,
        RawChangeSet? casChanges = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        changes = DigestionEvaluationScopes.ResolveChanges(scope, changes);
        casChanges ??= changes;
        var entries = document.RequireDigestionEntries();
        var findings = ImmutableArray.CreateBuilder<string>();
        if (FindDuplicateAtomId(entries) is { } duplicateAtomId)
        {
            findings.Add($"duplicate atom_id: {duplicateAtomId}");
            return new DigestionLedgerEvaluation([], findings.ToImmutable());
        }

        var alignment = DigestionLedgerAligner.Evaluate(
            document,
            snapshot,
            baselineDocument,
            DigestionAlignmentMode.Projection,
            casEvaluation: DigestionCasStore.Evaluate(document, snapshot, casChanges),
            changes: changes,
            casChanges: casChanges);
        findings.AddRange(alignment.Findings);
        var emptyLeanReport = LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));
        var emptyTruthStates = new Dictionary<RepoPath, TruthState>();
        var genreChecks = document.RequireDigestionSources()
            .ToDictionary(
                static source => source.SourceId,
                static source => source.GenreRegistryCheck,
                StringComparer.Ordinal);
        var frozenStatements = new Lazy<FrozenStatementIndex>(() => FrozenStatementIndex.Create(
            FrozenStateCatalog.Load(snapshot),
            emptyLeanReport));
        var statusAuthorityChangedAtomIds = ResolveStatusAuthorityChangedAtomIds(
            entries,
            baselineAtomIds: ImmutableHashSet<string>.Empty,
            changes,
            alignment,
            isBaseFactAffected: null);
        var work = entries
            .Select(entry => entry.CoverageGids.Length > 0
                ? CoveredMigrationContext(entry, alignment.AlignmentFor(entry.AtomId), alignment.AtomFor(entry.AtomId), findings)
                : Inspect(
                entry,
                alignment.AlignmentFor(entry.AtomId),
                alignment.AtomFor(entry.AtomId),
                baselineMigration: null,
                baselineEntryPresent: false,
                snapshot,
                emptyLeanReport,
                emptyTruthStates,
                frozenStatements,
                genreChecks[entry.SourceId],
                changes,
                statusAuthorityChangedAtomIds.Contains(entry.AtomId),
                findings))
            .ToArray();
        DeriveMigration(work);
        var evaluation = CompleteEvaluation(
            work,
            snapshot,
            findings,
            validateProjectedStatus: true,
            changes);
        return evaluation with
        {
            Entries = evaluation.Entries.Where(static item => item.Entry.CoverageGids.Length == 0).ToImmutableArray(),
        };
    }

    // The report-free selection query carries recorded covered migration as dependency
    // context, never as fresh Lean truth. Recheck structure and nested chain closure, but
    // exclude these entries from the returned evaluation. Admission still uses Evaluate
    // with a validated current report to resolve every coverage edge and truth state.
    private static EntryWork CoveredMigrationContext(DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment, DigestionAtom? atom, ImmutableArray<string>.Builder findings)
    {
        var gaps = new List<DigestionGap>();
        var structured = VerifyStructuredAlignment(entry, alignment, gaps, findings);
        return new EntryWork(entry, alignment, atom, gaps, [],
            localComplete: structured && entry.ProjectedStatus.Migration == DigestionMigrationState.Absorbed
                && entry.Coverage.All(static edge => edge.TargetStatementId is not null)
                && entry.Receipts.UnresolvedSubitems.IsEmpty
                && entry.Receipts.Quarantine is null && entry.Receipts.CoverDisposition is null,
            hasProgress: true, hasUnresolvedCoverageTarget: true, statusAuthorityChanged: false);
    }
}
