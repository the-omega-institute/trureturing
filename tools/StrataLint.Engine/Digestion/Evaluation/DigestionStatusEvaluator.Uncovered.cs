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
        RawChangeSet? casChanges = null,
        ImmutableHashSet<string>? sourceIds = null,
        Func<string, TheoryAtomizer>? atomizerResolver = null,
        Func<string, TheoryAtomizerWithContentKinds>? contentKindAtomizerResolver = null)
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
            atomizerResolver,
            casEvaluation: DigestionCasStore.Evaluate(document, snapshot, casChanges),
            changes: changes,
            casChanges: casChanges,
            contentKindAtomizerResolver: contentKindAtomizerResolver,
            sourceIds: sourceIds);
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
            entries.Where(entry => sourceIds is null || sourceIds.Contains(entry.SourceId)),
            baselineAtomIds: ImmutableHashSet<string>.Empty,
            changes,
            alignment,
            isBaseFactAffected: null);
        var work = entries
            .Where(entry => sourceIds is null || sourceIds.Contains(entry.SourceId))
            .Where(static entry => entry.CoverageGids.Length == 0)
            .Select(entry => Inspect(
                entry,
                alignment.AlignmentFor(entry.AtomId),
                alignment.AtomFor(entry.AtomId),
                baselineMigration: null,
                baselineEntryPresent: false,
                snapshot,
                emptyLeanReport,
                emptyTruthStates,
                verifiedScribeEmissions: null,
                frozenStatements,
                genreChecks[entry.SourceId],
                changes,
                statusAuthorityChangedAtomIds.Contains(entry.AtomId),
                findings))
            .ToArray();
        DeriveMigration(work);
        return CompleteEvaluation(
            work,
            snapshot,
            findings,
            validateProjectedStatus: true,
            changes);
    }
}
