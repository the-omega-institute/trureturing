using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static partial class DigestionStatusEvaluator
{
    internal static DigestionLedgerEvaluation EvaluateUncovered(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument? baselineDocument = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
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
            DigestionAlignmentMode.Projection);
        findings.AddRange(alignment.Findings);
        var emptyLeanReport = LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));
        var emptyTruthNodes = new Dictionary<RepoPath, TruthNode>();
        var genreChecks = document.RequireDigestionSources()
            .ToDictionary(
                static source => source.SourceId,
                static source => source.GenreRegistryCheck,
                StringComparer.Ordinal);
        var work = entries
            .Where(static entry => entry.CoverageGids.Length == 0)
            .Select(entry => Inspect(
                entry,
                alignment.AlignmentFor(entry.AtomId),
                alignment.AtomFor(entry.AtomId),
                baselineMigration: null,
                snapshot,
                emptyLeanReport,
                emptyTruthNodes,
                verifiedScribeEmissions: null,
                genreChecks[entry.SourceId],
                changes: null,
                findings))
            .ToArray();
        DeriveMigration(work);
        return CompleteEvaluation(work, snapshot, findings, validateProjectedStatus: true);
    }

    internal static DigestionLedgerEvaluation Evaluate(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        VerifiedScribeEmissions? verifiedScribeEmissions = null,
        BackfillInventoryDocument? baselineDocument = null,
        bool validateProjectedStatus = true,
        RepositorySnapshot? baselineSnapshot = null,
        DigestionCasEvaluation? casEvaluation = null,
        RawChangeSet? changes = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
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
            DigestionAlignmentMode.Admission,
            baselineSnapshot: baselineSnapshot,
            casEvaluation: casEvaluation);
        findings.AddRange(alignment.Findings);
        var baselineEntries = (baselineDocument?.RequireDigestionEntries()
                ?? ImmutableArray<DigestionLedgerEntry>.Empty)
            .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .Where(static group => group.Count() == 1)
            .ToDictionary(static group => group.Key, static group => group.Single(), StringComparer.Ordinal);

        var dag = AcyclicTruthDag.Build(snapshot, lean) switch
        {
            DagBuildOutcome.Accepted accepted => accepted.Capability,
            DagBuildOutcome.Rejected rejected => throw new FormatException(
                "truth DAG is cyclic: " + string.Join(" -> ", rejected.Witness.Select(static path => path.Value))),
        };
        var nodes = dag.Nodes.ToDictionary(static node => node.RepoPath);
        var genreChecks = document.RequireDigestionSources()
            .ToDictionary(
                static source => source.SourceId,
                static source => source.GenreRegistryCheck,
                StringComparer.Ordinal);
        var work = entries.Select(entry =>
        {
            var baselineMigration = baselineEntries.TryGetValue(entry.AtomId, out var baselineEntry)
                ? baselineEntry.ProjectedStatus.Migration
                : (DigestionMigrationState?)null;
            return Inspect(
                entry,
                alignment.AlignmentFor(entry.AtomId),
                alignment.AtomFor(entry.AtomId),
                baselineMigration,
                snapshot,
                lean.Report,
                nodes,
                verifiedScribeEmissions,
                genreChecks[entry.SourceId],
                changes,
                findings);
        }).ToArray();
        DeriveMigration(work);
        RequireDecompositionBeforeNewAbsorption(
            work,
            baselineEntries,
            alignment.VerifiedClausePlanParents,
            findings);

        return CompleteEvaluation(work, snapshot, findings, validateProjectedStatus);
    }

    private static void RequireDecompositionBeforeNewAbsorption(
        IEnumerable<EntryWork> work,
        IReadOnlyDictionary<string, DigestionLedgerEntry> baselineEntries,
        IReadOnlySet<string> verifiedClausePlanParents,
        ImmutableArray<string>.Builder findings)
    {
        foreach (var item in work.Where(static item => item.Atom is not null))
        {
            var baselineMigration = baselineEntries.TryGetValue(item.Entry.AtomId, out var baseline)
                ? baseline.ProjectedStatus.Migration
                : (DigestionMigrationState?)null;
            if (!DigestionDecompositionPolicy.RejectsNewAbsorption(
                    item.Atom!,
                    item.Migration,
                    item.Entry.Receipts.UnresolvedSubitems.Length,
                    verifiedClausePlanParents.Contains(item.Entry.AtomId),
                    baselineMigration))
            {
                continue;
            }

            findings.Add(
                $"entry {item.Entry.AtomId} has multiple clauses but newly claims absorbed "
                + "with unresolved_subitems=[]; decompose the uncovered clauses before absorption");
        }
    }

    private static string? FindDuplicateAtomId(IEnumerable<DigestionLedgerEntry> entries) =>
        entries
            .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .FirstOrDefault(static group => group.Count() > 1)
            ?.Key;

    private static DigestionLedgerEvaluation CompleteEvaluation(
        IReadOnlyList<EntryWork> work,
        RepositorySnapshot snapshot,
        ImmutableArray<string>.Builder findings,
        bool validateProjectedStatus)
    {
        var evaluations = ImmutableArray.CreateBuilder<DigestionEntryEvaluation>(work.Count);
        foreach (var item in work)
        {
            CompleteChainGaps(item, work);
            var truth = DeriveTruth(item, snapshot);
            var status = new DigestionStatus(item.Migration, truth);
            if (validateProjectedStatus && status != item.Entry.ProjectedStatus)
            {
                findings.Add(
                    $"entry {item.Entry.AtomId} handwritten status "
                    + $"{DigestionStatusNames.Migration(item.Entry.ProjectedStatus.Migration)}-"
                    + $"{DigestionStatusNames.Truth(item.Entry.ProjectedStatus.Truth)} differs from derived "
                    + $"{DigestionStatusNames.Migration(status.Migration)}-"
                    + DigestionStatusNames.Truth(status.Truth));
            }

            var gaps = item.Gaps
                .OrderBy(static gap => gap.Code, StringComparer.Ordinal)
                .ThenBy(static gap => gap.Detail, StringComparer.Ordinal)
                .ToImmutableArray();
            evaluations.Add(new DigestionEntryEvaluation(
                item.Entry,
                item.Alignment,
                item.Atom,
                status,
                item.Migration == DigestionMigrationState.Absorbed
                    && truth is DigestionTruthState.Closed or DigestionTruthState.Tail
                    && gaps.Length == 0,
                gaps));
        }

        return new DigestionLedgerEvaluation(
            evaluations.MoveToImmutable(),
            findings.Order(StringComparer.Ordinal).ToImmutableArray());
    }

    private static EntryWork Inspect(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        DigestionAtom? atom,
        DigestionMigrationState? baselineMigration,
        RepositorySnapshot snapshot,
        LeanAxiomReport leanReport,
        IReadOnlyDictionary<RepoPath, TruthNode> nodes,
        VerifiedScribeEmissions? verifiedScribeEmissions,
        GenreRegistryCheck genreRegistryCheck,
        RawChangeSet? changes,
        ImmutableArray<string>.Builder findings)
    {
        var gaps = new List<DigestionGap>();
        // A new entry has no baseline verdict to reuse, so it must be checked in full even
        // if a malformed change set omits its ledger path.
        var verificationChanges = baselineMigration is null ? null : changes;
        var boundary = entry.Atomizer == AtomizerRegistry.NoAtomizerId
            && entry.Boundary is not null
                ? VerifyBoundary(entry, snapshot, verificationChanges, gaps, findings)
                : VerifyStructuredAlignment(entry, alignment, gaps, findings);
        var targetStates = new List<(string Gid, TruthState State)>();
        var existingTargets = new Dictionary<string, RepositoryFile>(StringComparer.Ordinal);
        foreach (var gidText in entry.CoverageGids.Distinct(StringComparer.Ordinal))
        {
            if (!Gid.TryParse(gidText, out var gid)
                || !snapshot.TryGetFile(gid.Path.Value, out var target))
            {
                gaps.Add(new DigestionGap("target-gid-missing", gidText));
                continue;
            }

            if (!DeclarationExists(gid, leanReport, gaps))
            {
                continue;
            }

            existingTargets.Add(gidText, target);
            targetStates.Add((
                gidText,
                nodes.TryGetValue(target.Path, out var node) ? node.State : TruthState.Semantic));
        }

        if (entry.CoverageGids.Length == 0)
        {
            gaps.Add(new DigestionGap("coverage-gid-missing", entry.AtomId));
        }

        var coverage = VerifyCoverageReceipts(
            entry,
            existingTargets,
            verificationChanges,
            gaps,
            findings);
        var scribe = VerifyScribeReceipts(
            entry,
            snapshot,
            verifiedScribeEmissions,
            verificationChanges,
            gaps,
            findings);
        if (entry.Receipts.UnresolvedSubitems.Length > 0)
        {
            foreach (var subitem in entry.Receipts.UnresolvedSubitems)
            {
                gaps.Add(new DigestionGap("unresolved-subitem", subitem));
            }
        }

        foreach (var token in genreRegistryCheck.UnregisteredGenres.Where(token =>
                     UnregisteredGenreLocator.MatchesToken(entry.AstPath, token)))
        {
            gaps.Add(new DigestionGap("unregistered-genre", token));
        }

        // Partial is an aggregate baseline verdict: at least one local predicate failed,
        // but the ledger does not record which one. Skipped predicates therefore cannot be
        // combined into a new success. Touching the entry replays every predicate and earns
        // a fresh verdict; otherwise the baseline keeps this entry locally incomplete.
        var baselineKeepsLocalIncomplete = baselineMigration == DigestionMigrationState.Partial
            && changes is not null
            && !DigestionCasStore.EntryChanged(entry, changes);
        var localComplete = !baselineKeepsLocalIncomplete
            && boundary
            && existingTargets.Count == entry.CoverageGids.Distinct(StringComparer.Ordinal).Count()
            && entry.CoverageGids.Length > 0
            && coverage
            && scribe
            && entry.Receipts.UnresolvedSubitems.Length == 0;
        var hasProgress = existingTargets.Count > 0
            || entry.Receipts.Coverage.Length > 0
            || entry.Receipts.Scribe.Length > 0;
        return new EntryWork(entry, alignment, atom, gaps, targetStates, localComplete, hasProgress);
    }

    private static bool DeclarationExists(
        Gid gid,
        LeanAxiomReport leanReport,
        ICollection<DigestionGap> gaps)
    {
        if (gid.ToTarget() is not Target.Formal { Declaration: { } declaration } formal)
        {
            return true;
        }

        if (!leanReport.Files.TryGetValue(formal.Path, out var module)
            || !string.IsNullOrEmpty(module.Error))
        {
            gaps.Add(new DigestionGap("target-declaration-missing", gid.Value));
            return false;
        }

        var suffix = "." + declaration;
        var matches = module.Declarations.Count(candidate =>
            string.Equals(candidate.Name, declaration, StringComparison.Ordinal)
            || candidate.Name.EndsWith(suffix, StringComparison.Ordinal));
        if (matches == 1)
        {
            return true;
        }

        gaps.Add(new DigestionGap(
            matches == 0 ? "target-declaration-missing" : "target-declaration-ambiguous",
            gid.Value));
        return false;
    }

    private static Dictionary<string, T> UniqueByGid<T>(
        string label,
        IEnumerable<T> values,
        Func<T, string> gid,
        ImmutableArray<string>.Builder findings)
    {
        var result = new Dictionary<string, T>(StringComparer.Ordinal);
        foreach (var value in values)
        {
            var key = gid(value);
            if (!result.TryAdd(key, value))
            {
                findings.Add($"entry {label} has duplicate receipt for {key}");
            }
        }

        return result;
    }

    private static void DeriveMigration(IReadOnlyList<EntryWork> work)
    {
        foreach (var item in work)
        {
            item.Migration = item.LocalComplete && item.Entry.Receipts.ChainAtoms.Length == 0
                ? DigestionMigrationState.Absorbed
                : item.HasProgress
                    ? DigestionMigrationState.Partial
                    : DigestionMigrationState.Residual;
        }

        var byId = work.ToDictionary(static item => item.Entry.AtomId, StringComparer.Ordinal);
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var item in work.Where(static item =>
                         item.Migration != DigestionMigrationState.Absorbed && item.LocalComplete))
            {
                if (item.Entry.Receipts.ChainAtoms.All(atomId =>
                        byId.TryGetValue(atomId, out var dependency)
                        && dependency.Migration == DigestionMigrationState.Absorbed))
                {
                    item.Migration = DigestionMigrationState.Absorbed;
                    changed = true;
                }
            }
        }
    }

    private static void CompleteChainGaps(EntryWork item, IReadOnlyList<EntryWork> work)
    {
        var byId = work.ToDictionary(static candidate => candidate.Entry.AtomId, StringComparer.Ordinal);
        foreach (var atomId in item.Entry.Receipts.ChainAtoms)
        {
            if (!byId.TryGetValue(atomId, out var dependency)
                || dependency.Migration != DigestionMigrationState.Absorbed)
            {
                item.Gaps.Add(new DigestionGap("chain-migration-incomplete", atomId));
            }
        }
    }

    private static DigestionTruthState DeriveTruth(EntryWork item, RepositorySnapshot snapshot)
    {
        if (item.TargetStates.Count == 0
            || item.TargetStates.Any(static target => target.State is TruthState.Open or TruthState.Semantic))
        {
            foreach (var target in item.TargetStates.Where(static target =>
                         target.State is TruthState.Open or TruthState.Semantic))
            {
                item.Gaps.Add(new DigestionGap("lean-state-open", $"{target.Gid}:{target.State}"));
            }

            return DigestionTruthState.Open;
        }

        if (item.TargetStates.Any(static target => target.State == TruthState.Tail))
        {
            var tailGids = item.TargetStates
                .Where(static target => target.State == TruthState.Tail)
                .Select(static target => target.Gid)
                .ToArray();
            if (item.Migration != DigestionMigrationState.Absorbed
                || item.Entry.Receipts.TailAuthorization is null)
            {
                item.Gaps.Add(new DigestionGap(
                    "tail-authorization-missing",
                    string.Join(',', tailGids)));
                return DigestionTruthState.Open;
            }

            if (!TailAuthorizationArtifact.Verify(item.Entry, tailGids, snapshot))
            {
                item.Gaps.Add(new DigestionGap(
                    "tail-authorization-invalid",
                    string.Join(',', tailGids)));
                return DigestionTruthState.Open;
            }

            return DigestionTruthState.Tail;
        }

        return DigestionTruthState.Closed;
    }

    private static string EntryLabel(this DigestionLedgerEntry entry) => entry.AtomId;

    private sealed class EntryWork(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        DigestionAtom? atom,
        List<DigestionGap> gaps,
        List<(string Gid, TruthState State)> targetStates,
        bool localComplete,
        bool hasProgress)
    {
        internal DigestionLedgerEntry Entry { get; } = entry;

        internal DigestionReceiptAlignment Alignment { get; } = alignment;

        internal DigestionAtom? Atom { get; } = atom;

        internal List<DigestionGap> Gaps { get; } = gaps;

        internal List<(string Gid, TruthState State)> TargetStates { get; } = targetStates;

        internal bool LocalComplete { get; } = localComplete;

        internal bool HasProgress { get; } = hasProgress;

        internal DigestionMigrationState Migration { get; set; }
    }
}
