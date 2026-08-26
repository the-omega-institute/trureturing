using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static partial class DigestionStatusEvaluator
{
    internal static DigestionLedgerEvaluation EvaluateUncovered(
        DigestionEvaluationScope scope,
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument? baselineDocument = null,
        RawChangeSet? changes = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        changes = DigestionEvaluationScopes.ResolveChanges(scope, changes);
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
            casEvaluation: DigestionCasStore.Evaluate(document, snapshot, changes),
            changes: changes);
        findings.AddRange(alignment.Findings);
        var emptyLeanReport = LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));
        var emptyTruthStates = new Dictionary<RepoPath, TruthState>();
        var genreChecks = document.RequireDigestionSources()
            .ToDictionary(
                static source => source.SourceId,
                static source => source.GenreRegistryCheck,
                StringComparer.Ordinal);
        var frozenStatements = new Lazy<FrozenStatementIndex>(() => FrozenStatementIndex.Load(snapshot));
        var work = entries
            .Where(static entry => entry.CoverageGids.Length == 0)
            .Select(entry => Inspect(
                entry,
                alignment.AlignmentFor(entry.AtomId),
                alignment.AtomFor(entry.AtomId),
                baselineMigration: null,
                snapshot,
                emptyLeanReport,
                emptyTruthStates,
                verifiedScribeEmissions: null,
                frozenStatements,
                genreChecks[entry.SourceId],
                changes,
                isBaseFactAffected: null,
                projectedStatusChanges: changes,
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

    internal static DigestionLedgerEvaluation Evaluate(
        DigestionEvaluationScope scope,
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        AcceptedLeanClosure lean,
        VerifiedScribeEmissions? verifiedScribeEmissions = null,
        BackfillInventoryDocument? baselineDocument = null,
        bool validateProjectedStatus = true,
        RepositorySnapshot? baselineSnapshot = null,
        DigestionCasEvaluation? casEvaluation = null,
        RawChangeSet? changes = null,
        Func<string, bool>? isBaseFactAffected = null,
        RawChangeSet? projectedStatusChanges = null,
        IReadOnlyDictionary<RepoPath, TruthState>? truthStates = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(lean);
        changes = DigestionEvaluationScopes.ResolveChanges(scope, changes);
        var entries = document.RequireDigestionEntries();
        var findings = ImmutableArray.CreateBuilder<string>();
        if (FindDuplicateAtomId(entries) is { } duplicateAtomId)
        {
            findings.Add($"duplicate atom_id: {duplicateAtomId}");
            return new DigestionLedgerEvaluation([], findings.ToImmutable());
        }

        if (casEvaluation is not null && !casEvaluation.Matches(changes))
        {
            throw new ArgumentException(
                "CAS evaluation scope does not match the digestion evaluation scope.",
                nameof(casEvaluation));
        }

        casEvaluation ??= DigestionCasStore.Evaluate(
            document,
            snapshot,
            changes,
            isBaseFactAffected);
        var alignment = DigestionLedgerAligner.Evaluate(
            document,
            snapshot,
            baselineDocument,
            DigestionAlignmentMode.Admission,
            baselineSnapshot: baselineSnapshot,
            casEvaluation: casEvaluation,
            changes: changes);
        findings.AddRange(alignment.Findings);
        var baselineEntries = (baselineDocument?.RequireDigestionEntries()
                ?? ImmutableArray<DigestionLedgerEntry>.Empty)
            .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .Where(static group => group.Count() == 1)
            .ToDictionary(static group => group.Key, static group => group.Single(), StringComparer.Ordinal);

        var states = truthStates ?? LeanTruthStates.Resolve(snapshot, lean);
        var genreChecks = document.RequireDigestionSources()
            .ToDictionary(
                static source => source.SourceId,
                static source => source.GenreRegistryCheck,
                StringComparer.Ordinal);
        var frozenStatements = new Lazy<FrozenStatementIndex>(() => FrozenStatementIndex.Load(snapshot));
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
                states,
                verifiedScribeEmissions,
                frozenStatements,
                genreChecks[entry.SourceId],
                changes,
                isBaseFactAffected,
                projectedStatusChanges ?? changes,
                findings);
        }).ToArray();
        DeriveMigration(work);
        PropagateStatusAuthorityChanges(work);
        RequireDecompositionBeforeNewAbsorption(
            work,
            baselineEntries,
            alignment.VerifiedClausePlanParents,
            findings);

        var observations = alignment.Residual
            .Select(static item =>
                $"source {item.SourceId} has unregistered residual-open atom "
                + $"{item.Atom.AstPath} ({item.SuggestedAtomId}); run make ingest to close it")
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        return CompleteEvaluation(
            work,
            snapshot,
            findings,
            validateProjectedStatus,
            changes,
            observations);
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
        bool validateProjectedStatus,
        RawChangeSet? changes,
        // 非阻断的观察项(「已入库、尚未消化」)。两条评估路径共用本方法,
        // 只有 admission 路径会传入;projection 路径不产观察项。
        ImmutableArray<string> observations = default)
    {
        var evaluations = ImmutableArray.CreateBuilder<DigestionEntryEvaluation>(work.Count);
        foreach (var item in work)
        {
            CompleteChainGaps(item, work);
            var truth = DeriveTruth(item, snapshot, changes);
            var status = new DigestionStatus(item.Migration, truth);
            if (validateProjectedStatus
                && item.StatusAuthorityChanged
                && status != item.Entry.ProjectedStatus)
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
            findings.Order(StringComparer.Ordinal).ToImmutableArray(),
            observations.IsDefault ? [] : observations);
    }

    private static EntryWork Inspect(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        DigestionAtom? atom,
        DigestionMigrationState? baselineMigration,
        RepositorySnapshot snapshot,
        LeanAxiomReport leanReport,
        IReadOnlyDictionary<RepoPath, TruthState> states,
        VerifiedScribeEmissions? verifiedScribeEmissions,
        Lazy<FrozenStatementIndex> frozenStatements,
        GenreRegistryCheck genreRegistryCheck,
        RawChangeSet? changes,
        Func<string, bool>? isBaseFactAffected,
        RawChangeSet? projectedStatusChanges,
        ImmutableArray<string>.Builder findings)
    {
        var gaps = new List<DigestionGap>();
        // Boundary and Scribe retain their existing baseline-only full check. Coverage can
        // trust a committed receipt outside a nonempty, authoritative git delta even when the
        // query omitted --base; an empty delta retains the explicit whole-tree diagnostic.
        var verificationChanges = baselineMigration is null ? null : changes;
        var canReuseCoverageWithoutBaseline = changes is not null
            && changes.Paths.Any()
            && !DigestionCasStore.EntryChanged(entry, changes);
        var coverageVerificationChanges = baselineMigration is null
            && canReuseCoverageWithoutBaseline
                ? changes
                : verificationChanges;
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
                gaps.Add(new DigestionGap(
                    "target-gid-missing",
                    gidText,
                    DigestionGapSeverity.NonFatal));
                continue;
            }

            if (!DeclarationExists(gid, leanReport, gaps))
            {
                continue;
            }

            existingTargets.Add(gidText, target);
            targetStates.Add((
                gidText,
                states.TryGetValue(target.Path, out var state) ? state : TruthState.Semantic));
        }

        if (entry.CoverageGids.Length == 0)
        {
            gaps.Add(new DigestionGap(
                "coverage-gid-missing",
                entry.AtomId,
                DigestionGapSeverity.NonFatal));
        }

        var coverage = VerifyCoverageReceipts(
            entry,
            existingTargets,
            frozenStatements,
            coverageVerificationChanges,
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
                gaps.Add(new DigestionGap(
                    "unresolved-subitem",
                    subitem,
                    DigestionGapSeverity.NonFatal));
            }
        }

        foreach (var token in genreRegistryCheck.UnregisteredGenres.Where(token =>
                     UnregisteredGenreLocator.MatchesToken(entry.AstPath, token)))
        {
            gaps.Add(new DigestionGap(
                "unregistered-genre",
                token,
                DigestionGapSeverity.NonFatal));
        }

        // Partial is an aggregate baseline verdict: at least one local predicate failed,
        // but the ledger does not record which one. Skipped predicates therefore cannot be
        // combined into a new success. Touching the entry replays every predicate and earns
        // a fresh verdict; otherwise the baseline keeps this entry locally incomplete.
        var baselineKeepsLocalIncomplete = baselineMigration == DigestionMigrationState.Partial
            && changes is not null
            && !DigestionCasStore.EntryChanged(entry, changes)
            && isBaseFactAffected?.Invoke(entry.SourcePath) != true;
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
        return new EntryWork(
            entry,
            alignment,
            atom,
            gaps,
            targetStates,
            localComplete,
            hasProgress,
            StatusAuthorityClosureChanged(
                entry,
                baselineMigration,
                projectedStatusChanges,
                isBaseFactAffected));
    }

    private static bool StatusAuthorityClosureChanged(
        DigestionLedgerEntry entry,
        DigestionMigrationState? baselineMigration,
        RawChangeSet? changes,
        Func<string, bool>? isBaseFactAffected)
    {
        if (changes is null || DigestionCasStore.EntryChanged(entry, changes))
        {
            return true;
        }

        // A changed-set caller without a baseline (theory-candidates) still has an explicit
        // scope. Without a base-fact resolver, a missing historical migration marker alone does
        // not make every entry affected. Production callers provide the resolver and continue
        // through the full authority-closure check below.
        if (baselineMigration is null && isBaseFactAffected is null)
        {
            return false;
        }

        bool Affected(string path) => isBaseFactAffected?.Invoke(path) ?? PathChanged(changes, path);

        if (changes.Paths.Any(path =>
                FrozenLedgerChangeClassifier.IsAcceptedEventPath(path.Value))
            || Affected(entry.SourcePath)
            || Affected(TheoryAtomizerDataLoader.DataPath)
            || DigestionFingerprint.IsCanonicalSha256(entry.CasRef)
                && Affected(DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..])
            || entry.Receipts.TailAuthorization is { } tail && Affected(tail.Path))
        {
            return true;
        }

        foreach (var gidText in entry.CoverageGids)
        {
            if (!Gid.TryParse(gidText, out var gid))
            {
                continue;
            }

            var documentGid = ScribeEmissionAttestation.DocumentGid(gidText);
            if (Affected(gid.Path.Value)
                || Affected(ScribeEmissionAttestation.DefinitionPath(documentGid))
                || Affected(ScribeEmissionAttestation.EmissionPath(documentGid)))
            {
                return true;
            }
        }

        return false;
    }

    private static void PropagateStatusAuthorityChanges(IReadOnlyList<EntryWork> work)
    {
        var byId = work.ToDictionary(static item => item.Entry.AtomId, StringComparer.Ordinal);
        var changed = true;
        while (changed)
        {
            changed = false;
            foreach (var item in work.Where(static item => !item.StatusAuthorityChanged))
            {
                if (item.Entry.Receipts.ChainAtoms.Any(atomId =>
                        byId.TryGetValue(atomId, out var dependency)
                        && dependency.StatusAuthorityChanged))
                {
                    item.StatusAuthorityChanged = true;
                    changed = true;
                }
            }
        }
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
            gaps.Add(new DigestionGap(
                "target-declaration-missing",
                gid.Value,
                DigestionGapSeverity.NonFatal));
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
            gid.Value,
            DigestionGapSeverity.NonFatal));
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
                item.Gaps.Add(new DigestionGap(
                    "chain-migration-incomplete",
                    atomId,
                    DigestionGapSeverity.NonFatal));
            }
        }
    }

    private static DigestionTruthState DeriveTruth(
        EntryWork item,
        RepositorySnapshot snapshot,
        RawChangeSet? changes)
    {
        if (item.TargetStates.Count == 0
            || item.TargetStates.Any(static target => target.State is TruthState.Open or TruthState.Semantic))
        {
            foreach (var target in item.TargetStates.Where(static target =>
                         target.State is TruthState.Open or TruthState.Semantic))
            {
                item.Gaps.Add(new DigestionGap(
                    "lean-state-open",
                    $"{target.Gid}:{target.State}",
                    DigestionGapSeverity.NonFatal));
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
                    string.Join(',', tailGids),
                    DigestionGapSeverity.NonFatal));
                return DigestionTruthState.Open;
            }

            var validateStoredArtifact = changes is not null
                && (DigestionCasStore.EntryChanged(item.Entry, changes)
                    || changes.Paths.Any(path => path.Value == item.Entry.Receipts.TailAuthorization.Path));
            if (!TailAuthorizationArtifact.Verify(
                    item.Entry,
                    tailGids,
                    snapshot,
                    validateStoredArtifact))
            {
                item.Gaps.Add(new DigestionGap(
                    "tail-authorization-invalid",
                    string.Join(',', tailGids),
                    DigestionGapSeverity.NonFatal));
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
        bool hasProgress,
        bool statusAuthorityChanged)
    {
        internal DigestionLedgerEntry Entry { get; } = entry;

        internal DigestionReceiptAlignment Alignment { get; } = alignment;

        internal DigestionAtom? Atom { get; } = atom;

        internal List<DigestionGap> Gaps { get; } = gaps;

        internal List<(string Gid, TruthState State)> TargetStates { get; } = targetStates;

        internal bool LocalComplete { get; } = localComplete;

        internal bool HasProgress { get; } = hasProgress;

        internal bool StatusAuthorityChanged { get; set; } = statusAuthorityChanged;

        internal DigestionMigrationState Migration { get; set; }
    }
}
