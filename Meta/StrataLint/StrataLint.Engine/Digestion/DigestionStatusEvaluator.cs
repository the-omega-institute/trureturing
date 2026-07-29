using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record DigestionGap(string Code, string Detail);

internal sealed record DigestionEntryEvaluation(
    DigestionLedgerEntry Entry,
    DigestionReceiptAlignment Alignment,
    DigestionStatus DerivedStatus,
    bool Deletable,
    ImmutableArray<DigestionGap> Gaps)
{
    internal string Render() =>
        $"{Entry.SourceId}/{Entry.AtomId} "
        + $"alignment={DigestionReceiptAlignmentNames.Render(Alignment)} "
        + $"{DigestionStatusNames.Migration(DerivedStatus.Migration)}-"
        + $"{DigestionStatusNames.Truth(DerivedStatus.Truth)} "
        + $"deletable={Deletable.ToString().ToLowerInvariant()} "
        + $"gaps={string.Join(',', Gaps.Select(static gap => gap.Code))}";
}

internal sealed record DigestionLedgerEvaluation(
    ImmutableArray<DigestionEntryEvaluation> Entries,
    ImmutableArray<string> Findings)
{
    internal int DeletableCount => Entries.Count(static entry => entry.Deletable);
}

internal static class DigestionStatusNames
{
    internal static string Migration(DigestionMigrationState value) => value switch
    {
        DigestionMigrationState.Residual => "residual",
        DigestionMigrationState.Partial => "partial",
        DigestionMigrationState.Absorbed => "absorbed",
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };

    internal static string Truth(DigestionTruthState value) => value switch
    {
        DigestionTruthState.Closed => "closed",
        DigestionTruthState.Tail => "tail",
        DigestionTruthState.Open => "open",
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };
}

internal static class DigestionStatusEvaluator
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
            DigestionAlignmentMode.Admission);
        findings.AddRange(alignment.Findings);
        var emptyLeanReport = LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));
        var emptyTruthNodes = new Dictionary<RepoPath, TruthNode>();
        var work = entries
            .Where(static entry => entry.CoverageGids.Length == 0)
            .Select(entry => Inspect(
                entry,
                alignment.AlignmentFor(entry.AtomId),
                snapshot,
                emptyLeanReport,
                emptyTruthNodes,
                ScribeEmissionAttestation.Empty,
                verifiedScribeEmissions: null,
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
        bool validateProjectedStatus = true)
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
            DigestionAlignmentMode.Admission);
        findings.AddRange(alignment.Findings);

        var dag = AcyclicTruthDag.Build(snapshot, lean) switch
        {
            DagBuildOutcome.Accepted accepted => accepted.Capability,
            DagBuildOutcome.Rejected rejected => throw new FormatException(
                "truth DAG is cyclic: " + string.Join(" -> ", rejected.Witness.Select(static path => path.Value))),
        };
        var nodes = dag.Nodes.ToDictionary(static node => node.RepoPath);
        var scribeAttestation = ScribeEmissionAttestation.Load(snapshot, findings);
        var work = entries.Select(entry =>
            Inspect(
                entry,
                alignment.AlignmentFor(entry.AtomId),
                snapshot,
                lean.Report,
                nodes,
                scribeAttestation,
                verifiedScribeEmissions,
                findings)).ToArray();
        DeriveMigration(work);

        return CompleteEvaluation(work, snapshot, findings, validateProjectedStatus);
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
        RepositorySnapshot snapshot,
        LeanAxiomReport leanReport,
        IReadOnlyDictionary<RepoPath, TruthNode> nodes,
        ScribeEmissionAttestation scribeAttestation,
        VerifiedScribeEmissions? verifiedScribeEmissions,
        ImmutableArray<string>.Builder findings)
    {
        var inspection = DigestionReceiptInspector.Inspect(
            entry,
            alignment,
            snapshot,
            leanReport,
            nodes,
            scribeAttestation,
            verifiedScribeEmissions,
            findings);
        return new EntryWork(
            entry,
            alignment,
            inspection.Gaps.ToList(),
            inspection.TargetStates.ToList(),
            inspection.LocalComplete,
            inspection.HasProgress);
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

    private sealed class EntryWork(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        List<DigestionGap> gaps,
        List<(string Gid, TruthState State)> targetStates,
        bool localComplete,
        bool hasProgress)
    {
        internal DigestionLedgerEntry Entry { get; } = entry;

        internal DigestionReceiptAlignment Alignment { get; } = alignment;

        internal List<DigestionGap> Gaps { get; } = gaps;

        internal List<(string Gid, TruthState State)> TargetStates { get; } = targetStates;

        internal bool LocalComplete { get; } = localComplete;

        internal bool HasProgress { get; } = hasProgress;

        internal DigestionMigrationState Migration { get; set; }
    }
}
