using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    private const string DuplicateProbeGid = "D5/S0/Carrier/Probe";
    private const string DuplicateProbePath = "D5/S0/Carrier/Probe.lean";

    [Fact]
    public void BaselineInheritedDuplicateAtomIsObservedNotJudged()
    {
        var duplicated = CompleteWitnessAtom();
        var other = CompleteWitnessAtom("second atom receipt\n");
        var duplicatedId = AtomId(duplicated);
        var otherId = AtomId(other);
        var document = DuplicateLedger(
            DuplicateEntry(duplicated, DigestionMigrationState.Partial),
            DuplicateEntry(duplicated, DigestionMigrationState.Absorbed),
            DuplicateEntry(other, DigestionMigrationState.Partial));

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            DuplicateSnapshot(duplicated, other),
            AcceptedLean(DuplicateProbePath),
            baselineDocument: document,
            baselineSnapshot: DuplicateSnapshot(duplicated, other),
            changes: RawChangeSet.Create(["notes/unrelated.txt"]));

        Assert.Empty(evaluation.Findings);
        Assert.Contains(
            $"duplicate atom_id inherited from baseline (not judged): {duplicatedId}",
            evaluation.Observations);
        Assert.Equal([otherId], evaluation.Entries.Select(static entry => entry.Entry.AtomId));
    }

    [Fact]
    public void InheritedDuplicateParentChainingToInheritedDuplicateChildIsNotJudged()
    {
        var child = CompleteWitnessAtom();
        var parent = CompleteWitnessAtom("parent clause receipt\n");
        var other = CompleteWitnessAtom("second atom receipt\n");
        var childId = AtomId(child);
        var parentId = AtomId(parent);
        var otherId = AtomId(other);
        var document = DuplicateLedger(
            DuplicateEntry(child, DigestionMigrationState.Partial),
            DuplicateEntry(child, DigestionMigrationState.Absorbed),
            WithChain(DuplicateEntry(parent, DigestionMigrationState.Partial), childId),
            WithChain(DuplicateEntry(parent, DigestionMigrationState.Absorbed), childId),
            // Fully covered and chain-free, so the full scan derives absorbed for it.
            DuplicateEntry(other, DigestionMigrationState.Absorbed));

        // Pins the entry and observation contract only: the unregistered fixture atomizer never
        // reaches the aligner's clause-chain check. That path is pinned on a PZG fixture in
        // DigestionAlignmentTests.AdmissionDoesNotJudgeClauseChainOfBaselineInheritedDuplicates.
        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            DuplicateSnapshot(child, parent, other),
            AcceptedLean(DuplicateProbePath),
            baselineDocument: document,
            baselineSnapshot: DuplicateSnapshot(child, parent, other),
            changes: RawChangeSet.Create(["docs/source.md"]));

        Assert.True(evaluation.Findings.IsEmpty, string.Join(" | ", evaluation.Findings));
        Assert.Equal([otherId], evaluation.Entries.Select(static entry => entry.Entry.AtomId));
        Assert.Equal(
            [
                $"duplicate atom_id inherited from baseline (not judged): {childId}",
                $"duplicate atom_id inherited from baseline (not judged): {parentId}",
            ],
            evaluation.Observations.Where(static item => item.StartsWith("duplicate atom_id", StringComparison.Ordinal)).Order(StringComparer.Ordinal));
    }

    [Fact]
    public void CandidateIntroducedDuplicateAtomStillBlocks()
    {
        var duplicated = CompleteWitnessAtom();
        var other = CompleteWitnessAtom("second atom receipt\n");
        var duplicatedId = AtomId(duplicated);
        var baseline = DuplicateLedger(
            DuplicateEntry(duplicated, DigestionMigrationState.Partial),
            DuplicateEntry(other, DigestionMigrationState.Partial));
        var candidate = DuplicateLedger(
            DuplicateEntry(duplicated, DigestionMigrationState.Partial),
            DuplicateEntry(duplicated, DigestionMigrationState.Absorbed),
            DuplicateEntry(other, DigestionMigrationState.Partial));

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            candidate,
            DuplicateSnapshot(duplicated, other),
            AcceptedLean(DuplicateProbePath),
            baselineDocument: baseline,
            baselineSnapshot: DuplicateSnapshot(duplicated, other),
            changes: RawChangeSet.CreateWithKinds(
                [(EntryPath(DigestionMigrationState.Absorbed, duplicatedId), RawChangeKind.Added)]));

        Assert.Equal($"duplicate atom_id: {duplicatedId}", Assert.Single(evaluation.Findings));
        Assert.Empty(evaluation.Entries);
        Assert.Empty(evaluation.Observations);
    }

    [Fact]
    public void DuplicateAtomWithoutBaselineDocumentStillBlocks()
    {
        var duplicated = CompleteWitnessAtom();
        var duplicatedId = AtomId(duplicated);
        var candidate = DuplicateLedger(
            DuplicateEntry(duplicated, DigestionMigrationState.Partial),
            DuplicateEntry(duplicated, DigestionMigrationState.Absorbed));

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.FullScan,
            candidate,
            DuplicateSnapshot(duplicated),
            AcceptedLean(DuplicateProbePath));

        Assert.Equal($"duplicate atom_id: {duplicatedId}", Assert.Single(evaluation.Findings));
        Assert.Empty(evaluation.Entries);
    }

    private static DigestionLedgerEntry WithChain(DigestionLedgerEntry entry, string childId) =>
        entry with { Receipts = entry.Receipts with { ChainAtoms = [childId] } };

    private static string AtomId(DigestionAtom atom) =>
        atom.Fingerprints.RawSha256["sha256:".Length..];

    private static DigestionLedgerEntry DuplicateEntry(
        DigestionAtom atom,
        DigestionMigrationState migration) =>
        Assert.Single(Ledger(
            atom,
            migration,
            DigestionTruthState.Closed,
            DuplicateProbeGid,
            new DigestionCoverageEdge(DuplicateProbeGid, TestModuleStatementId),
            atomizer: AtomizerRegistry.NoAtomizerId).RequireDigestionEntries());

    private static BackfillInventoryDocument DuplicateLedger(params DigestionLedgerEntry[] entries)
    {
        var template = Ledger(
            CompleteWitnessAtom(),
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed,
            DuplicateProbeGid,
            new DigestionCoverageEdge(DuplicateProbeGid, TestModuleStatementId),
            atomizer: AtomizerRegistry.NoAtomizerId);
        var source = Assert.Single(template.RequireDigestionSources());
        return template.WithDigestionSources([source with { Entries = [.. entries] }]);
    }

    private static RepositorySnapshot DuplicateSnapshot(params DigestionAtom[] atoms) =>
        Snapshot([
            ("docs/source.md", Encoding.UTF8.GetBytes("manual specification receipu\n")),
            .. atoms.Select(CasFile),
            (DuplicateProbePath, Encoding.UTF8.GetBytes(Lean(DuplicateProbeGid))),
            .. FrozenLedgerFiles(DuplicateProbePath),
        ]);
}
