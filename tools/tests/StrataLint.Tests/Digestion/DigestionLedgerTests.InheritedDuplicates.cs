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
