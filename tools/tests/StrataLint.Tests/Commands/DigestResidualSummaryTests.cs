using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestResidualSummaryTests
{
    [Fact]
    public void RenderShardsChangesOnlyTheSourceWhoseEntriesChanged()
    {
        var baseline = new DigestionLedgerEvaluation([
            Entry("source-a", "atom-a", ("unresolved-subitem", "a-one")),
            Entry("source-b", "atom-b", ("unresolved-subitem", "b-one")),
        ], []);
        var changedA = new DigestionLedgerEvaluation([
            Entry("source-a", "atom-a", ("unresolved-subitem", "a-two")),
            Entry("source-b", "atom-b", ("unresolved-subitem", "b-one")),
        ], []);
        var changedB = new DigestionLedgerEvaluation([
            Entry("source-a", "atom-a", ("unresolved-subitem", "a-one")),
            Entry("source-b", "atom-b", ("unresolved-subitem", "b-two")),
        ], []);

        var original = DigestResidualSummary.RenderShards(baseline);
        var aPaths = ChangedPaths(original, DigestResidualSummary.RenderShards(changedA));
        var bPaths = ChangedPaths(original, DigestResidualSummary.RenderShards(changedB));

        Assert.Equal(["Generated/echo-residuals/source-a.md"], aPaths);
        Assert.Equal(["Generated/echo-residuals/source-b.md"], bPaths);
        Assert.Empty(aPaths.Intersect(bPaths, StringComparer.Ordinal));
    }

    [Fact]
    public void RenderShardsEmitsSettledSourcesAndKeepsQuarantineInItsSource()
    {
        var quarantined = Entry("source-a", "atom-q", ("unresolved-subitem", "held"));
        quarantined = quarantined with
        {
            Entry = quarantined.Entry with
            {
                Receipts = quarantined.Entry.Receipts with
                {
                    Quarantine = new DigestionQuarantine("because", "when-ready")
                }
            }
        };
        var shards = DigestResidualSummary.RenderShards(new DigestionLedgerEvaluation([
            quarantined,
            Entry("source-b", "atom-settled", ("other-gap", "ignored")),
        ], []));

        Assert.Equal(2, shards.Count);
        Assert.Contains("`atom-q` (1)", shards["Generated/echo-residuals/source-a.md"], StringComparison.Ordinal);
        Assert.Contains("`held`", shards["Generated/echo-residuals/source-a.md"], StringComparison.Ordinal);
        Assert.Contains("Mother residual atoms: none.", shards["Generated/echo-residuals/source-b.md"], StringComparison.Ordinal);
    }

    [Fact]
    public void RenderShardsAddingSourceChangesOnlyItsNewShard()
    {
        var before = DigestResidualSummary.RenderShards(new DigestionLedgerEvaluation([
            Entry("source-a", "atom-a", ("unresolved-subitem", "a-one")),
        ], []));
        var after = DigestResidualSummary.RenderShards(new DigestionLedgerEvaluation([
            Entry("source-a", "atom-a", ("unresolved-subitem", "a-one")),
            Entry("source-b", "atom-b", ("unresolved-subitem", "b-one")),
        ], []));

        Assert.Equal(["Generated/echo-residuals/source-b.md"], ChangedPaths(before, after));
    }

    [Fact]
    public void RenderShardsRemovingSourcesLastEntryChangesOnlyItsShard()
    {
        var before = DigestResidualSummary.RenderShards(new DigestionLedgerEvaluation([
            Entry("source-a", "atom-a", ("unresolved-subitem", "a-one")),
            Entry("source-b", "atom-b", ("unresolved-subitem", "b-one")),
        ], []));
        var after = DigestResidualSummary.RenderShards(new DigestionLedgerEvaluation([
            Entry("source-a", "atom-a", ("unresolved-subitem", "a-one")),
        ], []));

        Assert.Equal(["Generated/echo-residuals/source-b.md"], ChangedPaths(before, after));
    }

    private static string[] ChangedPaths(
        IReadOnlyDictionary<string, string> before,
        IReadOnlyDictionary<string, string> after) => before.Keys
        .Union(after.Keys, StringComparer.Ordinal)
        .Where(path =>
            !before.TryGetValue(path, out var beforeContent)
            || !after.TryGetValue(path, out var afterContent)
            || !string.Equals(beforeContent, afterContent, StringComparison.Ordinal))
        .Order(StringComparer.Ordinal)
        .ToArray();

    [Fact]
    public void RenderDerivesExactPerSourceCountsAndMotherAtomsDeterministically()
    {
        var entries = new[]
        {
            Entry("source-b", "atom-b", ("unresolved-subitem", "zeta"), ("other-gap", "ignored"), ("unresolved-subitem", "alpha")),
            Entry("spec-v1", "spec-settled", ("other-gap", "ignored")),
            Entry("source-a", "atom-z", ("unresolved-subitem", "source-a-only"), ("unresolved-subitem", "alpha")),
            Entry("source-b", "atom-a", ("unresolved-subitem", "alpha")),
        };
        var expected = """
            # Echo Residual Summary

            - unresolved_subitems: 5
            - mother_residual_atom_ids: 3

            ## quarantined residuals

            - quarantined_subitems: 0
            - mother_quarantined_atom_ids: 0

            Quarantined residual atoms: none.

            ## cross-volume shared residues

            - shared_residue_names: 1
            - host_atoms: 3

            Shared residue hosts:

            - `alpha` (2 volumes, 3 host atoms): `source-a/atom-z`, `source-b/atom-a`, `source-b/atom-b`

            ## `source-a`

            - unresolved_subitems: 2
            - mother_residual_atom_ids: 1

            Mother residual atoms:

            - `atom-z` (2)
              - `alpha`
              - `source-a-only`

            ## `source-b`

            - unresolved_subitems: 3
            - mother_residual_atom_ids: 2

            Mother residual atoms:

            - `atom-a` (1)
              - `alpha`
            - `atom-b` (2)
              - `alpha`
              - `zeta`

            ## `spec-v1`

            - unresolved_subitems: 0
            - mother_residual_atom_ids: 0

            Mother residual atoms: none.
            """ + "\n";

        var forward = DigestResidualSummary.Render(new DigestionLedgerEvaluation([.. entries], []));
        var reverse = DigestResidualSummary.Render(new DigestionLedgerEvaluation([.. entries.Reverse()], []));

        Assert.Equal(expected, forward);
        Assert.Equal(expected, reverse);
    }

    [Fact]
    public void RenderStatesWhenNoResidueIsSharedAcrossVolumes()
    {
        var entries = new[]
        {
            Entry("source-a", "atom-a", ("unresolved-subitem", "source-a-only")),
            Entry("source-b", "atom-b", ("unresolved-subitem", "source-b-only")),
        };

        var summary = DigestResidualSummary.Render(new DigestionLedgerEvaluation([.. entries], []));

        Assert.Contains(
            """
            ## cross-volume shared residues

            - shared_residue_names: 0
            - host_atoms: 0

            Shared residue hosts: none.
            """,
            summary,
            StringComparison.Ordinal);
    }

    private static DigestionEntryEvaluation Entry(
        string sourceId,
        string atomId,
        params (string Code, string Detail)[] gaps)
    {
        var status = new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed);
        var entry = new DigestionLedgerEntry(
            sourceId,
            "synthetic.md",
            "synthetic-v1",
            atomId,
            new DigestionFingerprints("sha256:synthetic", "sha256:synthetic"),
            [],
            new DigestionReceipts([], [], [], [], null),
            status,
            "sha256:synthetic");
        return new DigestionEntryEvaluation(
            entry,
            DigestionReceiptAlignment.Seen,
            status,
            false,
            gaps.Select(static gap => new DigestionGap(
                gap.Code,
                gap.Detail,
                DigestionGapSeverity.NonFatal)).ToImmutableArray());
    }
}
