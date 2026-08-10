using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestResidualSummaryTests
{
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
            "synthetic/path",
            null,
            new DigestionFingerprints("sha256:synthetic", "sha256:synthetic"),
            [],
            new DigestionReceipts([], [], [], [], null),
            status,
            null,
            "sha256:synthetic");
        return new DigestionEntryEvaluation(
            entry,
            DigestionReceiptAlignment.Seen,
            status,
            false,
            gaps.Select(static gap => new DigestionGap(gap.Code, gap.Detail)).ToImmutableArray());
    }
}
