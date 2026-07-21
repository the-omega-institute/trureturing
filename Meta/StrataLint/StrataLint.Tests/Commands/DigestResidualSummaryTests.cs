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
            Entry("source-a", "atom-z", ("unresolved-subitem", "source-a-only")),
            Entry("source-b", "atom-a", ("unresolved-subitem", "alpha")),
        };
        var expected = """
            <!-- stratalint:echo-residual-summary:start -->
            # Echo Residual Summary

            - candidate_snapshot_sha256: `sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa`
            - baseline_snapshot_sha256: `sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb`
            - unresolved_subitems: 4
            - mother_residual_atom_ids: 3

            ## `source-a`

            - unresolved_subitems: 1
            - mother_residual_atom_ids: 1

            Mother residual atoms:

            - `atom-z` (1)
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

            <!-- stratalint:echo-residual-summary:end -->
            """ + "\n";

        var forward = DigestResidualSummary.Render(
            new DigestionLedgerEvaluation([.. entries], []),
            "sha256:" + new string('a', 64),
            "sha256:" + new string('b', 64));
        var reverse = DigestResidualSummary.Render(
            new DigestionLedgerEvaluation([.. entries.Reverse()], []),
            "sha256:" + new string('a', 64),
            "sha256:" + new string('b', 64));

        Assert.Equal(expected, forward);
        Assert.Equal(expected, reverse);
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
