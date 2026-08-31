using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionQuarantineTests
{
    private const string CoverDisposition = """
        cover_disposition:
          outcome: partial-closed
          recorded_at_utc: 2026-08-25T04:03:02.0000000+00:00
          gids:
            - D5/S0/Carrier/Probe.probe
          gaps:
            - code: unresolved-subitem
              detail: remaining theorem clause
        """;

    public static TheoryData<string> InvalidCoverDispositions => new()
    {
        CoverDisposition.Replace(
            "  gaps:",
            "  unexpected: value\n  gaps:",
            StringComparison.Ordinal),
        CoverDisposition.Replace("+00:00", "+08:00", StringComparison.Ordinal),
        CoverDisposition.Replace(
            "    - D5/S0/Carrier/Probe.probe",
            "    - D5/S0/Carrier/Probe.zeta\n    - D5/S0/Carrier/Probe.alpha",
            StringComparison.Ordinal),
        CoverDisposition.Replace(
            "    - code: unresolved-subitem\n      detail: remaining theorem clause",
            "    - code: z-gap\n      detail: final\n    - code: a-gap\n      detail: first",
            StringComparison.Ordinal),
        CoverDisposition.Replace(
            "D5/S0/Carrier/Probe.probe",
            "not-a-gid",
            StringComparison.Ordinal),
    };

    [Fact]
    public void LoaderWriterLoaderReplaysCoverDispositionByteIdentically()
    {
        var document = BackfillInventoryLoader.Load(
            DirectorySnapshot(Atom(AtomId, CoverDisposition)));
        var entry = Assert.Single(document.RequireDigestionEntries());
        var disposition = Assert.IsType<DigestionCoverDisposition>(
            entry.Receipts.CoverDisposition);

        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed),
            disposition.Outcome);
        Assert.Equal(["D5/S0/Carrier/Probe.probe"], disposition.Gids.ToArray());
        Assert.Equal(
            new DateTimeOffset(2026, 8, 25, 4, 3, 2, TestBudgets.ZeroDuration),
            disposition.RecordedAtUtc);

        var first = BackfillInventoryWriter.WriteAtom(entry);
        var firstText = Encoding.UTF8.GetString(first.AsSpan());
        Assert.Contains(
            """
              cover_disposition:
                outcome: partial-closed
                recorded_at_utc: 2026-08-25T04:03:02.0000000+00:00
                gids:
                  - D5/S0/Carrier/Probe.probe
                gaps:
                  - code: unresolved-subitem
                    detail: remaining theorem clause
            """ + "\n",
            firstText,
            StringComparison.Ordinal);
        var replayed = Assert.Single(BackfillInventoryLoader.Load(
                DirectorySnapshot(firstText))
            .RequireDigestionEntries());
        var second = BackfillInventoryWriter.WriteAtom(replayed);

        Assert.True(first.AsSpan().SequenceEqual(second.AsSpan()));
    }

    [Theory]
    [MemberData(nameof(InvalidCoverDispositions))]
    public void LoaderRejectsNoncanonicalCoverDisposition(string disposition)
    {
        var error = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.Load(DirectorySnapshot(Atom(AtomId, disposition))));

        Assert.Contains("cover_disposition", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void LoaderRejectsCoverDispositionWithAdmittedCoverage()
    {
        var atom = Atom(AtomId, CoverDisposition).Replace(
            "coverage_gids: []",
            "coverage_gids:\n  - D5/S0/Carrier/Probe.probe",
            StringComparison.Ordinal);

        var error = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.Load(DirectorySnapshot(atom)));

        Assert.Contains("cover_disposition", error.Message, StringComparison.Ordinal);
        Assert.Contains("coverage_gids", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void LoaderRejectsCoverDispositionWithQuarantine()
    {
        var error = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.Load(DirectorySnapshot(
                Atom(AtomId, CoverDisposition + "\n" + Quarantine))));

        Assert.Contains("cover_disposition", error.Message, StringComparison.Ordinal);
        Assert.Contains("quarantine", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ResidualSelectorsExcludeCoverDispositionAtoms()
    {
        var entry = new DigestionLedgerEntry(
            "fixture-source",
            "docs/source.md",
            AtomizerRegistry.NoAtomizerId,
            "atom-dispositioned",
            new DigestionFingerprints(Digest, Digest),
            [],
            new DigestionReceipts(
                [],
                [],
                ["remaining theorem clause"],
                [],
                null,
                CoverDisposition: new DigestionCoverDisposition(
                    new DigestionStatus(
                        DigestionMigrationState.Partial,
                        DigestionTruthState.Closed),
                    ["D5/S0/Carrier/Probe.probe"],
                    [new DigestionDispositionGap(
                        "unresolved-subitem",
                        "remaining theorem clause")],
                    new DateTimeOffset(2026, 8, 25, 4, 3, 2, TestBudgets.ZeroDuration))),
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            Digest);
        var evaluated = new DigestionEntryEvaluation(
            entry,
            DigestionReceiptAlignment.Seen,
            entry.ProjectedStatus,
            false,
            [new DigestionGap(
                "unresolved-subitem",
                "remaining theorem clause",
                DigestionGapSeverity.NonFatal)]);
        var evaluation = new DigestionLedgerEvaluation([evaluated], []);

        var summary = DigestResidualSummary.Render(evaluation);
        var shard = Assert.Single(DigestResidualSummary.RenderShards(evaluation)).Value;

        Assert.DoesNotContain(entry.AtomId, summary, StringComparison.Ordinal);
        Assert.DoesNotContain(entry.AtomId, shard, StringComparison.Ordinal);
        Assert.Contains("mother_residual_atom_ids: 0", summary, StringComparison.Ordinal);
        Assert.Contains("mother_residual_atom_ids: 0", shard, StringComparison.Ordinal);
    }
}
