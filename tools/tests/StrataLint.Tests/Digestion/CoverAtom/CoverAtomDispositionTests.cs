using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CoverAtomTests
{
    private static void AssertFailedDispositionDoesNotAdmitCoverage(CoverExecution execution)
    {
        Assert.NotEqual(execution.Before, execution.After);
        var entry = Assert.Single(
            execution.AfterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.NotNull(entry.Receipts.CoverDisposition);
        Assert.Empty(entry.CoverageGids);
        Assert.Empty(entry.Receipts.Coverage);
        Assert.Empty(entry.Receipts.Scribe);
        Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
    }

    [Fact]
    public void CoverRecordsPartialClosedDispositionWithoutAdmittingCoverage()
    {
        var execution = Execute(new CoverSpec
        {
            InitialUnresolvedSubitems = ["remaining theorem clause"],
        });

        Assert.False(execution.Result.Success);
        Assert.Contains("partial-closed", execution.Result.Error, StringComparison.Ordinal);
        Assert.NotEqual(execution.Before, execution.After);
        var entry = Assert.Single(
            execution.AfterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        var disposition = Assert.IsType<DigestionCoverDisposition>(
            entry.Receipts.CoverDisposition);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed),
            disposition.Outcome);
        Assert.Equal(["D5/S0/Carrier/Probe.probe"], disposition.Gids.ToArray());
        var gap = Assert.Single(disposition.Gaps);
        Assert.Equal("unresolved-subitem", gap.Code);
        Assert.Equal("remaining theorem clause", gap.Detail);
        Assert.Equal(CoverWorld.RecordedAtUtc, disposition.RecordedAtUtc);
        Assert.Empty(entry.CoverageGids);
        Assert.Empty(entry.Receipts.Coverage);
        Assert.Empty(entry.Receipts.Scribe);
        Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
    }

    [Fact]
    public void SuccessfulCoverClearsPriorDisposition()
    {
        var spec = new CoverSpec();
        var execution = ExecuteWithPriorDisposition(spec, PriorDisposition(spec.Gid));

        Assert.True(execution.Result.Success, execution.Result.Error);
        var entry = Assert.Single(
            execution.AfterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == spec.AtomId);
        Assert.Null(entry.Receipts.CoverDisposition);
        Assert.Equal([spec.Gid], entry.CoverageGids.ToArray());
    }

    [Fact]
    public void FailedRetryReplacesPriorCoverDisposition()
    {
        var spec = new CoverSpec
        {
            InitialUnresolvedSubitems = ["new failed retry"],
        };
        var prior = PriorDisposition("D5/S0/Carrier/Probe.prior_probe");

        var execution = ExecuteWithPriorDisposition(spec, prior);

        Assert.False(execution.Result.Success);
        var entry = Assert.Single(
            execution.AfterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == spec.AtomId);
        var replacement = Assert.IsType<DigestionCoverDisposition>(
            entry.Receipts.CoverDisposition);
        Assert.Equal([spec.Gid], replacement.Gids.ToArray());
        var gap = Assert.Single(replacement.Gaps);
        Assert.Equal("unresolved-subitem", gap.Code);
        Assert.Equal("new failed retry", gap.Detail);
        Assert.Equal(CoverWorld.RecordedAtUtc, replacement.RecordedAtUtc);
        Assert.Empty(entry.CoverageGids);
        Assert.Empty(entry.Receipts.Coverage);
        Assert.Empty(entry.Receipts.Scribe);
    }

    private static DigestionCoverDisposition PriorDisposition(string gid) =>
        new(
            new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Closed),
            [gid],
            [new DigestionDispositionGap(
                "unresolved-subitem",
                "prior failed attempt")],
            new DateTimeOffset(2026, 8, 25, 4, 3, 2, TestBudgets.ZeroDuration));

    private static CoverExecution ExecuteWithPriorDisposition(
        CoverSpec spec,
        DigestionCoverDisposition disposition)
    {
        var inputs = spec.Materialize();
        var document = inputs.Document.WithDigestionSources(
            inputs.Document.RequireDigestionSources()
                .Select(source => source with
                {
                    Entries = source.Entries.Select(entry => entry with
                    {
                        Receipts = entry.Receipts with { CoverDisposition = disposition },
                    }).ToImmutableArray(),
                }).ToImmutableArray());
        var currentFiles = DirectoryLedgerTestSupport.Project(inputs.Files);
        DirectoryLedgerTestSupport.ReplaceWithProjection(currentFiles, document);
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, currentFiles);
        var before = DirectoryLedgerTestSupport.Image(
            BackfillInventoryLoader.LoadRoot(temporary.Path));

        var result = CoverWorld.Environment(temporary.Path, inputs, currentFiles).CoverAtom(
            ["--cover-atom", spec.AtomId, "--gid", inputs.Gid, "--base", "baseline",
                "--envelope", inputs.EnvelopePath]);

        var afterDocument = BackfillInventoryLoader.LoadRoot(temporary.Path);
        return new CoverExecution(
            result,
            DirectoryLedgerTestSupport.Image(afterDocument),
            before,
            afterDocument);
    }
}
