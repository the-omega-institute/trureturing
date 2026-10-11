using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CoverAtomTests
{
    [Fact]
    public void CoverRejectsPartialCoverWithoutWritingDisposition()
    {
        var execution = Execute(new CoverSpec
        {
            InitialUnresolvedSubitems = ["remaining theorem clause"],
        });

        Assert.False(execution.Result.Success);
        Assert.Contains("partial-closed", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(execution.Before, execution.After);
        var entry = Assert.Single(
            execution.AfterDocument.RequireDigestionEntries(),
            candidate => candidate.AtomId == CoverWorld.DefaultAtomId);
        Assert.Null(entry.Receipts.CoverDisposition);
        Assert.Empty(entry.CoverageGids);
        Assert.Empty(entry.Coverage);
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
    public void FailedCoverPreservesPriorDisposition()
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
        var preserved = Assert.IsType<DigestionCoverDisposition>(
            entry.Receipts.CoverDisposition);
        Assert.Equal(["D5/S0/Carrier/Probe.prior_probe"], preserved.Gids.ToArray());
        var gap = Assert.Single(preserved.Gaps);
        Assert.Equal("unresolved-subitem", gap.Code);
        Assert.Equal("prior failed attempt", gap.Detail);
        Assert.Empty(entry.CoverageGids);
        Assert.Empty(entry.Coverage);
    }

    private static DigestionCoverDisposition PriorDisposition(string gid) =>
        new(
            new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Closed),
            [gid],
            [new DigestionDispositionGap(
                "unresolved-subitem",
                "prior failed attempt")]);

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
            ["--cover-atom", spec.AtomId, "--gid", inputs.Gid]);

        var afterDocument = BackfillInventoryLoader.LoadRoot(temporary.Path);
        return new CoverExecution(
            result,
            DirectoryLedgerTestSupport.Image(afterDocument),
            before,
            afterDocument);
    }
}
