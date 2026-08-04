using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanReportStatusCommandTests
{
    [Fact]
    public void ValidReportDoesNotRequireTheDigestionLedgerOrCas()
    {
        var repository = Repository();
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["Trureturing.lean"] = new([], []),
        });

        var result = LeanReportStatusCommand.Run(
            repository,
            new FakeLeanReportSource(report),
            []);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("LEAN_REPORT_STATUS valid\n", result.Output);
        Assert.Empty(result.Error);
        Assert.Equal(1, repository.ReadCount);
    }

    [Fact]
    public void InvalidReportHasAnActionSpecificTypedVerdict()
    {
        var result = LeanReportStatusCommand.Run(
            Repository(),
            new ThrowingLeanReportSource(
                new FormatException("Raw Lean report is missing modules: D5/S1/Stale.lean")),
            []);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(
            "LEAN_REPORT_STATUS invalid Raw Lean report is missing modules: D5/S1/Stale.lean\n",
            result.Output);
        Assert.Empty(result.Error);
    }

    [Fact]
    public void SnapshotFailureIsNotReportedAsAnInvalidReport()
    {
        var result = LeanReportStatusCommand.Run(
            new FakeRepositoryGateway(RawChangeSet.Create([]), current: null, baseline: null),
            new ThrowingLeanReportSource(
                new InvalidOperationException("Lean report source must not be called")),
            []);

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.Output);
        Assert.Equal(
            "LEAN_REPORT_STATUS not-checked current snapshot should not be read\n",
            result.Error);
    }

    [Fact]
    public void UnknownArgumentsAreNotCheckedAndCannotAuthorizeRepair()
    {
        var repository = Repository();

        var result = LeanReportStatusCommand.Run(
            repository,
            new ThrowingLeanReportSource(
                new InvalidOperationException("Lean report source must not be called")),
            ["--formalize-candidates"]);

        Assert.Equal(2, result.ExitCode);
        Assert.Empty(result.Output);
        Assert.Equal(
            "LEAN_REPORT_STATUS not-checked USAGE: StrataLint lean-report-status\n",
            result.Error);
        Assert.Equal(0, repository.ReadCount);
    }

    private static FakeRepositoryGateway Repository()
    {
        var current = RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText("Trureturing.lean", "def current : Nat := 1\n"),
        ]);
        return new FakeRepositoryGateway(RawChangeSet.Create([]), current, baseline: null);
    }

    private sealed class ThrowingLeanReportSource(Exception exception) : ILeanReportSource
    {
        public LeanAxiomReport Load(RepositorySnapshot snapshot) => throw exception;
    }
}
