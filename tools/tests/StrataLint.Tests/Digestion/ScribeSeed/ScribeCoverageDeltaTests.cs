using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeCoverageDeltaTests
{
    [Fact]
    public void ChangedCoverageStatementWithoutScribeReceiptIsRejected()
    {
        var fixture = new ScribeSeedFixture();
        fixture.Baseline = ScribeSeedFixture.Map(fixture.Baseline, entry => entry with
        {
            Coverage = [entry.Coverage[0] with { TargetStatementId = null }],
        });
        var repository = fixture.Gateway(RawChangeSet.Create([ScribeSeedFixture.EntryPath(fixture.First)]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-scribe-receipt-required", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void FullScanStillUsesProtectedBaseEdgeValuesForReceiptDebt()
    {
        var fixture = new ScribeSeedFixture(84);
        var repository = fixture.Gateway(RawChangeSet.Create([]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(84, result.Output.Split('\n').Count(line =>
            line.Contains("gaps=scribe-receipt-missing", StringComparison.Ordinal)));
    }

    [Fact]
    public void CandidateNewCoverageWithoutScribeReceiptIsRejected()
    {
        var fixture = new ScribeSeedFixture();
        fixture.Baseline = ScribeSeedFixture.Map(fixture.Baseline, entry => entry with { Coverage = [] });
        var repository = fixture.Gateway(RawChangeSet.Create([ScribeSeedFixture.EntryPath(fixture.First)]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-scribe-receipt-required", result.Error, StringComparison.Ordinal);
        Assert.Contains(fixture.First.AtomId, result.Error, StringComparison.Ordinal);
        Assert.Contains(ScribeSeedFixture.DeclarationGid, result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void UnrelatedDeltaWith84MissingScribeReceiptsIsNonBlockingAndObservable()
    {
        var fixture = new ScribeSeedFixture(84);
        var repository = fixture.Gateway(RawChangeSet.Create(["notes/unrelated.txt"]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(84, result.Output.Split('\n').Count(line =>
            line.Contains("gaps=scribe-receipt-missing", StringComparison.Ordinal)));
        Assert.DoesNotContain("coverage-scribe-receipt-required", result.Output, StringComparison.Ordinal);
    }
}
