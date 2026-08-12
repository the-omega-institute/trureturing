using Xunit;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ShadowReconcilerTests
{
    private static ShadowJob Job(int pr, long run, string outcome = "hit", double? wall = null, bool terminal = true, int attempt = 1) => new(pr, run, attempt, terminal, new[] { new ShadowRecord(pr, run, attempt, "sha", outcome, wall) });
    [Fact] public void NormalWindowPasses() { var r=ShadowReconciler.Reconcile(Enumerable.Range(1,40).Select(i=>Job(i,i)).ToArray()); Assert.True(r.WindowClosed); Assert.False(r.Halted); Assert.Equal(1,r.HitRate); }
    [Fact] public void LowHitRateHalts() { var j=Enumerable.Range(1,40).Select(i=>Job(i,i,i<=31?"hit":"miss",1)).ToArray(); Assert.True(ShadowReconciler.Reconcile(j).Halted); }
    [Fact] public void BudgetHalts() { var j=Enumerable.Range(1,40).Select(i=>Job(i,i,i==40?"miss":"hit",i==40?1201:null)).ToArray(); Assert.True(ShadowReconciler.Reconcile(j).Halted); }
    [Fact] public void MaxHalts() { var j=Enumerable.Range(1,40).Select(i=>Job(i,i,i==40?"miss":"hit",i==40?181:null)).ToArray(); Assert.True(ShadowReconciler.Reconcile(j).Halted); }
    [Fact] public void MissingRecordHalts() { var j=Enumerable.Range(1,40).Select(i=>i==7?new ShadowJob(7,7,1,true,Array.Empty<ShadowRecord>()):Job(i,i)).ToArray(); Assert.True(ShadowReconciler.Reconcile(j).Halted); }
    [Fact]
    public void HaltWithTerminalFailureReportsKnownStatistics()
    {
        var j = Enumerable.Range(1, 3).Select(i => i == 3 ? Job(i, i, "miss", 5, terminal: false) : Job(i, i)).ToArray();

        var result = ShadowReconciler.Reconcile(j, windowSize: 3);

        Assert.True(result.Halted);
        Assert.Equal(3, result.N);
        Assert.Equal(2, result.HitCount);
        Assert.Equal(2d / 3d, result.HitRate);
        Assert.Equal(5d / 3d, result.AmortisedMissSeconds);
        Assert.Equal(5, result.MaxMissSeconds);
    }

    [Fact]
    public void HaltWithMissingRecordReportsNullUnavailableStatistics()
    {
        var j = Enumerable.Range(1, 3).Select(i => i == 3 ? new ShadowJob(i, i, 1, true, Array.Empty<ShadowRecord>()) : Job(i, i)).ToArray();

        var result = ShadowReconciler.Reconcile(j, windowSize: 3);

        Assert.True(result.Halted);
        Assert.Equal(3, result.N);
        Assert.Equal(2, result.HitCount);
        Assert.Null(result.HitRate);
        Assert.Null(result.AmortisedMissSeconds);
        Assert.Null(result.MaxMissSeconds);
    }

    [Fact] public void FirstAttemptWins() { var j=new[]{Job(1,10,"miss",5),Job(1,11,"hit"),Job(2,20)}; var r=ShadowReconciler.Reconcile(j,2); Assert.True(r.Halted); Assert.Equal(2.5,r.AmortisedMissSeconds); }

    [Fact]
    public void SinceRunExcludesRunsAtOrBeforeBoundary()
    {
        var jobs = new[]
        {
            new ShadowJob(899, 99, 1, true, Array.Empty<ShadowRecord>()),
            new ShadowJob(900, 100, 1, true, Array.Empty<ShadowRecord>()),
        }.Concat(Enumerable.Range(101, 40).Select(run => Job(run, run))).ToArray();

        var reopened = ShadowReconciler.Reconcile(jobs, sinceRun: 100);
        var negativeControl = ShadowReconciler.Reconcile(jobs);

        Assert.True(reopened.WindowClosed);
        Assert.False(reopened.Halted);
        Assert.Equal(40, reopened.N);
        Assert.Equal(40, reopened.HitCount);
        Assert.True(negativeControl.Halted);
        Assert.Equal("PR #899: job terminal/record reconciliation failed", negativeControl.HaltReason);
    }

    [Fact]
    public void SameSinceRunProducesSameDecision()
    {
        var jobs = Enumerable.Range(501, 40).Select(run => Job(run, run)).ToArray();

        var first = ShadowReconciler.Reconcile(jobs, sinceRun: 500);
        var second = ShadowReconciler.Reconcile(jobs, sinceRun: 500);
        var negativeControl = ShadowReconciler.Reconcile(jobs, sinceRun: 501);

        Assert.Equal(first, second);
        Assert.True(first.WindowClosed);
        Assert.False(negativeControl.WindowClosed);
        Assert.NotEqual(first, negativeControl);
    }

    [Fact]
    public void OmittingSinceRunPreservesEarliestRunWindow()
    {
        var jobs = new[]
        {
            Job(71, 20),
            Job(71, 10, "miss", 5),
            Job(72, 30),
        };

        var omitted = ShadowReconciler.Reconcile(jobs, windowSize: 2);
        var explicitDefault = ShadowReconciler.Reconcile(jobs, windowSize: 2, sinceRun: null);
        var negativeControl = ShadowReconciler.Reconcile(jobs, windowSize: 2, sinceRun: 10);

        Assert.Equal(explicitDefault, omitted);
        Assert.True(omitted.WindowClosed);
        Assert.True(omitted.Halted);
        Assert.Equal("hit rate below 80%", omitted.HaltReason);
        Assert.Equal(2.5, omitted.AmortisedMissSeconds);
        Assert.False(negativeControl.Halted);
    }

    [Fact]
    public void CommandAcceptsExplicitSinceRun()
    {
        var path = Path.GetTempFileName();
        try
        {
            var jobs = new[]
            {
                new ShadowJob(999, 100, 1, true, Array.Empty<ShadowRecord>()),
                Job(101, 101),
            };
            File.WriteAllText(path, System.Text.Json.JsonSerializer.Serialize(jobs));

            var result = ShadowReconcileCommand.Run(["--since-run", "100", path]);

            Assert.True(result.Success);
            Assert.Contains("\"Halted\":false", result.Output, StringComparison.Ordinal);
            Assert.Contains("\"N\":1", result.Output, StringComparison.Ordinal);
        }
        finally
        {
            File.Delete(path);
        }
    }
}
