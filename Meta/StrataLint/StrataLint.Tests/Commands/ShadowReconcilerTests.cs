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
    [Fact] public void FirstAttemptWins() { var j=new[]{Job(1,10,"miss",5),Job(1,11,"hit"),Job(2,20)}; var r=ShadowReconciler.Reconcile(j,2); Assert.True(r.Halted); Assert.Equal(2.5,r.AmortisedMissSeconds); }
}
