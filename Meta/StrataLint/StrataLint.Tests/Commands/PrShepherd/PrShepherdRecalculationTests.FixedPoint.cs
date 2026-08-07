namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    [Fact]
    public void DerivedLaneCommitsEmissionsUntilTheTruthGraphReachesAFixedPoint()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(
            conflicting: true,
            ledgerConflict: true,
            truthGraphDirtyRounds: 2);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(2, fixture.CountCommitsWithSubject(CommitSubject));
        Assert.Equal(3, fixture.MutationCalls().Count(call => call == "emit"));
        Assert.Contains("emit-check", fixture.MutationCalls());
        Assert.Contains("push", fixture.MutationCalls());

        var observations = fixture.FixedPointObservations();
        Assert.Equal(3, observations.Length);
        Assert.Equal(3, observations.Select(line => line.Split(':')[2]).Distinct().Count());
    }

    [Fact]
    public void DerivedLaneAlertsWithoutPushWhenThreeRoundsDoNotConverge()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ShepherdFixture(truthGraphDirtyRounds: 4);

        var result = fixture.Run();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(fixture.OriginalHead, fixture.RemoteHead());
        Assert.Equal(3, fixture.MutationCalls().Count(call => call == "emit"));
        Assert.DoesNotContain("emit-check", fixture.MutationCalls());
        Assert.DoesNotContain("push", fixture.MutationCalls());
        Assert.Contains(
            "ALERT #1 truth graph 3 轮未收敛,不 push",
            result.Log,
            StringComparison.Ordinal);
    }
}
