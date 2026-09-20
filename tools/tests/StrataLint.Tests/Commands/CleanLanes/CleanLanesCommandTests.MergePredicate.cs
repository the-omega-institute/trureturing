using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void SummaryModeTracksForceAndDryRunInput()
    {
        using var fixture = new CleanLanesFixture();

        var force = fixture.Run("--force", "--lanes-only");
        var dryRun = fixture.Run("--lanes-only");

        Assert.True(force.Success, force.Error);
        Assert.True(dryRun.Success, dryRun.Error);
        Assert.Equal("force", ReadSummary(force.Output).GetProperty("mode").GetString());
        Assert.Equal("dry_run", ReadSummary(dryRun.Output).GetProperty("mode").GetString());
    }

    [Fact]
    public void SummaryBaseCoordinatesTrackNonDevBaseInput()
    {
        using var fixture = new CleanLanesFixture();
        const string alternateBase = "harness/summary-alternate-base";
        var lane = fixture.AddUnmergedLane(alternateBase);
        var devCommit = fixture.Head(fixture.RepositoryWorkingDirectory);
        var alternateCommit = fixture.Head(lane);

        var dev = fixture.Run("--lanes-only");
        var alternate = fixture.RunWithBase(alternateBase, "--lanes-only");

        Assert.True(dev.Success, dev.Error);
        Assert.True(alternate.Success, alternate.Error);
        Assert.NotEqual(devCommit, alternateCommit);
        Assert.Equal("dev", ReadSummary(dev.Output).GetProperty("base_revision").GetString());
        var alternateSummary = ReadSummary(alternate.Output);
        Assert.Equal(alternateBase, alternateSummary.GetProperty("base_revision").GetString());
        Assert.Equal(alternateCommit, alternateSummary.GetProperty("base_commit").GetString());
    }

    [Fact]
    public void SummaryPinsModeBaseRevisionAndResolvedBaseCommit()
    {
        using var fixture = new CleanLanesFixture();
        var expectedBaseCommit = fixture.Head(fixture.RepositoryWorkingDirectory);

        var result = fixture.Run("--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        var summary = ReadSummary(result.Output);
        Assert.Equal("force", summary.GetProperty("mode").GetString());
        Assert.Equal("dev", summary.GetProperty("base_revision").GetString());
        Assert.Equal(expectedBaseCommit, summary.GetProperty("base_commit").GetString());
    }

}
