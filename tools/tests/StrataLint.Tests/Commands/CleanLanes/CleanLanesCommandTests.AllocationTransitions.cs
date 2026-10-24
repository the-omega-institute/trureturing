namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void AllocationGraceSurvivesAttachmentChanges(bool dirty, bool detach)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/allocation-origin");
        var saved = fixture.Head(lane);
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.GitAt(lane, allocated.AddDays(-2), "branch", "harness/old-destination");
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", "harness/claimed-allocation");
        if (detach)
            CleanLanesFixture.GitAt(lane, allocated.AddSeconds(60), "checkout", "--detach", "HEAD");
        else
            CleanLanesFixture.GitAt(lane, allocated.AddSeconds(60), "switch", "harness/old-destination");
        if (dirty)
        {
            File.WriteAllText(Path.Combine(lane, "ordinary.txt"), "recoverable bytes\n");
            fixture.AdvanceBase(300);
        }
        var grace = dirty ? 86400 : 10800;

        var recent = fixture.RunAt(allocated.AddSeconds(grace - 1), "--force", "--lanes-only");

        Assert.True(recent.Success, recent.Error);
        Assert.Equal("recently_updated", ReasonFor(recent.Output, lane));
        Assert.True(Directory.Exists(lane));
        Assert.Equal(saved, fixture.Head(lane));
        if (dirty) Assert.Equal("recoverable bytes\n", File.ReadAllText(Path.Combine(lane, "ordinary.txt")));

        var elapsed = fixture.RunAt(allocated.AddSeconds(grace), "--force", "--lanes-only");

        Assert.True(elapsed.Success, elapsed.Error);
        Assert.Equal(dirty ? "stale_behind" : "merged_to_dev", ReasonFor(elapsed.Output, lane));
        Assert.False(Directory.Exists(lane));
    }

    [Fact]
    public void ReturningToClaimedBranchDoesNotRenewAllocationGrace()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/allocation-return");
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", "harness/allocation-return-claim");
        CleanLanesFixture.GitAt(lane, allocated.AddHours(1), "checkout", "--detach", "HEAD");
        CleanLanesFixture.GitAt(lane, allocated.AddHours(2), "switch", "harness/allocation-return-claim");

        var result = fixture.RunAt(allocated.AddHours(3), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal("merged_to_dev", ReasonFor(result.Output, lane));
        Assert.False(Directory.Exists(lane));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ExplicitAllocationRecordSurvivesBranchRetirement(bool detach)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/allocation-record-origin");
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        var saved = fixture.Head(lane);
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", "harness/allocation-record-claim");
        CleanLanesFixture.GitAt(lane, allocated, "update-ref", "-m",
            "worktree-allocation:0123456789abcdef0123456789abcdef", "HEAD", saved, saved);
        if (detach)
            CleanLanesFixture.GitAt(lane, allocated.AddSeconds(60), "checkout", "--detach", "HEAD");
        else
            CleanLanesFixture.GitAt(lane, allocated.AddSeconds(60), "switch", "harness/allocation-record-origin");
        CleanLanesFixture.Git(lane, "branch", "-D", "harness/allocation-record-claim");

        var recent = fixture.RunAt(allocated.AddSeconds(10799), "--force", "--lanes-only");
        var elapsed = fixture.RunAt(allocated.AddSeconds(10800), "--force", "--lanes-only");

        Assert.True(recent.Success, recent.Error);
        Assert.True(elapsed.Success, elapsed.Error);
        Assert.Equal("recently_updated", ReasonFor(recent.Output, lane));
        Assert.Equal("merged_to_dev", ReasonFor(elapsed.Output, lane));
        Assert.False(Directory.Exists(lane));
    }
}
