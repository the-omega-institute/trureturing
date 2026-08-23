using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Fact]
    public void ClosedPullRequestCannotAuthorizeDeletionWhenOtherMergeTermsQualify()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/pr-state-mismatch";
        var lane = fixture.AddLandedLane(branch);
        var head = fixture.Head(lane);
        fixture.RegisterPullRequests(
            branch,
            new PullRequestInfo(branch, head, "CLOSED", head));

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("pr_not_merged", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void MergedPullRequestForDifferentHeadBranchCannotAuthorizeLaneDeletion()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/pr-lookup-branch";
        var lane = fixture.AddLandedLane(branch);
        var head = fixture.Head(lane);
        fixture.RegisterPullRequests(
            branch,
            new PullRequestInfo("harness/different-head-branch", head, "MERGED", head));

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("pr_not_merged", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void MergeCommitMustBeReachableEvenWhenHeadOidIsReachable()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/pr-merge-unreachable";
        var lane = fixture.AddLandedLane(branch);
        var reachableHead = fixture.Head(lane);
        var unmergedLane = fixture.AddUnmergedLane("harness/pr-unreachable-source");
        var unreachableMergeCommit = fixture.Head(unmergedLane);
        Assert.Equal(fixture.Head(fixture.RepositoryWorkingDirectory), reachableHead);
        Assert.NotEqual(reachableHead, unreachableMergeCommit);
        fixture.RegisterPullRequests(
            branch,
            new PullRequestInfo(branch, reachableHead, "MERGED", unreachableMergeCommit));

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("pr_not_merged", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void MalformedPullRequestListCannotFallThroughToLaterQualifyingPullRequest()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/pr-malformed-list";
        var lane = fixture.AddLandedLane(branch);
        var head = fixture.Head(lane);
        fixture.RegisterPullRequests(
            branch,
            new PullRequestInfo(string.Empty, head, "OPEN", null),
            new PullRequestInfo(branch, head, "MERGED", head));

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("pr_unknown", ReasonFor(result.Output, lane));
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
