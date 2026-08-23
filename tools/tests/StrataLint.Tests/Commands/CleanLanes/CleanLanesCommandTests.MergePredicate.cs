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
    public void WellFormedNonQualifyingPullRequestFallsThroughToLaterQualifyingPullRequest()
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/pr-well-formed-list";
        var lane = fixture.AddLandedLane(branch);
        var head = fixture.Head(lane);
        fixture.RegisterPullRequests(
            branch,
            new PullRequestInfo(branch, head, "CLOSED", null),
            new PullRequestInfo(branch, head, "MERGED", head));

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("merged_clean", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void PullRequestHeadOidMustBeObjectOid() =>
        AssertMalformedPullRequestIsUnknown(
            "harness/pr-malformed-head-oid",
            static (branch, _) => new PullRequestInfo(branch, "not-an-oid", "OPEN", null));

    [Fact]
    public void PullRequestStateMustBeRecognized() =>
        AssertMalformedPullRequestIsUnknown(
            "harness/pr-malformed-state",
            static (branch, head) => new PullRequestInfo(branch, head, "DRAFT", null));

    [Fact]
    public void NonNullPullRequestMergeCommitMustBeObjectOid() =>
        AssertMalformedPullRequestIsUnknown(
            "harness/pr-malformed-merge-oid",
            static (branch, head) => new PullRequestInfo(branch, head, "OPEN", "not-an-oid"));

    [Fact]
    public void MergedPullRequestMustNameMergeCommit() =>
        AssertMalformedPullRequestIsUnknown(
            "harness/pr-missing-merge-oid",
            static (_, head) => new PullRequestInfo(
                "harness/different-head-branch",
                head,
                "MERGED",
                null));

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

    private static void AssertMalformedPullRequestIsUnknown(
        string branch,
        Func<string, string, PullRequestInfo> createPullRequest)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane(branch);
        fixture.RegisterPullRequests(branch, createPullRequest(branch, fixture.Head(lane)));

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("pr_unknown", ReasonFor(result.Output, lane));
    }
}
