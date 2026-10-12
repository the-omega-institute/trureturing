using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData("commit: lane work")]
    [InlineData("commit (amend): lane work")]
    [InlineData("commit (merge): lane work")]
    [InlineData("cherry-pick: lane work")]
    [InlineData("rebase (finish): returning to refs/heads/harness/witness")]
    [InlineData("rebase (pick): lane work")]
    [InlineData("rebase -i (finish): returning to refs/heads/harness/witness")]
    public void ProducingHeadEventsSupplyWorkWitness(string message)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/witness");
        fixture.RewriteLastRecord(lane, message: message);

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddMinutes(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("merged_to_dev", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData("reset: moving to HEAD")]
    [InlineData("checkout: moving from old-task to dev")]
    [InlineData("merge dev: Fast-forward")]
    [InlineData("pull: Fast-forward")]
    [InlineData("rebase (start): checkout dev")]
    [InlineData("commit (initial): lane work")]
    [InlineData("merge dev: Merge made by the 'ort' strategy.")]
    public void NonProducingEventsCannotSupplyWorkWitness(string message)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/non-witness");
        fixture.RewriteLastRecord(lane, message: message);

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddMinutes(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("recently_updated", ReasonFor(result.Output, lane));
        AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_reason", "merged_without_work_witness");
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void WitnessRequiresNonzeroDistinctOldHead(bool zero)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/unchanged-head");
        fixture.RewriteLastRecord(lane, oldHead: zero ? new string('0', 40) : fixture.Head(lane));

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddMinutes(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_reason", "merged_without_work_witness");
    }

    [Fact]
    public void ActualMergeCommitIsAWorkWitness()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/merge-witness", landed: false);
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "commit", "--allow-empty", "-m", "dev work");
        CleanLanesFixture.Git(lane, "merge", "--no-ff", "-m", "merge dev", "dev");
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "merge", "--ff-only", "harness/merge-witness");

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddMinutes(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("merged_to_dev", ReasonFor(result.Output, lane));
    }

    [Fact]
    public void SquashMergeDoesNotSupplyAncestryEvidence()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddMergedLane("harness/squashed");
        File.WriteAllText(Path.Combine(lane, "work.txt"), "lane work\n");
        CleanLanesFixture.Git(lane, "add", "work.txt");
        CleanLanesFixture.Git(lane, "commit", "-m", "lane work");
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "merge", "--squash", "harness/squashed");
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "commit", "-m", "squash lane work");

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddMinutes(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("recently_updated", ReasonFor(result.Output, lane));
    }

    [Theory]
    [InlineData("MERGE_HEAD")]
    [InlineData("CHERRY_PICK_HEAD")]
    [InlineData("REVERT_HEAD")]
    [InlineData("rebase-merge")]
    [InlineData("rebase-apply")]
    [InlineData("sequencer")]
    public void UnfinishedOperationPreventsMergedShortcut(string marker)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/unfinished-landed");
        var path = Path.Combine(fixture.WorktreeGitDirectory(lane), marker);
        if (marker.EndsWith("HEAD", StringComparison.Ordinal)) File.WriteAllText(path, fixture.Head(lane) + "\n");
        else Directory.CreateDirectory(path);

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddMinutes(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.DoesNotContain(ReadItems(result.Output), item => ItemMatches(item, lane, "removed", "merged_to_dev"));
    }

    [Fact]
    public void OldLaneWithoutWitnessStillUsesOriginalSelectors()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddMergedLane("harness/old-unused");
        fixture.AdvanceBase(300);

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddDays(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.Equal("stale_behind", ReasonFor(result.Output, lane));
        AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_reason", "merged_without_work_witness");
    }

    [Fact]
    public void DetachedWorkedHeadUsesShortcutAndRetainsRecoveryBranchThroughOrphanSweep()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddDetachedJudge("trureturing-detached-work");
        CleanLanesFixture.Git(lane, "commit", "--allow-empty", "-m", "detached work");
        var head = fixture.Head(lane);
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "merge", "--ff-only", head);

        var result = fixture.RunAt(fixture.LastUpdate(lane).AddMinutes(1), "--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        var item = ReadItems(result.Output).Single(item => item.GetProperty("path").GetString() == lane);
        Assert.Equal("merged_to_dev", item.GetProperty("reason").GetString());
        var branch = item.GetProperty("recovery_branch").GetString()!;
        Assert.True(fixture.BranchExists(branch["refs/heads/".Length..]));
        Assert.Equal(head, CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "rev-parse", branch).Trim());
    }
}
