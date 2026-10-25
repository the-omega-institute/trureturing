namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData("token")]
    [InlineData("oids")]
    public void InvalidExplicitAllocationRetainsTreeInPreviewAndForce(string shape)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/invalid-allocation-record");
        var saved = fixture.Head(lane);
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.GitAt(lane, allocated, "update-ref", "-m",
            "worktree-allocation:0123456789abcdef0123456789abcdef", "HEAD", saved, saved);
        var log = Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD");
        var lines = File.ReadAllLines(log);
        if (shape == "token")
            lines[^1] = lines[^1].Replace("0123456789abcdef0123456789abcdef", "invalid", StringComparison.Ordinal);
        else
            lines[^1] = CleanLanesFixture.Git(lane, "rev-parse", "HEAD^").Trim() + lines[^1][saved.Length..];
        File.WriteAllLines(log, lines);

        foreach (var force in new[] { false, true })
        {
            var result = fixture.RunAt(allocated.AddDays(2), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(result.Success, result.Error);
            Assert.Equal("update_unknown", ReasonFor(result.Output, lane));
            AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_detail", "allocation_record_invalid");
            Assert.True(Directory.Exists(lane));
            Assert.True(fixture.WorktreeRegistered(lane));
            Assert.Equal(saved, fixture.Head(lane));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ExpiredBranchCreationRequiresDominatedTimestamp(bool dominated)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/expired-branch-creation");
        var saved = fixture.Head(lane);
        var anchor = fixture.LastUpdate(lane).AddDays(2);
        fixture.RewriteLogTimes(Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD"), anchor);
        var branchLog = fixture.BranchLogPath(lane);
        File.WriteAllLines(branchLog, File.ReadAllLines(branchLog).TakeLast(1));
        fixture.RewriteLogTimes(branchLog, anchor.AddSeconds(dominated ? 0 : 1));
        var fields = File.ReadAllText(branchLog).Split(' ');
        Assert.Contains(fields[0], static c => c != '0');
        Assert.Equal(saved, fields[1]);

        foreach (var force in new[] { false, true })
        {
            var result = fixture.RunAt(anchor.AddDays(2), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(result.Success, result.Error);
            Assert.Equal(dominated ? "merged_to_dev" : "update_unknown", ReasonFor(result.Output, lane));
            if (!dominated)
                AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_detail", "branch_allocation_unverifiable");
            Assert.Equal(!force || !dominated, Directory.Exists(lane));
            Assert.Equal(!force || !dominated, fixture.WorktreeRegistered(lane));
            if (Directory.Exists(lane)) Assert.Equal(saved, fixture.Head(lane));
        }
    }

    [Theory]
    [InlineData("origin/dev")]
    [InlineData("refs/heads/dev")]
    public void AmbiguousCheckoutIgnoresLocalBranchNamespaceDirectories(string destination)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/branch-namespace");
        var checkout = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.Git(lane, "update-ref", "refs/remotes/origin/dev", fixture.Head(lane));
        CleanLanesFixture.Git(lane, "branch", destination + "/child");
        var prefixLog = Path.Combine(fixture.RepositoryRoot, ".git", "logs", "refs", "heads", destination);
        Assert.True(Directory.Exists(prefixLog));
        CleanLanesFixture.GitAt(lane, checkout, "checkout", "--detach", destination);

        foreach (var force in new[] { false, true })
        {
            var result = fixture.RunAt(checkout.AddHours(3), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(result.Success, result.Error);
            Assert.Equal("merged_to_dev", ReasonFor(result.Output, lane));
            Assert.Equal(!force, Directory.Exists(lane));
        }
    }

    [Theory]
    [InlineData("origin/dev")]
    [InlineData("refs/remotes/origin/dev")]
    [InlineData("refs/heads/dev")]
    [InlineData("heads/dev")]
    [InlineData("allocation-tag")]
    [InlineData("refs/tags/allocation-tag")]
    [InlineData("full-oid")]
    [InlineData("short-oid")]
    [InlineData("HEAD^0")]
    [InlineData("dev^{commit}")]
    public void CheckoutDestinationsUseOnlyApplicableAllocationAmbiguity(string revision)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/nonbranch-checkout");
        var saved = fixture.Head(lane);
        var checkout = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.Git(lane, "update-ref", "refs/remotes/origin/dev", saved);
        CleanLanesFixture.Git(lane, "tag", "allocation-tag", saved);
        var destination = revision == "full-oid" ? saved : revision == "short-oid" ? saved[..7] : revision;
        CleanLanesFixture.GitAt(lane, checkout, "checkout", "--detach", destination);
        var headLog = File.ReadAllLines(Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD"));
        Assert.EndsWith(" to " + destination, headLog[^1], StringComparison.Ordinal);

        var ambiguous = revision is not ("HEAD^0" or "dev^{commit}");
        if (ambiguous)
            foreach (var force in new[] { false, true })
            {
                var recent = fixture.RunAt(checkout.AddSeconds(10799), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

                Assert.True(recent.Success, recent.Error);
                Assert.Equal("recently_updated", ReasonFor(recent.Output, lane));
                Assert.True(Directory.Exists(lane));
            }

        foreach (var force in new[] { false, true })
        {
            var result = fixture.RunAt(checkout.AddHours(ambiguous ? 3 : 1), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(result.Success, result.Error);
            Assert.Equal("merged_to_dev", ReasonFor(result.Output, lane));
            Assert.Equal(!force, Directory.Exists(lane));
            Assert.Equal(!force, fixture.WorktreeRegistered(lane));
        }
    }

    [Theory]
    [InlineData("HEAD")]
    [InlineData("HEAD~1")]
    [InlineData("@{-1}")]
    [InlineData("x^0")]
    [InlineData("a..b")]
    [InlineData(":path")]
    public void RevisionExpressionCheckoutDoesNotAllocateTree(string destination)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/revision-expression");
        var checkout = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.GitAt(lane, checkout, "checkout", "--detach", "HEAD");
        var log = Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD");
        var lines = File.ReadAllLines(log);
        Assert.EndsWith(" to HEAD", lines[^1], StringComparison.Ordinal);
        lines[^1] = lines[^1][..^4] + destination;
        File.WriteAllLines(log, lines);

        foreach (var force in new[] { false, true })
        {
            var result = fixture.RunAt(checkout.AddHours(1), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(result.Success, result.Error);
            Assert.Equal("merged_to_dev", ReasonFor(result.Output, lane));
            Assert.Equal(!force, Directory.Exists(lane));
            Assert.Equal(!force, fixture.WorktreeRegistered(lane));
        }
    }

    [Theory]
    [InlineData("origin/dev")]
    [InlineData("short-oid")]
    [InlineData("full-oid")]
    public void LocalBranchWithRevisionLikeNameStillAllocatesTree(string name)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/local-revision-name");
        var saved = fixture.Head(lane);
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.Git(lane, "update-ref", "refs/remotes/origin/dev", saved);
        var branch = name == "short-oid" ? saved[..7] : name == "full-oid" ? saved : name;
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", branch);
        CleanLanesFixture.GitAt(lane, allocated.AddMinutes(1), "checkout", "--detach", "HEAD");

        var recent = fixture.RunAt(allocated.AddSeconds(10799), "--force", "--lanes-only");

        Assert.True(recent.Success, recent.Error);
        Assert.Equal("recently_updated", ReasonFor(recent.Output, lane));
        Assert.True(Directory.Exists(lane));

        var elapsed = fixture.RunAt(allocated.AddHours(3), "--force", "--lanes-only");

        Assert.True(elapsed.Success, elapsed.Error);
        Assert.Equal("merged_to_dev", ReasonFor(elapsed.Output, lane));
        Assert.False(Directory.Exists(lane));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LostSurvivingLocalBranchEvidenceRetainsTree(bool orphanedLog)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/lost-local-evidence");
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        var branch = "origin/dev";
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", branch);
        var log = fixture.BranchLogPath(lane);
        CleanLanesFixture.GitAt(lane, allocated.AddMinutes(1), "checkout", "--detach", "HEAD");
        CleanLanesFixture.Git(lane, "update-ref", "refs/remotes/origin/dev", fixture.Head(lane));
        if (orphanedLog)
            File.Delete(Path.Combine(fixture.RepositoryRoot, ".git", "refs", "heads", branch));
        else
            File.Delete(log);

        foreach (var force in new[] { false, true })
        {
            var result = fixture.RunAt(allocated.AddDays(2), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(result.Success, result.Error);
            Assert.Equal("update_unknown", ReasonFor(result.Output, lane));
            AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_detail",
                !orphanedLog ? "branch_reflog_missing" : "branch_reflog_unreadable");
            Assert.True(Directory.Exists(lane));
            Assert.True(fixture.WorktreeRegistered(lane));
        }
    }

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

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CheckoutOfExistingBranchDoesNotAllocateTree(bool explicitAllocation)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/existing-branch-origin");
        var old = fixture.LastUpdate(lane);
        var checkout = old.AddDays(2);
        if (explicitAllocation)
            CleanLanesFixture.GitAt(lane, old, "update-ref", "-m",
                "worktree-allocation:0123456789abcdef0123456789abcdef", "HEAD", fixture.Head(lane), fixture.Head(lane));
        CleanLanesFixture.GitAt(lane, checkout.AddMinutes(-1), "branch", "harness/existing-branch-destination");
        CleanLanesFixture.GitAt(lane, checkout, "switch", "harness/existing-branch-destination");

        var result = fixture.RunAt(checkout.AddHours(1), "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal("merged_to_dev", ReasonFor(result.Output, lane));
        Assert.False(Directory.Exists(lane));
    }
}
