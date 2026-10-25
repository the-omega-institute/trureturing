namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData("origin/dev", false)]
    [InlineData("origin/dev", true)]
    [InlineData("short-oid", false)]
    [InlineData("short-oid", true)]
    [InlineData("full-oid", false)]
    [InlineData("full-oid", true)]
    [InlineData("sha256-length-hex", false)]
    [InlineData("sha256-length-hex", true)]
    [InlineData("refs/heads/retired-allocation", false)]
    [InlineData("refs/heads/retired-allocation", true)]
    [InlineData("harness/retired-allocation", false)]
    [InlineData("harness/retired-allocation", true)]
    public void NativeBranchRetirementPreservesApplicableAllocationGrace(string name, bool rename)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/retired-allocation-origin");
        var saved = fixture.Head(lane);
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.Git(lane, "update-ref", "refs/remotes/origin/dev", saved);
        Assert.Equal("sha1", CleanLanesFixture.Git(lane, "rev-parse", "--show-object-format").Trim());
        var branch = name == "short-oid" ? saved[..7] : name == "full-oid" ? saved
            : name == "sha256-length-hex" ? new string('a', 64) : name;
        Assert.Equal(branch, CleanLanesFixture.Git(lane, "check-ref-format", "--branch", branch).Trim());
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", branch);
        var log = fixture.BranchLogPath(lane);
        if (rename)
        {
            CleanLanesFixture.GitAt(lane, allocated.AddMinutes(1), "branch", "-m", "harness/renamed-allocation");
            var renamedLog = fixture.BranchLogPath(lane);
            Assert.True(File.Exists(renamedLog));
            Assert.StartsWith(new string('0', saved.Length) + " " + saved, File.ReadLines(renamedLog).First(), StringComparison.Ordinal);
        }
        CleanLanesFixture.GitAt(lane, allocated.AddMinutes(2), "checkout", "--detach", "HEAD");
        if (!rename) CleanLanesFixture.Git(lane, "branch", "-d", branch);
        Assert.False(File.Exists(log));
        Assert.DoesNotContain("refs/heads/" + branch,
            CleanLanesFixture.Git(lane, "for-each-ref", "--format=%(refname)").Split('\n'));
        if (name is "origin/dev" or "short-oid" or "full-oid")
            Assert.Equal(saved, CleanLanesFixture.Git(lane, "rev-parse", "--verify", branch + "^{commit}").Trim());

        foreach (var force in new[] { false, true })
        {
            var recent = fixture.RunAt(allocated.AddSeconds(10799), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(recent.Success, recent.Error);
            Assert.Equal("recently_updated", ReasonFor(recent.Output, lane));
            Assert.True(Directory.Exists(lane));
            Assert.True(fixture.WorktreeRegistered(lane));
            Assert.Equal(saved, fixture.Head(lane));
        }
        foreach (var force in new[] { false, true })
        {
            var elapsed = fixture.RunAt(allocated.AddHours(3), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(elapsed.Success, elapsed.Error);
            Assert.Equal("merged_to_dev", ReasonFor(elapsed.Output, lane));
            Assert.Equal(!force, Directory.Exists(lane));
            Assert.Equal(!force, fixture.WorktreeRegistered(lane));
        }
    }

    [Fact]
    public void ExpiredAmbiguousCheckoutCannotValidateLostBranchCreation()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/ambiguous-evidence-origin");
        var saved = fixture.Head(lane);
        var parent = CleanLanesFixture.Git(lane, "rev-parse", "HEAD^").Trim();
        var checkout = fixture.LastUpdate(lane).AddDays(2);
        const string surviving = "harness/ambiguous-evidence-survivor";
        CleanLanesFixture.GitAt(lane, checkout.AddMinutes(-1), "branch", surviving);
        CleanLanesFixture.GitAt(lane, checkout.AddSeconds(-1), "update-ref", "refs/heads/" + surviving, parent, saved);
        CleanLanesFixture.GitAt(lane, checkout.AddSeconds(-1), "update-ref", "refs/heads/" + surviving, saved, parent);
        var branchLog = Path.Combine(fixture.RepositoryRoot, ".git", "logs", "refs", "heads", surviving);
        File.WriteAllLines(branchLog, File.ReadAllLines(branchLog).TakeLast(1));
        Assert.Contains(File.ReadAllText(branchLog).Split(' ')[0], static c => c != '0');
        CleanLanesFixture.GitAt(lane, checkout, "switch", "-c", "origin/dev");
        var deletedLog = fixture.BranchLogPath(lane);
        CleanLanesFixture.GitAt(lane, checkout.AddMinutes(1), "checkout", "--detach", "HEAD");
        CleanLanesFixture.Git(lane, "branch", "-d", "origin/dev");
        Assert.False(File.Exists(deletedLog));
        CleanLanesFixture.GitAt(lane, checkout.AddMinutes(2), "switch", surviving);

        foreach (var force in new[] { false, true })
        {
            var result = fixture.RunAt(checkout.AddDays(2), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(result.Success, result.Error);
            Assert.Equal("update_unknown", ReasonFor(result.Output, lane));
            AssertItemProperty(ReadItems(result.Output), "path", lane, "selection_detail", "branch_allocation_unverifiable");
            Assert.True(Directory.Exists(lane));
            Assert.True(fixture.WorktreeRegistered(lane));
            Assert.Equal(saved, fixture.Head(lane));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AmbiguousCheckoutUsesOutstandingWorkGrace(bool nonLocalAlsoResolves)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/ambiguous-dirty-origin");
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        var branch = nonLocalAlsoResolves ? "origin/dev" : "harness/ambiguous-dirty-allocation";
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", branch);
        var log = fixture.BranchLogPath(lane);
        CleanLanesFixture.GitAt(lane, allocated.AddMinutes(1), "checkout", "--detach", "HEAD");
        CleanLanesFixture.Git(lane, "branch", "-d", branch);
        Assert.False(File.Exists(log));
        if (nonLocalAlsoResolves)
            CleanLanesFixture.Git(lane, "update-ref", "refs/remotes/origin/dev", fixture.Head(lane));
        File.WriteAllText(Path.Combine(lane, "ordinary.txt"), "recoverable bytes\n");
        fixture.AdvanceBase(300);

        foreach (var force in new[] { false, true })
        {
            var recent = fixture.RunAt(allocated.AddSeconds(86399), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(recent.Success, recent.Error);
            Assert.Equal("recently_updated", ReasonFor(recent.Output, lane));
            Assert.True(Directory.Exists(lane));
            Assert.Equal("recoverable bytes\n", File.ReadAllText(Path.Combine(lane, "ordinary.txt")));
        }
        foreach (var force in new[] { false, true })
        {
            var elapsed = fixture.RunAt(allocated.AddDays(1), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(elapsed.Success, elapsed.Error);
            Assert.Equal("stale_behind", ReasonFor(elapsed.Output, lane));
            Assert.Equal(!force, Directory.Exists(lane));
            Assert.Equal(!force, fixture.WorktreeRegistered(lane));
        }
    }
}
