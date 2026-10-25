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
    [InlineData("harness/retired-allocation", false)]
    [InlineData("harness/retired-allocation", true)]
    public void NativeBranchRetirementPreservesBoundedAllocationGrace(string name, bool rename)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/retired-allocation-origin");
        var saved = fixture.Head(lane);
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        CleanLanesFixture.Git(lane, "update-ref", "refs/remotes/origin/dev", saved);
        var branch = name == "short-oid" ? saved[..7] : name == "full-oid" ? saved : name;
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
