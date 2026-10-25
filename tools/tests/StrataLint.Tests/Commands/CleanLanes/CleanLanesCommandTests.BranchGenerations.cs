namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    public static IEnumerable<object[]> ReusedAllocationHistories()
    {
        foreach (var branch in new[] { "origin/dev", "deadbeef", "harness/reused-allocation" })
        foreach (var rename in new[] { false, true })
        foreach (var dirty in new[] { false, true })
        foreach (var delayed in new[] { false, true })
        foreach (var force in new[] { false, true })
            yield return [branch, rename, dirty, delayed, force];
    }

    [Theory]
    [MemberData(nameof(ReusedAllocationHistories))]
    public void NativeBranchNameReusePreservesCheckoutGrace(
        string branch, bool rename, bool dirty, bool delayed, bool force)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/reused-allocation-origin");
        var saved = fixture.Head(lane);
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        var grace = dirty ? 86400 : 10800;
        CleanLanesFixture.Git(lane, "update-ref", "refs/remotes/origin/dev", saved);
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", branch);
        var log = fixture.BranchLogPath(lane);
        if (rename)
            CleanLanesFixture.GitAt(lane, allocated.AddSeconds(30), "branch", "-m", "harness/renamed-generation");
        CleanLanesFixture.GitAt(lane, allocated.AddMinutes(1), "checkout", "--detach", "HEAD");
        if (!rename) CleanLanesFixture.GitAt(lane, allocated.AddSeconds(90), "branch", "-d", branch);
        Assert.False(File.Exists(log));
        var recreated = allocated.AddSeconds(delayed ? grace + 60 : 120);
        CleanLanesFixture.GitAt(lane, recreated, "branch", "--create-reflog", branch, "HEAD");
        Assert.StartsWith(new string('0', saved.Length) + " " + saved, File.ReadLines(log).First(), StringComparison.Ordinal);
        Assert.Equal(string.Empty, CleanLanesFixture.Git(lane, "branch", "--show-current").Trim());
        if (dirty)
        {
            File.WriteAllText(Path.Combine(lane, "ordinary.txt"), "recoverable bytes\n");
            fixture.AdvanceBase(300);
        }

        if (!delayed)
        {
            var recent = fixture.RunAt(allocated.AddSeconds(grace - 1), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

            Assert.True(recent.Success, recent.Error);
            Assert.Equal("recently_updated", ReasonFor(recent.Output, lane));
            Assert.True(Directory.Exists(lane));
            Assert.True(fixture.WorktreeRegistered(lane));
            Assert.Equal(saved, fixture.Head(lane));
            if (dirty) Assert.Equal("recoverable bytes\n", File.ReadAllText(Path.Combine(lane, "ordinary.txt")));
        }

        var elapsed = fixture.RunAt(delayed ? recreated.AddMinutes(1) : allocated.AddSeconds(grace),
            force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

        Assert.True(elapsed.Success, elapsed.Error);
        Assert.Equal(dirty ? "stale_behind" : "merged_to_dev", ReasonFor(elapsed.Output, lane));
        Assert.Equal(!force, Directory.Exists(lane));
        Assert.Equal(!force, fixture.WorktreeRegistered(lane));
        if (dirty && force)
        {
            var recovery = ReadItems(elapsed.Output).Single(item => item.GetProperty("path").GetString() == lane)
                .GetProperty("recovery_branch").GetString()!;
            Assert.Equal("recoverable bytes\n", CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory,
                "show", recovery + ":ordinary.txt"));
        }
    }

    [Theory]
    [InlineData("create", false)]
    [InlineData("create", true)]
    [InlineData("rename", false)]
    [InlineData("rename", true)]
    [InlineData("copy", false)]
    [InlineData("copy", true)]
    public void ExistingCheckoutOfReplacementDoesNotEraseOrRenewEarlierGrace(string replacement, bool force)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/replacement-checkout-origin");
        var allocated = fixture.LastUpdate(lane).AddDays(2);
        if (replacement != "create")
            CleanLanesFixture.GitAt(lane, allocated.AddMinutes(-1), "branch", "harness/replacement-generation");
        CleanLanesFixture.GitAt(lane, allocated, "switch", "-c", "origin/dev");
        CleanLanesFixture.GitAt(lane, allocated.AddMinutes(1), "checkout", "--detach", "HEAD");
        CleanLanesFixture.GitAt(lane, allocated.AddSeconds(90), "branch", "-d", "origin/dev");
        if (replacement != "create")
            CleanLanesFixture.GitAt(lane, allocated.AddMinutes(2), "branch", replacement == "rename" ? "-m" : "-c",
                "harness/replacement-generation", "origin/dev");
        else
            CleanLanesFixture.GitAt(lane, allocated.AddMinutes(2), "branch", "origin/dev");
        CleanLanesFixture.GitAt(lane, allocated.AddHours(1), "switch", "origin/dev");
        CleanLanesFixture.GitAt(lane, allocated.AddHours(1).AddMinutes(1), "checkout", "--detach", "HEAD");

        var recent = fixture.RunAt(allocated.AddSeconds(10799), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

        Assert.True(recent.Success, recent.Error);
        Assert.Equal("recently_updated", ReasonFor(recent.Output, lane));
        Assert.True(Directory.Exists(lane));
        Assert.True(fixture.WorktreeRegistered(lane));

        var elapsed = fixture.RunAt(allocated.AddHours(3), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

        Assert.True(elapsed.Success, elapsed.Error);
        Assert.Equal("merged_to_dev", ReasonFor(elapsed.Output, lane));
        Assert.Equal(!force, Directory.Exists(lane));
        Assert.Equal(!force, fixture.WorktreeRegistered(lane));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SameSecondCreationAtDifferentCommitIsAmbiguous(bool force)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddWorkedLane("harness/same-second-origin");
        var saved = fixture.Head(lane);
        var parent = CleanLanesFixture.Git(lane, "rev-parse", "HEAD^").Trim();
        var checkout = fixture.LastUpdate(lane).AddDays(2);
        const string branch = "harness/same-second-destination";
        CleanLanesFixture.GitAt(lane, checkout, "branch", branch, parent);
        CleanLanesFixture.GitAt(lane, checkout, "branch", "-f", branch, saved);
        CleanLanesFixture.GitAt(lane, checkout, "switch", branch);
        CleanLanesFixture.GitAt(lane, checkout.AddMinutes(1), "checkout", "--detach", "HEAD");

        var recent = fixture.RunAt(checkout.AddSeconds(10799), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

        Assert.True(recent.Success, recent.Error);
        Assert.Equal("recently_updated", ReasonFor(recent.Output, lane));
        Assert.True(Directory.Exists(lane));
        Assert.True(fixture.WorktreeRegistered(lane));

        var elapsed = fixture.RunAt(checkout.AddHours(3), force ? ["--force", "--lanes-only"] : ["--lanes-only"]);

        Assert.True(elapsed.Success, elapsed.Error);
        Assert.Equal("merged_to_dev", ReasonFor(elapsed.Output, lane));
        Assert.Equal(!force, Directory.Exists(lane));
        Assert.Equal(!force, fixture.WorktreeRegistered(lane));
    }
}
