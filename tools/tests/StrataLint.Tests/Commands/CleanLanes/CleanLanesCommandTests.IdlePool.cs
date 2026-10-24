using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData("checkpoint_failed", "failed")]
    [InlineData("partial_or_indeterminate", "partially_removed")]
    public void IdlePoolFailurePreservesRecoveryAndDefersExtraSweeps(string outcome, string action)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "lane/governance/idle-fixture";
        var path = fixture.AddMergedLane(branch);
        fixture.AddOrphan("harness/retained-after-idle-failure", merged: true);
        const string recovery = "refs/heads/lane/governance/recovery-confirmed";
        const string candidate = "refs/heads/lane/governance/recovery-candidate";
        var payload = JsonSerializer.Serialize(new
        {
            @event = "worktree_pool", status = "failed", capacity = 4,
            items = new[] { new { path, branch = "refs/heads/" + branch, head = fixture.Head(path),
                outcome, reason = "idle_disk_pressure", error = "native failure detail",
                recovery_branch = recovery, recovery_branch_candidate = candidate } },
        });
        var runner = fixture.CreateRunner((file, args, _) => file == "python3" && args.Contains("pool")
            ? new ProcessOutput(74, Encoding.UTF8.GetBytes(payload), []) : null);

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.False(result.Success);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path);
        Assert.Equal(action, item.GetProperty("action").GetString());
        Assert.Contains(outcome, item.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Contains("native failure detail", item.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Equal(recovery, item.GetProperty("recovery_branch").GetString());
        Assert.Equal(candidate, item.GetProperty("recovery_branch_candidate").GetString());
        var summary = ReadSummary(result.Output);
        Assert.Equal("deferred", summary.GetProperty("extra_sweeps").GetString());
        Assert.Equal(1, summary.GetProperty(action == "failed" ? "failed_count" : "partial_count").GetInt32());
        Assert.True(fixture.BranchExists("harness/retained-after-idle-failure"));
    }

    [Fact]
    public void IdlePrefixedTaskKeepsOrdinaryAllocationProtection()
    {
        using var fixture = new CleanLanesFixture();
        var path = fixture.AddMergedLane("lane/governance/idle-analysis");
        var result = fixture.RunAt(fixture.CreationTime(path).AddHours(1), "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path);
        Assert.Equal("lane_worktree", item.GetProperty("kind").GetString());
        Assert.Equal("skipped", item.GetProperty("action").GetString());
        Assert.Equal("recently_updated", item.GetProperty("reason").GetString());
        Assert.True(Directory.Exists(path));
    }
}
