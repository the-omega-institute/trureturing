using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Runtime;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(1, false)]
    [InlineData(2, false)]
    [InlineData(3, false)]
    [InlineData(1, true)]
    [InlineData(2, true)]
    [InlineData(3, true)]
    public void CurrentHostActivityOrUnknownEvidenceRetainsAtEveryRefresh(int boundary, bool unknown)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/activity-refresh");
        fixture.LockLane(lane, InitializationLock);
        var reads = 0;
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file != "python3" || args.LastOrDefault() != "active-paths") return null;
            if (++reads < boundary) return new ProcessOutput(0, Encoding.UTF8.GetBytes("[]"), []);
            return unknown ? GitFailure("activity unavailable")
                : new ProcessOutput(0, Encoding.UTF8.GetBytes(JsonSerializer.Serialize(new[] { lane })), []);
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal(unknown ? "locked_activity_unknown" : "locked_activity", ReasonFor(result.Output, lane));
        Assert.Equal(boundary, reads);
        Assert.Equal(InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.Take(2).SequenceEqual(["worktree", "remove"]));
    }

    [Theory]
    [InlineData("identity", "identity_changed")]
    [InlineData("content", "content_changed")]
    [InlineData("staged", "evidence_changed")]
    [InlineData("history", "history_changed")]
    [InlineData("nested", "nested_worktree")]
    [InlineData("manual-lock", "locked_changed")]
    [InlineData("inventory-failure", "unreadable")]
    public void PostUnlockObservedDriftRefusesRemoval(string change, string reason)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/post-unlock-refresh");
        fixture.LockLane(lane, InitializationLock);
        var inventories = 0;
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file != "git" || !args.SequenceEqual(["worktree", "list", "--porcelain", "-z"])
                || ++inventories != 3) return null;
            switch (change)
            {
                case "identity":
                    CleanLanesFixture.Git(lane, "switch", "-c", "scratch/replacement");
                    File.WriteAllText(Path.Combine(lane, "new.txt"), "resumed session\n");
                    break;
                case "content":
                    File.WriteAllText(Path.Combine(lane, "new.txt"), "new content\n");
                    break;
                case "staged":
                    File.AppendAllText(Path.Combine(lane, "README.md"), "new staging\n");
                    CleanLanesFixture.Git(lane, "add", "README.md");
                    CleanLanesFixture.Git(lane, "restore", "--source=HEAD", "--worktree", "README.md");
                    break;
                case "history":
                    var log = Path.Combine(fixture.WorktreeGitDirectory(lane), "logs", "HEAD");
                    File.AppendAllText(log, File.ReadLines(log).Last() + "\n");
                    break;
                case "nested":
                    fixture.AddNestedWorktree(lane);
                    break;
                case "manual-lock":
                    fixture.LockLane(lane, "intentional resumed session");
                    break;
                case "inventory-failure": return GitFailure("post-unlock inventory unavailable");
            }
            return null;
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal(reason, ReasonFor(result.Output, lane));
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.Take(2).SequenceEqual(["worktree", "remove"]));
        Assert.Equal(change == "manual-lock" ? "intentional resumed session" : InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LockedRemovalFailureReportsPartialAndRestoresRetentionWhenPossible(bool relockFails)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/locked-remove-failure");
        fixture.LockLane(lane, InitializationLock);
        var runner = fixture.CreateRunner((file, args, _) =>
            file == "git" && (args.Take(2).SequenceEqual(["worktree", "remove"])
                || (relockFails && args.Take(2).SequenceEqual(["worktree", "lock"])))
                ? GitFailure("removal or relock failed") : null);
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.False(result.Success);
        Assert.True(Directory.Exists(lane));
        Assert.Equal(relockFails ? "worktree_relock_failed_state_indeterminate"
            : "worktree_remove_failed_state_indeterminate", ReasonFor(result.Output, lane));
        Assert.Equal(1, ReadSummary(result.Output).GetProperty("partial_count").GetInt32());
        if (!relockFails)
            Assert.Equal(InitializationLock,
                File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void UnlockFailureRetainsInitializationProtectionIncludingAfterSideEffects(bool afterSideEffect)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/unlock-failure");
        fixture.LockLane(lane, InitializationLock);
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((file, args, cwd) =>
        {
            if (file != "git" || !args.Take(2).SequenceEqual(["worktree", "unlock"])) return null;
            if (afterSideEffect)
                Assert.Equal(0, production.Run(file, args, cwd, TestBudgets.ScriptProcessHangGuard).ExitCode);
            return GitFailure("unlock failed");
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.Equal("unlock_failed", ReasonFor(result.Output, lane));
        Assert.Equal(InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
    }
}
