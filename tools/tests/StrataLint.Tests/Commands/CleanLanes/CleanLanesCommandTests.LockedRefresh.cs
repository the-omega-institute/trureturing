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
    [InlineData("branch-history", "history_changed")]
    [InlineData("private-recovery", "history_changed")]
    [InlineData("nested", "nested_worktree")]
    [InlineData("manual-lock", "locked_changed")]
    [InlineData("inventory-failure", "unreadable")]
    [InlineData("relocation", "locked_changed")]
    public void FinalLockedObservationDriftRefusesRemoval(string change, string reason)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/final-locked-refresh");
        fixture.LockLane(lane, InitializationLock);
        var moved = lane + "-moved";
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
                case "branch-history":
                    var branchLog = CleanLanesFixture.Git(lane, "rev-parse", "--path-format=absolute",
                        "--git-path", "logs/refs/heads/harness/final-locked-refresh").Trim();
                    File.AppendAllText(branchLog, File.ReadLines(branchLog).Last() + "\n");
                    break;
                case "private-recovery":
                    File.WriteAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "ORIG_HEAD"),
                        fixture.Head(lane) + "\n");
                    break;
                case "nested":
                    fixture.AddNestedWorktree(lane);
                    break;
                case "manual-lock":
                    CleanLanesFixture.Git(lane, "worktree", "unlock", lane);
                    fixture.LockLane(lane, "intentional resumed session");
                    break;
                case "relocation":
                    CleanLanesFixture.Git(lane, "worktree", "move", "--force", "--force", lane, moved);
                    break;
                case "inventory-failure": return GitFailure("final locked inventory unavailable");
            }
            return null;
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        var retained = change == "relocation" ? moved : lane;
        Assert.True(Directory.Exists(retained));
        Assert.Equal(reason, ReasonFor(result.Output, lane));
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.Take(2).SequenceEqual(["worktree", "remove"]));
        Assert.Equal(change == "manual-lock" ? "intentional resumed session" : InitializationLock,
            File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(retained), "locked")).Trim());
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.Take(2).SequenceEqual(["worktree", "unlock"]));
    }

    [Theory]
    [InlineData("before-native")]
    [InlineData("native-refusal")]
    [InlineData("after-native")]
    public void LockedNativeRemovalFailureReportsPartialWithoutUnlocking(string boundary)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/locked-remove-failure");
        fixture.LockLane(lane, InitializationLock);
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((file, args, cwd) =>
        {
            if (file != "git" || !args.Take(2).SequenceEqual(["worktree", "remove"])) return null;
            Assert.Equal(new[] { "worktree", "remove", "--force", "--force", "--", lane }, args);
            Assert.Equal(InitializationLock,
                File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
            if (boundary == "native-refusal")
            {
                var refused = production.Run(file, ["worktree", "remove", "--force", "--", lane],
                    cwd, TestBudgets.ScriptProcessHangGuard);
                Assert.NotEqual(0, refused.ExitCode);
                return refused;
            }
            if (boundary == "after-native")
                Assert.Equal(0, production.Run(file, args, cwd, TestBudgets.ScriptProcessHangGuard).ExitCode);
            return GitFailure("returned removal failure");
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.False(result.Success);
        Assert.Equal(boundary != "after-native", Directory.Exists(lane));
        Assert.Equal("worktree_remove_failed_state_indeterminate", ReasonFor(result.Output, lane));
        Assert.Equal(1, ReadSummary(result.Output).GetProperty("partial_count").GetInt32());
        Assert.True(fixture.BranchExists("harness/locked-remove-failure"));
        if (boundary != "after-native")
            Assert.Equal(InitializationLock,
                File.ReadAllText(Path.Combine(fixture.WorktreeGitDirectory(lane), "locked")).Trim());
        Assert.DoesNotContain(runner.Invocations, call => call.Arguments.Take(2).SequenceEqual(["worktree", "unlock"])
            || call.Arguments.Take(2).SequenceEqual(["worktree", "lock"]));
    }
}
