using System.Text.Json;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InterruptedRemovalBypassesFreshAllocationAndBehindSelectors(bool landed)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/interrupted-removal";
        var lane = fixture.AddInterruptedRemoval(branch, landed);
        var head = fixture.Head(lane);
        var now = fixture.LastUpdate(lane).AddHours(1);
        var record = File.ReadAllBytes(Path.Combine(fixture.WorktreeGitDirectory(lane), "worktree-removal"));
        Assert.Contains("?? cache/output", CleanLanesFixture.Git(lane, "status", "--porcelain", "--untracked-files=all"));

        var preview = fixture.RunAt(now, "--lanes-only");

        Assert.True(preview.Success, preview.Error);
        Assert.Contains(ReadItems(preview.Output), item => ItemMatches(item, lane, "would_remove", "interrupted_removal"));
        Assert.Equal(record, File.ReadAllBytes(Path.Combine(fixture.WorktreeGitDirectory(lane), "worktree-removal")));
        Assert.True(fixture.WorktreeRegistered(lane));

        var removed = fixture.RunAt(now, "--force");

        Assert.True(removed.Success, removed.Error);
        var item = Assert.Single(ReadItems(removed.Output), row => row.GetProperty("path").GetString() == lane);
        Assert.Equal("removed", item.GetProperty("action").GetString());
        Assert.Equal("interrupted_removal", item.GetProperty("reason").GetString());
        Assert.Equal("interrupted_removal", item.GetProperty("selection_reason").GetString());
        Assert.Equal("refs/heads/" + branch, item.GetProperty("recovery_branch").GetString());
        Assert.False(Directory.Exists(lane));
        Assert.False(fixture.WorktreeRegistered(lane));
        Assert.Equal(head, CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "rev-parse", branch).Trim());
        Assert.Equal("cache/\n", CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "show", branch + ":.gitignore"));
    }

    [Theory]
    [InlineData("head")]
    [InlineData("recovery")]
    [InlineData("modified")]
    [InlineData("untracked")]
    [InlineData("staged")]
    [InlineData("malformed")]
    [InlineData("MERGE_HEAD")]
    [InlineData("CHERRY_PICK_HEAD")]
    [InlineData("REVERT_HEAD")]
    [InlineData("rebase-merge")]
    [InlineData("rebase-apply")]
    [InlineData("sequencer")]
    public void InterruptedRemovalRejectsLaterWorkAndUnfinishedOperations(string change)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/interrupted-changed";
        var lane = fixture.AddInterruptedRemoval(branch);
        var metadata = fixture.WorktreeGitDirectory(lane);
        if (change == "head")
            CleanLanesFixture.Git(lane, "commit", "--allow-empty", "-m", "later head");
        else if (change == "recovery")
        {
            CleanLanesFixture.Git(lane, "branch", "recovery-moved", "HEAD^");
            fixture.WriteRemovalRecord(lane, "refs/heads/recovery-moved");
        }
        else if (change == "modified") File.WriteAllText(Path.Combine(lane, "CLAUDE.md"), "later tracked work\n");
        else if (change == "untracked") File.WriteAllText(Path.Combine(lane, "later.txt"), "later ordinary work\n");
        else if (change == "staged") CleanLanesFixture.Git(lane, "add", "-u");
        else if (change == "malformed") File.WriteAllText(Path.Combine(metadata, "worktree-removal"), "{");
        else if (change.EndsWith("HEAD", StringComparison.Ordinal)) File.WriteAllText(Path.Combine(metadata, change), fixture.Head(lane) + "\n");
        else Directory.CreateDirectory(Path.Combine(metadata, change));
        var status = CleanLanesFixture.Git(lane, "status", "--porcelain");
        var record = File.ReadAllBytes(Path.Combine(metadata, "worktree-removal"));
        var now = fixture.LastUpdate(lane).AddHours(1);

        foreach (var arguments in new[] { new[] { "--lanes-only" }, new[] { "--force", "--lanes-only" } })
        {
            var result = fixture.RunAt(now, arguments);

            Assert.True(result.Success, result.Error);
            var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == lane);
            Assert.Equal("skipped", item.GetProperty("action").GetString());
            Assert.Equal("recently_updated", item.GetProperty("reason").GetString());
            Assert.Equal("original_selectors", item.GetProperty("selection_reason").GetString());
            Assert.True(fixture.WorktreeRegistered(lane));
            Assert.Equal(status, CleanLanesFixture.Git(lane, "status", "--porcelain"));
            Assert.Equal(record, File.ReadAllBytes(Path.Combine(metadata, "worktree-removal")));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void InterruptedRemovalRechecksWritesAfterSelection(bool atRemovalEntry)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddInterruptedRemoval("harness/interrupted-late-write");
        var injected = false;
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            var trigger = atRemovalEntry
                ? file == "python3" && IsProtocol(args, "remove") && !args.Contains("--preview")
                : IsLaneGit(file, args, directory, lane, "rev-parse", "--verify", "HEAD^{commit}");
            if (trigger && !injected)
            {
                injected = true;
                File.WriteAllText(Path.Combine(lane, "later.txt"), "later ordinary work\n");
            }
            return null;
        });

        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");

        Assert.True(result.Success, result.Error);
        Assert.Equal(atRemovalEntry ? 1 : 0, ReadSummary(result.Output).GetProperty("failed_count").GetInt32());
        Assert.True(injected);
        Assert.Equal(atRemovalEntry ? "checkpoint_failed:interrupted_removal_tree_changed" : "race_changed", ReasonFor(result.Output, lane));
        Assert.True(fixture.WorktreeRegistered(lane));
        Assert.Equal("later ordinary work\n", File.ReadAllText(Path.Combine(lane, "later.txt")));
    }

    private sealed partial class CleanLanesFixture
    {
        internal string AddInterruptedRemoval(string branch, bool landed = true)
        {
            var lane = AddMergedLane(branch);
            File.WriteAllText(Path.Combine(lane, ".gitignore"), "cache/\n");
            Git(lane, "add", ".gitignore");
            Git(lane, "commit", "-m", "snapshot ignore rules");
            if (landed) Git(RepositoryWorkingDirectory, "merge", "--ff-only", branch);
            WriteRemovalRecord(lane, "refs/heads/" + branch);
            File.Delete(Path.Combine(lane, "README.md"));
            File.Delete(Path.Combine(lane, ".gitignore"));
            Directory.CreateDirectory(Path.Combine(lane, "cache"));
            File.WriteAllText(Path.Combine(lane, "cache/output"), "rebuildable\n");
            return lane;
        }

        internal void WriteRemovalRecord(string lane, string recovery) => File.WriteAllText(
            Path.Combine(WorktreeGitDirectory(lane), "worktree-removal"),
            JsonSerializer.Serialize(new { commit = Head(lane), recovery_branch = recovery,
                predecessors = Array.Empty<object>(), native_locks = Array.Empty<object>() }));
    }
}
