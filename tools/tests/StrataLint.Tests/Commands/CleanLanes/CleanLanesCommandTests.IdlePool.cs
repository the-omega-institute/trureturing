using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false, "revalidate", "idle_identity_changed")]
    [InlineData(true, "remove", "locked_recent")]
    public void IdlePoolSelectedRefusalPreservesCauseAndFailsPublicExit(bool force, string stage, string reason)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "lane/governance/idle-selected";
        const string orphan = "harness/retained-after-selected-refusal";
        var path = fixture.AddMergedLane(branch);
        fixture.AddOrphan(orphan, merged: true);
        var payload = JsonSerializer.Serialize(new
        {
            @event = "worktree_pool", status = "failed", capacity = 4,
            items = new[] { new { path, branch = "refs/heads/" + branch, head = fixture.Head(path),
                outcome = "retained", reason, stage, error = reason, error_type = "Refused" } },
        });
        var runner = fixture.CreateRunner((file, args, _) => file == "python3" && IsProtocol(args, "pool")
            ? new ProcessOutput(74, Encoding.UTF8.GetBytes(payload), []) : null);

        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);

        Assert.False(result.Success);
        AssertQualificationPublicExit(result, force, 2);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path);
        Assert.Equal("skipped", item.GetProperty("action").GetString());
        Assert.Equal(reason, item.GetProperty("reason").GetString());
        Assert.Contains(stage, item.GetProperty("diagnostic").GetString());
        Assert.Contains(reason, item.GetProperty("diagnostic").GetString());
        Assert.DoesNotContain(ReadItems(result.Output), row => row.GetProperty("reason").GetString() == "idle_pool_failed:");
        Assert.Equal(1, ReadSummary(result.Output).GetProperty("failed_count").GetInt32());
        Assert.Equal("deferred", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        Assert.True(Directory.Exists(path));
        Assert.True(fixture.BranchExists(orphan));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IdlePoolRetainsFailedTaskReturnedBeforeFreshInventory(bool inject)
    {
        using var fixture = new CleanLanesFixture();
        fixture.AddMergedLane("lane/governance/idle-trigger");
        var path = fixture.AddMergedLane("lane/governance/task-returning");
        var calls = 0;
        var poolObserved = false;
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            if (inject && IsLaneGit(file, args, directory, path, "rev-parse", "--absolute-git-dir") && ++calls == 1)
                return GitFailure("initial task identity cause");
            if (file != "python3" || !IsProtocol(args, "pool")) return null;
            poolObserved = true;
            var token = new string('b', 32);
            var branch = "lane/governance/idle-" + token;
            CleanLanesFixture.Git(path, "switch", "-c", branch);
            var log = Path.Combine(fixture.RepositoryRoot, ".git/logs/refs/heads", branch);
            var rows = File.ReadAllLines(log);
            rows[0] = rows[0].Split('\t')[0] + "\tworktree-idle:" + token;
            File.WriteAllLines(log, rows);
            var pressured = args.ToArray();
            pressured[2] = pressured[2].Replace("sys.exit(sys.modules['worktree_protocol'].main())",
                "sys.modules['worktree_pool'].available_fraction = lambda source: 0.04\n"
                + "sys.exit(sys.modules['worktree_protocol'].main())", StringComparison.Ordinal);
            return TestProcessRunner.Run("python3", pressured,
                directory, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        });

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.True(poolObserved);
        Assert.True(result.Success == !inject, result.Output + result.Error);
        AssertQualificationPublicExit(result, force: true, inject ? 2 : 0);
        Assert.Equal(inject, Directory.Exists(path));
        if (inject)
        {
            Assert.Contains(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path
                && row.GetProperty("action").GetString() == "failed"
                && row.GetProperty("reason").GetString()!.Contains("initial task identity cause", StringComparison.Ordinal));
            Assert.DoesNotContain(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path
                && row.GetProperty("action").GetString() == "removed");
            Assert.Equal("deferred", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        }
    }

    [Theory]
    [InlineData(false, false, false)]
    [InlineData(true, false, false)]
    [InlineData(true, true, false)]
    [InlineData(true, true, true)]
    public void IdleInitialIdentityFailureMustRemainFailed(bool inject, bool force, bool poolTimeout)
    {
        using var fixture = new CleanLanesFixture();
        var token = new string('a', 32);
        var branch = "lane/governance/idle-" + token;
        var path = fixture.AddMergedLane(branch);
        var log = Path.Combine(fixture.RepositoryRoot, ".git/logs/refs/heads", branch);
        var rows = File.ReadAllLines(log);
        rows[0] = rows[0].Split('\t')[0] + "\tworktree-idle:" + token;
        File.WriteAllLines(log, rows);
        var calls = 0;
        var poolObserved = false;
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            if (inject && IsLaneGit(file, args, directory, path, "rev-parse", "--absolute-git-dir") && ++calls == 1)
                return GitFailure("initial idle native identity cause");
            if (file == "python3" && IsProtocol(args, "pool"))
            {
                poolObserved = true;
                if (inject) Assert.DoesNotContain("--force", args);
                if (poolTimeout) throw new TimeoutException("later pool observation deadline");
            }
            return null;
        });
        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);
        Assert.True(poolObserved);
        Assert.Equal(!inject, result.Success);
        AssertQualificationPublicExit(result, force, inject ? 2 : 0);
        Assert.Equal(inject ? poolTimeout ? 2 : 1 : 0, ReadSummary(result.Output).GetProperty("failed_count").GetInt32());
        Assert.Equal(inject ? "deferred" : "completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        if (inject) Assert.Contains(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path
            && row.GetProperty("action").GetString() == "failed"
            && row.GetProperty("reason").GetString()!.Contains("initial idle native identity cause", StringComparison.Ordinal));
        else Assert.Contains(ReadItems(result.Output), row => ItemMatches(row, path, "skipped", "idle_pool"));
        Assert.True(Directory.Exists(path));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void BusyPoolBeforeEntryReportsOnlyPoolFailure(bool force)
    {
        using var fixture = new CleanLanesFixture();
        var path = fixture.AddMergedLane("lane/governance/idle-busy");
        fixture.AddOrphan("harness/retained-after-pool-contention", merged: true);
        var payload = JsonSerializer.Serialize(new
        {
            @event = "worktree_pool", status = "failed", capacity = 4,
            items = Array.Empty<object>(),
            failure = new { scope = "operation:idle-pool", stage = "pool_scope", outcome = "refused",
                error = "busy_scope:operation:idle-pool", error_type = "Refused" },
        });
        var runner = fixture.CreateRunner((file, args, _) => file == "python3" && args.Contains("pool")
            ? new ProcessOutput(74, Encoding.UTF8.GetBytes(payload), []) : null);

        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);

        Assert.False(result.Success);
        var items = ReadItems(result.Output);
        var failed = Assert.Single(items, row => row.GetProperty("action").GetString() == "failed");
        Assert.Equal("idle_pool", failed.GetProperty("kind").GetString());
        Assert.Equal(JsonValueKind.Null, failed.GetProperty("path").ValueKind);
        Assert.Equal(JsonValueKind.Null, failed.GetProperty("branch").ValueKind);
        Assert.Equal("pool_scope:busy_scope:operation:idle-pool", failed.GetProperty("reason").GetString());
        Assert.DoesNotContain(items, row => row.GetProperty("kind").GetString() == "idle_worktree");
        var summary = ReadSummary(result.Output);
        Assert.Equal(1, summary.GetProperty("failed_count").GetInt32());
        Assert.Equal(0, summary.GetProperty("removed_count").GetInt32());
        Assert.Equal("deferred", summary.GetProperty("extra_sweeps").GetString());
        Assert.True(Directory.Exists(path));
        Assert.True(fixture.BranchExists("harness/retained-after-pool-contention"));
    }

    [Fact]
    public void IdlePoolSweepFailureKeepsCompletedEvictionsAndDefersExtraSweeps()
    {
        using var fixture = new CleanLanesFixture();
        const string removedBranch = "lane/governance/idle-removed";
        const string failedBranch = "lane/governance/idle-failed";
        var removedPath = fixture.AddMergedLane(removedBranch);
        var failedPath = fixture.AddMergedLane(failedBranch);
        fixture.AddOrphan("harness/retained-after-sweep-failure", merged: true);
        var payload = JsonSerializer.Serialize(new
        {
            @event = "worktree_pool", status = "failed", capacity = 4,
            items = new[]
            {
                new { path = removedPath, branch = "refs/heads/" + removedBranch, head = fixture.Head(removedPath),
                    outcome = "removed", reason = "idle_disk_pressure", stage = (string?)null, error = (string?)null,
                    recovery_branch = (string?)("refs/heads/" + removedBranch) },
                new { path = failedPath, branch = "refs/heads/" + failedBranch, head = fixture.Head(failedPath),
                    outcome = "sweep_failed", reason = "idle_sweep_failed", stage = (string?)"revalidate",
                    error = (string?)"git fetch timed out", recovery_branch = (string?)null },
            },
        });
        var runner = fixture.CreateRunner((file, args, _) => file == "python3" && args.Contains("pool")
            ? new ProcessOutput(74, Encoding.UTF8.GetBytes(payload), []) : null);

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.False(result.Success);
        var items = ReadItems(result.Output);
        var removed = Assert.Single(items, row => row.GetProperty("path").GetString() == removedPath);
        Assert.Equal("removed", removed.GetProperty("action").GetString());
        Assert.Equal("refs/heads/" + removedBranch, removed.GetProperty("recovery_branch").GetString());
        var failed = Assert.Single(items, row => row.GetProperty("path").GetString() == failedPath);
        Assert.Equal("failed", failed.GetProperty("action").GetString());
        Assert.Contains("revalidate", failed.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Contains("git fetch timed out", failed.GetProperty("reason").GetString(), StringComparison.Ordinal);
        var summary = ReadSummary(result.Output);
        Assert.Equal(1, summary.GetProperty("removed_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("failed_count").GetInt32());
        Assert.Equal("deferred", summary.GetProperty("extra_sweeps").GetString());
        Assert.True(fixture.BranchExists("harness/retained-after-sweep-failure"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IdlePoolUnresolvedAggregateIsFailedRatherThanSkipped(bool hasReceipt)
    {
        using var fixture = new CleanLanesFixture();
        var path = fixture.AddMergedLane("lane/governance/idle-unresolved");
        fixture.AddOrphan("harness/retained-after-unresolved-pool", merged: true);
        var payload = hasReceipt ? JsonSerializer.Serialize(new
        {
            @event = "worktree_pool", status = "failed", capacity = 4,
            items = Array.Empty<object>(),
        }) : string.Empty;
        var runner = fixture.CreateRunner((file, args, _) => file == "python3" && args.Contains("pool")
            ? new ProcessOutput(74, Encoding.UTF8.GetBytes(payload), Encoding.UTF8.GetBytes("native failure")) : null);

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.False(result.Success);
        Assert.Contains(ReadItems(result.Output), row => row.GetProperty("action").GetString() == "failed");
        Assert.Equal("deferred", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        Assert.True(Directory.Exists(path));
        Assert.True(fixture.BranchExists("harness/retained-after-unresolved-pool"));
    }

    [Theory]
    [InlineData("qualification_failed", "failed")]
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
                outcome, reason = outcome == "qualification_failed" ? "qualification_failed:native failure detail" : "idle_disk_pressure", error = "native failure detail",
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
    public void IdlePoolReceiptIncludesTreeReturnedAfterInventory()
    {
        using var fixture = new CleanLanesFixture();
        fixture.AddMergedLane("lane/governance/idle-trigger");
        string? returnedPath = null;
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (file != "python3" || !args.Contains("pool")) return null;
            const string branch = "lane/governance/idle-late";
            returnedPath = fixture.AddMergedLane(branch);
            var payload = JsonSerializer.Serialize(new
            {
                @event = "worktree_pool", status = "failed", capacity = 4,
                items = new[] { new { path = returnedPath, branch = "refs/heads/" + branch,
                    head = fixture.Head(returnedPath), outcome = "checkpoint_failed",
                    reason = "idle_disk_pressure", error = "checkpoint blocker",
                    recovery_branch = "refs/heads/" + branch } },
            });
            return new ProcessOutput(74, Encoding.UTF8.GetBytes(payload), []);
        });

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.False(result.Success);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == returnedPath);
        Assert.Equal("failed", item.GetProperty("action").GetString());
        Assert.Equal("checkpoint_failed:checkpoint blocker", item.GetProperty("reason").GetString());
        Assert.Equal("deferred", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IdlePoolCarriesNativeLocksAndProtectsPredecessorRoots(bool checkpointFailed)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "lane/governance/idle-evidence";
        const string predecessor = "harness/pool-predecessor";
        const string control = "harness/pool-retirable-control";
        var path = fixture.AddMergedLane(branch);
        fixture.AddOrphan(predecessor, merged: true);
        fixture.AddOrphan(control, merged: true);
        var locks = new[] { new { path = path + "/index.lock", size = 9, age_seconds = 0.0,
            action = "native_lock_cleared" } };
        var payload = JsonSerializer.Serialize(new
        {
            @event = "worktree_pool", status = checkpointFailed ? "failed" : "succeeded", capacity = 4,
            items = new[] { new { path, branch = "refs/heads/" + branch, head = fixture.Head(path),
                outcome = checkpointFailed ? "checkpoint_failed" : "removed", reason = "idle_disk_pressure",
                error = checkpointFailed ? "checkpoint retry failed" : null,
                checkpoint = checkpointFailed ? null : new { native_locks = locks },
                native_locks = checkpointFailed ? locks : null,
                recovery_roots = new[] { "refs/heads/" + predecessor } } },
        });
        var runner = fixture.CreateRunner((file, args, _) => file == "python3" && args.Contains("pool")
            ? new ProcessOutput(checkpointFailed ? 74 : 0, Encoding.UTF8.GetBytes(payload), []) : null);

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.Equal(!checkpointFailed, result.Success);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path);
        var evidence = Assert.Single(item.GetProperty("native_locks").EnumerateArray());
        Assert.Equal(path + "/index.lock", evidence.GetProperty("path").GetString());
        Assert.Equal(9, evidence.GetProperty("size").GetInt32());
        Assert.True(fixture.BranchExists(predecessor));
        Assert.Equal(checkpointFailed, fixture.BranchExists(control));
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
