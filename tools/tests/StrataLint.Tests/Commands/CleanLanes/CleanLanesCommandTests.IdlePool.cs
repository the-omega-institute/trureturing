using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false, "revalidate")]
    [InlineData(true, "revalidate")]
    [InlineData(false, "refused")]
    [InlineData(true, "refused")]
    [InlineData(false, "checkpoint_failed")]
    [InlineData(true, "checkpoint_failed")]
    [InlineData(false, "partial_or_indeterminate")]
    [InlineData(true, "partial_or_indeterminate")]
    public void IdlePoolProductionSweepContinuesAfterCandidateFailure(bool force, string failure)
    {
        using var fixture = new CleanLanesFixture();
        var older = AddIdleSweepCandidate(fixture, 'a', 1000000000);
        var newer = AddIdleSweepCandidate(fixture, 'b', 1000000001);
        var injection = "pool = sys.modules['worktree_pool']\n"
            + "pool.available_fraction = lambda source: 0.04\n"
            + "native_remove, native_state = pool.remove, pool.idle_state\n"
            + "validations = 0\n"
            + "def fault_state(source, path, *args):\n"
            + "    global validations\n"
            + "    if str(path) == " + JsonSerializer.Serialize(older) + ":\n"
            + "        validations += 1\n"
            + (failure == "revalidate"
                ? "        if validations == 2: raise pool.Refused('idle_identity_changed')\n" : string.Empty)
            + "    return native_state(source, path, *args)\n"
            + "def fault_remove(options):\n"
            + "    if str(options.path[0]) == " + JsonSerializer.Serialize(older) + ":\n"
            + "        return dict(status='failed', items=[dict(path=str(options.path[0]), outcome="
            + JsonSerializer.Serialize(failure == "revalidate" ? "refused" : failure)
            + ", reason='candidate_failure', error='candidate failure detail')])\n"
            + "    return native_remove(options)\n"
            + "pool.remove, pool.idle_state = fault_remove, fault_state\n";

        var result = fixture.RunWithRaw(InjectIdlePoolProgram(fixture, injection), force ? ["--force"] : []);

        Assert.True(result.Success, result.Output + result.Error);
        AssertQualificationPublicExit(result, force, 0);
        var items = ReadItems(result.Output);
        Assert.Contains(items, row => ItemMatches(row, newer, force ? "removed" : "would_remove", "idle_disk_pressure"));
        Assert.True(Directory.Exists(older));
        Assert.Equal(!force, Directory.Exists(newer));
        var warning = Assert.Single(ReadEvents(result.Error, "clean_lanes_warning"));
        Assert.Equal(older, warning.GetProperty("path").GetString());
        Assert.Equal(failure switch
        {
            "revalidate" => "idle_identity_changed",
            "refused" => "candidate_failure",
            _ => failure + ":candidate failure detail",
        }, warning.GetProperty("reason").GetString());
        Assert.Contains(failure == "revalidate" ? "idle_identity_changed" : "candidate failure detail",
            warning.GetProperty("diagnostic").GetString());
        Assert.Equal("succeeded", ReadSummary(result.Output).GetProperty("status").GetString());
        Assert.Equal("completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IdlePoolProductionInventoryFailureRemainsGlobal(bool force)
    {
        using var fixture = new CleanLanesFixture();
        var path = AddIdleSweepCandidate(fixture, 'c', 1000000000);
        var judge = fixture.AddGitlessJudgeSnapshot("trureturing-pool-inventory-control");
        const string injection = "def fail_inventory(source):\n"
            + "    raise RuntimeError('pool inventory unavailable')\n"
            + "sys.modules['worktree_pool'].inventory = fail_inventory\n";

        var result = fixture.RunWithRaw(InjectIdlePoolProgram(fixture, injection), force ? ["--force"] : []);

        Assert.False(result.Success, result.Output + result.Error);
        AssertQualificationPublicExit(result, force, 2);
        var failure = Assert.Single(ReadItems(result.Output), row => row.GetProperty("action").GetString() == "failed");
        Assert.Equal("idle_pool", failure.GetProperty("kind").GetString());
        Assert.Equal(JsonValueKind.Null, failure.GetProperty("path").ValueKind);
        Assert.Contains("inventory:pool inventory unavailable", failure.GetProperty("reason").GetString());
        Assert.Equal("failed", ReadSummary(result.Output).GetProperty("status").GetString());
        Assert.Equal("deferred", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        Assert.True(Directory.Exists(path));
        Assert.True(Directory.Exists(judge));
    }

    private static string AddIdleSweepCandidate(CleanLanesFixture fixture, char token, long timestamp)
    {
        var branch = "lane/governance/idle-" + new string(token, 32);
        var path = fixture.AddMergedLane(branch);
        var log = Path.Combine(fixture.RepositoryRoot, ".git/logs/refs/heads", branch);
        var rows = File.ReadAllLines(log);
        var fields = rows[0].Split('\t')[0];
        fields = fields[..fields.LastIndexOf(' ')];
        fields = fields[..fields.LastIndexOf(' ')] + " " + timestamp + " +0000";
        rows[0] = fields + "\tworktree-idle:" + new string(token, 32);
        File.WriteAllLines(log, rows);
        return path;
    }

    private static IWorktreeProcessRunner InjectIdlePoolProgram(CleanLanesFixture fixture, string injection) =>
        fixture.CreateRunner((file, args, directory) =>
        {
            if (file != "python3" || !IsProtocol(args, "pool")) return null;
            File.WriteAllText(args[2], File.ReadAllText(args[2]).Replace("sys.exit(sys.modules['worktree_protocol'].main())",
                injection + "sys.exit(sys.modules['worktree_protocol'].main())", StringComparison.Ordinal));
            return TestProcessRunner.Run(file, args, directory, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        });

    [Theory]
    [InlineData(false, "revalidate", "idle_identity_changed")]
    [InlineData(true, "remove", "locked_recent")]
    public void IdlePoolSelectedRefusalPreservesCauseAndContinues(bool force, string stage, string reason)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "lane/governance/idle-selected";
        var path = fixture.AddMergedLane(branch);
        var payload = JsonSerializer.Serialize(new
        {
            @event = "worktree_pool", status = "failed", capacity = 4,
            items = new[] { new { path, branch = "refs/heads/" + branch, head = fixture.Head(path),
                outcome = "retained", reason, stage, error = reason, error_type = "Refused" } },
        });
        var runner = fixture.CreateRunner((file, args, _) => file == "python3" && IsProtocol(args, "pool")
            ? new ProcessOutput(74, Encoding.UTF8.GetBytes(payload), []) : null);

        var result = fixture.RunWithRaw(runner, force ? ["--force"] : []);

        Assert.True(result.Success, result.Error);
        AssertQualificationPublicExit(result, force, 0);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path);
        Assert.Equal("skipped", item.GetProperty("action").GetString());
        Assert.Equal(reason, item.GetProperty("reason").GetString());
        Assert.Contains(stage, item.GetProperty("diagnostic").GetString());
        Assert.Contains(reason, item.GetProperty("diagnostic").GetString());
        Assert.DoesNotContain(ReadItems(result.Output), row => row.GetProperty("reason").GetString() == "idle_pool_failed:");
        Assert.Equal(0, ReadSummary(result.Output).GetProperty("failed_count").GetInt32());
        Assert.Equal("completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
        Assert.True(Directory.Exists(path));
        Assert.True(fixture.BranchExists(branch));
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
            File.WriteAllText(pressured[2], File.ReadAllText(pressured[2]).Replace("sys.exit(sys.modules['worktree_protocol'].main())",
                "sys.modules['worktree_pool'].available_fraction = lambda source: 0.04\n"
                + "sys.exit(sys.modules['worktree_protocol'].main())", StringComparison.Ordinal));
            return TestProcessRunner.Run("python3", pressured,
                directory, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        });

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.True(poolObserved);
        Assert.True(result.Success, result.Output + result.Error);
        AssertQualificationPublicExit(result, force: true, 0);
        Assert.Equal(inject, Directory.Exists(path));
        if (inject)
        {
            Assert.Contains(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path
                && row.GetProperty("action").GetString() == "failed"
                && row.GetProperty("reason").GetString()!.Contains("initial task identity cause", StringComparison.Ordinal));
            Assert.DoesNotContain(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path
                && row.GetProperty("action").GetString() == "removed");
            Assert.Equal("completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
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
        Assert.Equal(!poolTimeout, result.Success);
        AssertQualificationPublicExit(result, force, poolTimeout ? 2 : 0);
        Assert.Equal(inject ? poolTimeout ? 2 : 1 : 0, ReadSummary(result.Output).GetProperty("failed_count").GetInt32());
        Assert.Equal(poolTimeout ? "deferred" : "completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
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
    }

    [Fact]
    public void IdlePoolTreeFailureKeepsCompletedEvictionsAndContinuesSweeps()
    {
        using var fixture = new CleanLanesFixture();
        const string removedBranch = "lane/governance/idle-removed";
        const string failedBranch = "lane/governance/idle-failed";
        var removedPath = fixture.AddMergedLane(removedBranch);
        var failedPath = fixture.AddMergedLane(failedBranch);
        var judge = fixture.AddGitlessJudgeSnapshot("trureturing-idle-failure-control");
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

        Assert.True(result.Success, result.Error);
        var items = ReadItems(result.Output);
        var removed = Assert.Single(items, row => row.GetProperty("path").GetString() == removedPath);
        Assert.Equal("removed", removed.GetProperty("action").GetString());
        Assert.Equal("refs/heads/" + removedBranch, removed.GetProperty("recovery_branch").GetString());
        var failed = Assert.Single(items, row => row.GetProperty("path").GetString() == failedPath);
        Assert.Equal("failed", failed.GetProperty("action").GetString());
        Assert.Contains("revalidate", failed.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Contains("git fetch timed out", failed.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.False(Directory.Exists(judge));
        Assert.Contains(items, row => ItemMatches(row, judge, "removed", "gitless_judge_snapshot"));
        var summary = ReadSummary(result.Output);
        Assert.Equal(2, summary.GetProperty("removed_count").GetInt32());
        Assert.Equal(1, summary.GetProperty("failed_count").GetInt32());
        Assert.Equal("completed", summary.GetProperty("extra_sweeps").GetString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IdlePoolUnresolvedAggregateIsFailedRatherThanSkipped(bool hasReceipt)
    {
        using var fixture = new CleanLanesFixture();
        var path = fixture.AddMergedLane("lane/governance/idle-unresolved");
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
    }

    [Theory]
    [InlineData("qualification_failed", "failed")]
    [InlineData("checkpoint_failed", "failed")]
    [InlineData("partial_or_indeterminate", "partially_removed")]
    public void IdlePoolFailurePreservesRecoveryAndContinuesSweeps(string outcome, string action)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "lane/governance/idle-fixture";
        var path = fixture.AddMergedLane(branch);
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

        Assert.True(result.Success, result.Error);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path);
        Assert.Equal(action, item.GetProperty("action").GetString());
        Assert.Contains(outcome, item.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Contains("native failure detail", item.GetProperty("reason").GetString(), StringComparison.Ordinal);
        Assert.Equal(recovery, item.GetProperty("recovery_branch").GetString());
        Assert.Equal(candidate, item.GetProperty("recovery_branch_candidate").GetString());
        var summary = ReadSummary(result.Output);
        Assert.Equal("completed", summary.GetProperty("extra_sweeps").GetString());
        Assert.Equal(1, summary.GetProperty(action == "failed" ? "failed_count" : "partial_count").GetInt32());
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

        Assert.True(result.Success, result.Error);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == returnedPath);
        Assert.Equal("failed", item.GetProperty("action").GetString());
        Assert.Equal("checkpoint_failed:checkpoint blocker", item.GetProperty("reason").GetString());
        Assert.Equal("completed", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IdlePoolCarriesNativeLockEvidence(bool checkpointFailed)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "lane/governance/idle-evidence";
        var path = fixture.AddMergedLane(branch);
        var locks = new[] { new { path = path + "/index.lock", size = 9, age_seconds = 0.0,
            action = "native_lock_cleared" } };
        var payload = JsonSerializer.Serialize(new
        {
            @event = "worktree_pool", status = checkpointFailed ? "failed" : "succeeded", capacity = 4,
            items = new[] { new { path, branch = "refs/heads/" + branch, head = fixture.Head(path),
                outcome = checkpointFailed ? "checkpoint_failed" : "removed", reason = "idle_disk_pressure",
                error = checkpointFailed ? "checkpoint retry failed" : null,
                checkpoint = checkpointFailed ? null : new { native_locks = locks },
                native_locks = checkpointFailed ? locks : null } },
        });
        var runner = fixture.CreateRunner((file, args, _) => file == "python3" && args.Contains("pool")
            ? new ProcessOutput(checkpointFailed ? 74 : 0, Encoding.UTF8.GetBytes(payload), []) : null);

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.True(result.Success, result.Error);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == path);
        var evidence = Assert.Single(item.GetProperty("native_locks").EnumerateArray());
        Assert.Equal(path + "/index.lock", evidence.GetProperty("path").GetString());
        Assert.Equal(9, evidence.GetProperty("size").GetInt32());
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
