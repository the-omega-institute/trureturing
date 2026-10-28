using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Runtime;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RemovalOuterTimeoutAfterNativeDeletionIsIndeterminate(bool settlementFailure)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/removal-outer-deadline";
        var lane = fixture.AddLandedLane(branch);
        fixture.AddOrphan("harness/retained-after-removal-deadline", merged: true);
        var deletionObserved = false;
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            if (file != "python3" || !IsProtocol(args, "remove") || args.Contains("--preview")) return null;
            var modified = args.ToArray();
            modified[2] = modified[2].Replace("sys.exit(sys.modules['worktree_protocol'].main())", """
                import threading
                p = sys.modules['worktree_preservation']
                native_git = p.git
                def delete_then_wait(root, *args, **kwargs):
                    result = native_git(root, *args, **kwargs)
                    if args[:2] == ('worktree', 'remove'):
                        print('native deletion completed', flush=True)
                        threading.Event().wait()
                    return result
                p.git = delete_then_wait
                sys.exit(sys.modules['worktree_protocol'].main())
                """, StringComparison.Ordinal);
            new ProductionWorktreeProcessRunner().RunStreaming<int>(file, modified, directory,
                TimeSpan.FromSeconds(600), async (stream, cancellation) =>
                {
                    using var reader = new StreamReader(stream, Encoding.UTF8);
                    deletionObserved = await reader.ReadLineAsync(cancellation) == "native deletion completed";
                    if (settlementFailure) throw new System.ComponentModel.Win32Exception("native settlement failed after deletion");
                    throw new TimeoutException("outer removal deadline after native deletion");
                });
            throw new InvalidOperationException("expected outer removal deadline");
        });

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.True(deletionObserved);
        Assert.False(Directory.Exists(lane));
        Assert.True(fixture.BranchExists(branch));
        Assert.False(result.Success);
        AssertQualificationPublicExit(result, true, 2);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == lane);
        Assert.Equal("partially_removed", item.GetProperty("action").GetString());
        Assert.Equal("worktree_remove_failed_state_indeterminate", item.GetProperty("reason").GetString());
        Assert.Contains(settlementFailure ? "Win32Exception:native settlement failed after deletion"
            : "TimeoutException:outer removal deadline after native deletion", item.GetProperty("diagnostic").GetString());
        var invocation = Assert.Single(runner.Invocations, call => IsProtocol(call.Arguments, "remove"));
        Assert.Equal(TimeSpan.FromSeconds(600), invocation.Timeout);
        var summary = ReadSummary(result.Output);
        Assert.Equal(1, summary.GetProperty("partial_count").GetInt32());
        Assert.Equal(0, summary.GetProperty("failed_count").GetInt32());
        Assert.Equal("deferred", summary.GetProperty("extra_sweeps").GetString());
        Assert.True(fixture.BranchExists("harness/retained-after-removal-deadline"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RemovalIncompleteReceiptPreservesAvailableRecovery(bool includeOutcome)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/removal-incomplete");
        const string recovery = "refs/heads/harness/recovery-confirmed";
        const string candidate = "refs/heads/harness/recovery-candidate";
        fixture.AddOrphan("harness/recovery-confirmed", merged: true);
        var row = new Dictionary<string, object>
        {
            ["path"] = lane, ["recovery_branch"] = recovery, ["recovery_branch_candidate"] = candidate,
            ["native_locks"] = new[] { new { path = lane + "/index.lock", action = "native_lock_cleared" } },
        };
        if (includeOutcome) row["outcome"] = "partial_or_indeterminate";
        var payload = JsonSerializer.Serialize(new { @event = "worktree_removal", items = new[] { row } });
        var runner = fixture.CreateRunner((file, args, _) => file == "python3" && IsProtocol(args, "remove")
            ? new ProcessOutput(74, Encoding.UTF8.GetBytes(payload), Encoding.UTF8.GetBytes("native deletion interrupted")) : null);

        var result = fixture.RunWithRaw(runner, "--force");

        Assert.False(result.Success);
        AssertQualificationPublicExit(result, true, 2);
        var item = Assert.Single(ReadItems(result.Output), row => row.GetProperty("path").GetString() == lane);
        Assert.Equal("partially_removed", item.GetProperty("action").GetString());
        Assert.Equal(recovery, item.GetProperty("recovery_branch").GetString());
        Assert.Equal(candidate, item.GetProperty("recovery_branch_candidate").GetString());
        Assert.Single(item.GetProperty("native_locks").EnumerateArray());
        Assert.Contains("native deletion interrupted", item.GetProperty("diagnostic").GetString());
        Assert.True(fixture.BranchExists("harness/recovery-confirmed"));
        Assert.Equal(1, ReadSummary(result.Output).GetProperty("partial_count").GetInt32());
        Assert.Equal("deferred", ReadSummary(result.Output).GetProperty("extra_sweeps").GetString());
    }
}
