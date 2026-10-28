using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ResumedRemovalProtectsPredecessorsThroughFullOrphanSweep(bool interruptAfterReplacement)
    {
        using var fixture = new CleanLanesFixture();
        const string branch = "harness/resumed-recovery";
        const string control = "harness/retirable-control";
        var lane = fixture.AddLandedLane(branch);
        fixture.AddOrphan(control, merged: true);
        var root = TestRepositoryLayout.FindRoot();
        var script = """
            import argparse, json, sys
            from pathlib import Path
            from unittest.mock import patch
            sys.path.insert(0, sys.argv[1])
            import worktree_preservation as p
            from worktree_protocol import git, value
            source, target = map(Path, sys.argv[2:4])
            metadata = Path(value(target, 'rev-parse', '--absolute-git-dir'))
            original = value(target, 'rev-parse', 'HEAD')
            p.record_removal(metadata, original, value(target, 'symbolic-ref', 'HEAD'))
            git(target, 'commit', '--allow-empty', '-m', 'next snapshot')
            (metadata / 'index.lock').write_text('reconvergence lock\n')
            options = argparse.Namespace(source=source, names='', path=[target], expected=[], preview=False, force=False)
            native_git = p.git
            def interrupt(path, *args, **kwargs):
                if args[:2] == ('worktree', 'remove'):
                    raise OSError('native deletion interrupted')
                return native_git(path, *args, **kwargs)
            if sys.argv[4] == 'True':
                with patch.object(p, 'git', side_effect=interrupt):
                    result = p.remove(options)['items'][0]
                assert result['outcome'] == 'partial_or_indeterminate', result
                record = json.loads((metadata / p.REMOVAL_RECORD).read_text())
                assert record['commit'] != original and record['predecessors'], record
                print(json.dumps(record['predecessors']))
            """;
        var prepared = TestProcessRunner.Run("python3", ["-B", "-c", script,
                Path.Combine(root, "tools/scripts/worktree"), fixture.RepositoryRoot, lane,
                interruptAfterReplacement.ToString()], root, TimeSpan.FromSeconds(60), 1024 * 1024);
        Assert.True(prepared.ExitCode == 0, Encoding.UTF8.GetString(prepared.StandardError));
        CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "merge", "--no-edit", branch);
        var result = fixture.Run("--force");
        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane), result.Output);
        Assert.False(fixture.BranchExists(control), result.Output);
        if (interruptAfterReplacement)
        {
            using var roots = JsonDocument.Parse(prepared.StandardOutput);
            foreach (var predecessor in roots.RootElement.EnumerateArray())
            {
                var reference = predecessor.GetProperty("recovery_branch").GetString()!;
                Assert.Equal(predecessor.GetProperty("commit").GetString(),
                    CleanLanesFixture.Git(fixture.RepositoryWorkingDirectory, "rev-parse", reference).Trim());
            }
        }
        else
        {
            var receipt = Assert.Single(ReadItems(result.Output), item => item.GetProperty("path").GetString() == lane);
            var clearance = Assert.Single(receipt.GetProperty("native_locks").EnumerateArray());
            Assert.Equal("native_lock_cleared", clearance.GetProperty("status").GetString());
            Assert.EndsWith("index.lock", clearance.GetProperty("path").GetString());
            Assert.Equal("reconvergence lock\n".Length, clearance.GetProperty("size").GetInt32());
            Assert.True(clearance.GetProperty("age_seconds").GetDouble() >= 0);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NativeClearanceReceiptSurvivesFailedCheckpointRetry(bool nativeRemovalFailure)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/failed-lock-retry", dirty: true);
        var hooks = Path.Combine(fixture.RepositoryRoot, ".git", "rejecting-hooks");
        Directory.CreateDirectory(hooks);
        var hook = Path.Combine(hooks, "pre-commit");
        File.WriteAllText(hook, "#!/bin/sh\nexit 1\n");
        if (!OperatingSystem.IsWindows()) File.SetUnixFileMode(hook, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        if (!nativeRemovalFailure) CleanLanesFixture.Git(lane, "config", "core.hooksPath", hooks);
        var path = Path.Combine(fixture.WorktreeGitDirectory(lane), "index.lock");
        File.WriteAllText(path, "cleared before failure\n");
        var production = new ProductionWorktreeProcessRunner();
        var runner = fixture.CreateRunner((file, args, directory) =>
        {
            if (!nativeRemovalFailure || file != "python3" || !IsProtocol(args, "remove")) return null;
            var modified = args.ToArray();
            modified[2] = modified[2].Replace("sys.exit(sys.modules['worktree_protocol'].main())", """
                p = sys.modules['worktree_preservation']
                native_git = p.git
                def interrupt(path, *args, **kwargs):
                    if args[:2] == ('worktree', 'remove'):
                        raise OSError('native deletion interrupted')
                    return native_git(path, *args, **kwargs)
                p.git = interrupt
                sys.exit(sys.modules['worktree_protocol'].main())
                """, StringComparison.Ordinal);
            return production.Run(file, modified, directory, TimeSpan.FromSeconds(60));
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        Assert.False(result.Success);
        Assert.True(Directory.Exists(lane));
        Assert.False(File.Exists(path));
        var receipt = Assert.Single(ReadItems(result.Output), item => item.GetProperty("path").GetString() == lane);
        var clearance = Assert.Single(receipt.GetProperty("native_locks").EnumerateArray());
        Assert.Equal("native_lock_cleared", clearance.GetProperty("status").GetString());
        Assert.Equal(path, clearance.GetProperty("path").GetString());
        Assert.Equal("cleared before failure\n".Length, clearance.GetProperty("size").GetInt32());
        Assert.True(clearance.GetProperty("age_seconds").GetDouble() >= 0);
    }

    [Theory]
    [InlineData("dirty")]
    [InlineData("staged")]
    [InlineData("index.lock")]
    [InlineData("held-index.lock")]
    [InlineData("MERGE_HEAD")]
    [InlineData("private")]
    public void ElapsedLockCheckpointsOrdinaryChangesAndReportsNativeFailures(string material)
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/disposable-lock");
        fixture.LockLane(lane);
        if (material is "dirty" or "staged")
        {
            File.WriteAllText(Path.Combine(lane, "README.md"), "unpublished bytes\n");
            if (material == "staged") CleanLanesFixture.Git(lane, "add", "README.md");
        }
        else File.WriteAllText(Path.Combine(fixture.WorktreeGitDirectory(lane),
            material == "held-index.lock" ? "index.lock" : material), "local recovery\n");
        using var holder = material == "held-index.lock"
            ? File.Open(Path.Combine(fixture.WorktreeGitDirectory(lane), "index.lock"),
                FileMode.Open, FileAccess.ReadWrite, FileShare.ReadWrite) : null;
        var runner = fixture.CreateRunner((file, args, _) =>
        {
            if (args.Contains("active-paths")) throw new InvalidOperationException("activity inspection must not run");
            return null;
        });
        var result = fixture.RunWithRaw(runner, "--force", "--lanes-only");
        var failed = material is "MERGE_HEAD" or "held-index.lock";
        Assert.True(result.Success == !failed, result.Output + result.Error);
        Assert.Equal(failed, Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/disposable-lock"));
        if (failed) Assert.StartsWith("checkpoint_failed:", ReasonFor(result.Output, lane));
        if (material is "index.lock" or "held-index.lock")
        {
            var receipt = Assert.Single(ReadItems(result.Output), item => item.GetProperty("path").GetString() == lane);
            var clearance = Assert.Single(receipt.GetProperty("native_locks").EnumerateArray());
            Assert.EndsWith("index.lock", clearance.GetProperty("path").GetString());
            Assert.True(clearance.GetProperty("size").GetInt64() > 0);
            Assert.True(clearance.GetProperty("age_seconds").GetDouble() >= 0);
            Assert.Equal(material == "held-index.lock" ? "held" : "native_lock_cleared",
                clearance.GetProperty("status").GetString());
        }
    }

    [Fact]
    public void SuppliedActivityCannotVetoAnElapsedLock()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddLandedLane("harness/disposable-active");
        fixture.LockLane(lane);
        var result = fixture.RunWithActivePath(lane, "--force", "--lanes-only");
        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/disposable-active"));
    }
}
